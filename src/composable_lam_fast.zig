const std = @import("std");
const base = @import("base.zig");
const builtin = @import("builtin");

const Alignment = std.mem.Alignment;
const mapFnToLam = base.mapFnToLam;
const MapFnToLamType = base.MapFnToLamType;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const isErrorUnionOrVal = base.isErrorUnionOrVal;
const copyOrCloneOrRef = base.copyOrCloneOrRef;
const deinitOrUnref = base.deinitOrUnref;

const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

/// Configuration for ComposableLamFast. Use getDefaultComposableLamCfg(allocator) for defaults.
pub const ComposableLamCfg = struct {
    allocator: Allocator,
    errors: ?type,

    /// Max bytes for stack-allocated params buffer; larger pipelines use heap. Default from defaultStackParamsMaxSize().
    stack_params_max_size: usize = defaultStackParamsMaxSize(),

    /// Max alignment guaranteed for params buffer. Typical desktop: 16. MCU: 4 or 8.
    params_max_align: Alignment = Alignment.fromByteUnits(16),

    /// LamBox SBO capacity (bytes). Lambdas with size <= this and align <= sbo_align are stored inline.
    sbo_size: usize = 32,

    /// LamBox SBO alignment. Must be >= max alignment of lambdas stored inline.
    sbo_align: Alignment = Alignment.fromByteUnits(16),

    /// When true, Frame includes trace_in_size/out_size/align for observability.
    trace_inout_params: bool = false,
};

/// Returns default ComposableLamCfg. stack_params_max_size uses defaultStackParamsMaxSize().
pub fn getDefaultComposableLamCfg(allocator: Allocator) ComposableLamCfg {
    return .{
        .allocator = allocator,
        .errors = Allocator.Error,
        .stack_params_max_size = defaultStackParamsMaxSize(),
        .params_max_align = Alignment.fromByteUnits(16),
        .sbo_size = 32,
        .sbo_align = Alignment.fromByteUnits(16),
        .trace_inout_params = false,
    };
}

/// High-performance, dynamically-appendable, type-safe composable lambda pipeline.
/// Key properties:
/// - Dynamic append (runtime): appendLam builds a pipeline of frames (no nested recursion).
/// - Static strong typing for intermediate values: each stage is compiled for its exact types.
/// - No boxing of intermediate values: uses single scratch buffer (raw bytes), typed by each stage.
/// - Deterministic alignment via cfg.scratch_align_cap (comptime). Each append checks align requirements.
/// - Lambda environment storage uses LamBox with SBO (small-buffer optimization).
///
pub fn defaultStackParamsMaxSize() usize {
    // Keep conservative defaults on constrained targets.
    if (builtin.target.os.tag == .freestanding or builtin.target.os.tag == .uefi) return 64;
    if (builtin.target.ptrBitWidth() <= 32) return 128;
    return 256;
}

fn getCallFnType(comptime Lam: type) type {
    const info = @typeInfo(Lam);
    return switch (info) {
        .@"fn" => Lam,
        .pointer => |p| switch (@typeInfo(p.child)) {
            .@"fn" => p.child, // *const fn(...) ...
            .@"struct" => blk: {
                if (!@hasDecl(p.child, "call")) @compileError("Lambda pointer type must point to a struct with `pub fn call(...)`.");
                const call_decl = @TypeOf(@field(p.child, "call"));
                if (@typeInfo(call_decl) != .@"fn") @compileError("`call` must be a function.");
                break :blk call_decl;
            },
            else => @compileError("Unsupported lambda pointer type."),
        },
        .@"struct" => blk: {
            if (!@hasDecl(Lam, "call")) @compileError("Lambda struct type must define `pub fn call(...)`.");
            const call_decl = @TypeOf(@field(Lam, "call"));
            if (@typeInfo(call_decl) != .@"fn") @compileError("`call` must be a function.");
            break :blk call_decl;
        },
        else => @compileError("Unsupported lambda type. Use a function or a struct with `call`."),
    };
}

/// A LamBox stores a lambda env (value) with reference counting and SBO.
/// It supports both:
/// - Lam = struct lambda value (with call method)
/// - Lam = function type / pointer-to-function (stored as value)
///
/// Note: For Lam = pointer-to-struct lambda, this LamBox stores the pointer value,
/// not the pointed object. Lifetime management for the pointed object is user's responsibility
/// unless they provide custom ref/deinit in the lambda type itself.
pub fn ComposableLamFast(
    comptime cfg: anytype,
    comptime A: type,
    comptime B: type,
) type {
    const has_err_final, const _B_payload = comptime isErrorUnionOrVal(B);
    const ErrSet = if (has_err_final) @typeInfo(B).error_union.error_set else error{};
    const TRACE_INOUT_PARAMS: bool = comptime if (@hasField(@TypeOf(cfg), "trace_inout_params"))
        cfg.trace_inout_params
    else
        false;
    // Configurable params buffer alignment; default keeps previous behavior.
    const PARAMS_MAX_ALIGN: Alignment = comptime if (@hasField(@TypeOf(cfg), "params_max_align"))
        cfg.params_max_align
    else
        Alignment.fromByteUnits(16);
    const PARAMS_MAX_ALIGN_BYTES: usize = Alignment.toByteUnits(PARAMS_MAX_ALIGN);
    // Configurable LamBox SBO size/alignment; defaults keep previous behavior.
    const SBO_SIZE: usize = comptime if (@hasField(@TypeOf(cfg), "sbo_size"))
        cfg.sbo_size
    else
        32;
    const SBO_ALIGN: Alignment = comptime if (@hasField(@TypeOf(cfg), "sbo_align"))
        cfg.sbo_align
    else
        Alignment.fromByteUnits(16);

    // The max size of a stack-allocated parameter buffer.
    const STACK_PARAMS_MAX_SIZE: usize = comptime if (@hasField(@TypeOf(cfg), "stack_params_max_size"))
        cfg.stack_params_max_size
    else
        defaultStackParamsMaxSize();

    return struct {
        composed: *Composed,

        const Self = @This();

        const StorageTag = enum { sbo, heap };

        const LamBox = struct {
            ref_count: usize,
            tag: StorageTag,
            storage: union {
                sbo: [SBO_SIZE]u8 align(Alignment.toByteUnits(SBO_ALIGN)),
                heap: *anyopaque,
            },
            ref_fn: *const fn (*LamBox) void,
            unref_fn: *const fn (*LamBox) void,

            fn envPtr(box: *LamBox) *anyopaque {
                return switch (box.tag) {
                    .sbo => @ptrCast(@alignCast(&box.storage.sbo)),
                    .heap => box.storage.heap,
                };
            }
        };

        const Frame = struct {
            box: ?*LamBox,

            // In-place apply: reads input value from `buf` as InType, writes output value to same `buf` as OutType.
            // `env` is null for stateless lambdas.
            apply: *const fn (?*anyopaque, [*]u8) ErrSet!void,

            // Runtime scheduling uses merged in/out requirements for the in-place buffer.
            inout_size: usize,
            inout_align: u29,

            // Optional observability fields (compiled in only when TRACE_INOUT_PARAMS=true).
            trace_in_size: if (TRACE_INOUT_PARAMS) usize else void = if (TRACE_INOUT_PARAMS) 0 else {},
            trace_out_size: if (TRACE_INOUT_PARAMS) usize else void = if (TRACE_INOUT_PARAMS) 0 else {},
            trace_in_align: if (TRACE_INOUT_PARAMS) u29 else void = if (TRACE_INOUT_PARAMS) 0 else {},
            trace_out_align: if (TRACE_INOUT_PARAMS) u29 else void = if (TRACE_INOUT_PARAMS) 0 else {},
        };

        const Composed = struct {
            ref_count: usize,
            frames: ArrayList(Frame),
            max_size: usize,

            fn init() Allocator.Error!*Composed {
                const composed = try cfg.allocator.create(Composed);
                composed.* = .{
                    .ref_count = 1,
                    .frames = .{},
                    .max_size = 0,
                };
                return composed;
            }

            fn ref(self: *Composed) void {
                self.ref_count += 1;
            }

            fn unref(self: *Composed) void {
                if (self.ref_count > 1) {
                    self.ref_count -= 1;
                    return;
                }
                for (self.frames.items) |fr| {
                    if (fr.box) |b| b.unref_fn(b);
                }
                self.frames.deinit(cfg.allocator);
                cfg.allocator.destroy(self);
            }

            fn clone(self: *Composed) Allocator.Error!*Composed {
                const composed_new = try Composed.init();
                errdefer composed_new.unref();

                composed_new.max_size = self.max_size;
                try composed_new.frames.ensureTotalCapacity(cfg.allocator, self.frames.items.len);
                for (self.frames.items) |frame| {
                    if (frame.box) |b| b.ref_fn(b);
                    composed_new.frames.appendAssumeCapacity(frame);
                }
                return composed_new;
            }

            fn ensureUniqueForAppend(self: *Composed) Allocator.Error!*Composed {
                if (self.ref_count == 1) return self;
                return self.clone();
            }

            fn updateScratchNeed(self: *Composed, inout_size: usize) void {
                self.max_size = @max(self.max_size, inout_size);
            }
        };

        /// Create an empty Composed for pipeline output type Out (used when appending to produce a new pipeline type).
        fn createEmptyComposedFor(comptime Out: type) Allocator.Error!*ComposableLamFast(cfg, A, Out).Composed {
            const ComposedOut = ComposableLamFast(cfg, A, Out).Composed;
            const composed = try cfg.allocator.create(ComposedOut);
            composed.* = .{
                .ref_count = 1,
                .frames = .{},
                .max_size = 0,
            };
            return composed;
        }

        fn assertAlignCapOk(comptime InT: type, comptime OutT: type) void {
            comptime {
                const need_in: Alignment = Alignment.fromByteUnits(@alignOf(InT));
                const need_out: Alignment = Alignment.fromByteUnits(@alignOf(OutT));
                const need: Alignment = Alignment.max(need_in, need_out);
                if (Alignment.compare(need, .gt, PARAMS_MAX_ALIGN)) {
                    @compileError(std.fmt.comptimePrint(
                        "ComposableLamFast scratch_align_cap too small: cap={d}, need={d}. In={s} (align {d}), Out={s} (align {d}). " ++
                            "Increase cfg.scratch_align_cap to >= {d}.",
                        .{ Alignment.toByteUnits(PARAMS_MAX_ALIGN), Alignment.toByteUnits(need), @typeName(InT), Alignment.toByteUnits(need_in), @typeName(OutT), Alignment.toByteUnits(need_out), Alignment.toByteUnits(need) },
                    ));
                }
            }
        }

        fn AppendedRetType(comptime PrevOutType: type, comptime Lam: type) type {
            const prev_out_info = @typeInfo(PrevOutType);
            const LamRetType = MapLamRetType(Lam);
            if (prev_out_info != .error_union) return LamRetType;

            const ret_info = @typeInfo(LamRetType);
            const PrevError = prev_out_info.error_union.error_set;
            const OutError, const RetType = if (ret_info == .error_union)
                .{ PrevError || ret_info.error_union.error_set, ret_info.error_union.payload }
            else
                .{ PrevError, LamRetType };

            return OutError!RetType;
        }

        pub fn newLamBox(lam_val: anytype) Allocator.Error!*LamBox {
            const Lam = @TypeOf(lam_val);
            // When Lam is a pointer (e.g. *ComposableLamFast), use pointee type for @hasDecl and correct call target
            const LamDecl = if (@typeInfo(Lam) == .pointer) std.meta.Child(Lam) else Lam;

            const BoxFns = struct {
                fn get(box: *LamBox) *Lam {
                    return switch (box.tag) {
                        .sbo => @ptrCast(@alignCast(&box.storage.sbo)),
                        .heap => @ptrCast(@alignCast(box.storage.heap)),
                    };
                }

                fn ref(box: *LamBox) void {
                    const p = get(box);
                    if (@hasDecl(LamDecl, "refSubLam")) {
                        if (@typeInfo(Lam) == .pointer) (p.*).refSubLam() else p.refSubLam();
                    }
                    box.ref_count += 1;
                }

                fn unref(box: *LamBox) void {
                    const p = get(box);

                    if (box.ref_count > 1) {
                        box.ref_count -= 1;
                        if (@hasDecl(LamDecl, "unrefSubLam")) {
                            if (@typeInfo(Lam) == .pointer) (p.*).unrefSubLam() else p.unrefSubLam();
                        }
                        return;
                    }

                    // last reference
                    deinitOrUnref(p.*);
                    if (box.tag == .heap) {
                        cfg.allocator.destroy(p);
                    }
                    cfg.allocator.destroy(box);
                }
            };

            const box = try cfg.allocator.create(LamBox);
            errdefer cfg.allocator.destroy(box);

            const use_sbo = (@sizeOf(Lam) <= SBO_SIZE) and Alignment.compare(Alignment.fromByteUnits(@alignOf(Lam)), .lte, SBO_ALIGN);
            box.* = .{
                .ref_count = 1,
                .tag = if (use_sbo) .sbo else .heap,
                .storage = undefined,
                .ref_fn = BoxFns.ref,
                .unref_fn = BoxFns.unref,
            };

            if (use_sbo) {
                // Store Lam value inline.
                const p: *Lam = @ptrCast(@alignCast(&box.storage.sbo));
                p.* = try copyOrCloneOrRef(lam_val);
            } else {
                // Heap allocate Lam and store pointer.
                const p = try cfg.allocator.create(Lam);
                errdefer cfg.allocator.destroy(p);
                p.* = try copyOrCloneOrRef(lam_val);
                box.storage = .{ .heap = @ptrCast(p) };
            }
            return box;
        }

        /// Call the stored lambda (function or struct-with-call) in a uniform way.
        fn lamCall(comptime Lam: type, env: *anyopaque, x: anytype) MapLamRetType(Lam) {
            const info = @typeInfo(Lam);
            switch (info) {
                .@"fn" => return (@as(Lam, @ptrCast(env)))(x), // unreachable in our storage (env points to value), but kept for completeness
                .pointer => |p| {
                    if (@typeInfo(p.child) == .@"fn") {
                        // env points to a value of type Lam (pointer-to-fn or pointer-to-fn? Actually Lam itself is pointer type)
                        const p_fp: *Lam = @ptrCast(@alignCast(env));
                        const fp: Lam = p_fp.*;
                        return fp(x);
                    }
                    // pointer to struct lambda is stored as Lam value; call on it
                    const p_lv: *Lam = @ptrCast(@alignCast(env));
                    const lv: Lam = p_lv.*;
                    return lv.call(x);
                },
                .@"struct" => {
                    const l: *Lam = @ptrCast(@alignCast(env));
                    return l.call(x);
                },
                else => @compileError("Unsupported Lam in lamCall."),
            }
        }

        pub fn isStatelessLam(comptime Lam: type) bool {
            return @typeInfo(Lam) == .@"struct" and @sizeOf(Lam) == 0;
        }

        pub fn makeApplyBoxed(
            comptime MapLam: type,
        ) *const fn (?*anyopaque, [*]u8) ErrSet!void {
            const InType = MapLamInType(MapLam);
            const ret_has_err, const RetType = comptime isErrorUnionOrVal(MapLamRetType(MapLam));
            comptime {
                // alignment cap check (compile-time)
                assertAlignCapOk(InType, RetType);
            }

            return struct {
                fn apply(env_opt: ?*anyopaque, buf: [*]u8) ErrSet!void {
                    const env = env_opt.?;

                    const in_ptr: *InType = @ptrCast(@alignCast(buf));
                    const x: InType = in_ptr.*;

                    const out_ptr: *RetType = @ptrCast(@alignCast(buf));
                    out_ptr.* = if (ret_has_err)
                        try lamCall(MapLam, env, x)
                    else
                        lamCall(MapLam, env, x);
                }
            }.apply;
        }

        pub fn makeApplyStateless(
            comptime MapLam: type,
        ) *const fn (?*anyopaque, [*]u8) ErrSet!void {
            comptime {
                if (!isStatelessLam(MapLam)) @compileError("makeApplyStateless requires a zero-sized struct lambda type.");
            }

            const InType = MapLamInType(MapLam);
            const ret_has_err, const RetType = comptime isErrorUnionOrVal(MapLamRetType(MapLam));
            comptime {
                assertAlignCapOk(InType, RetType);
            }

            return struct {
                fn apply(_: ?*anyopaque, buf: [*]u8) ErrSet!void {
                    const in_ptr: *InType = @ptrCast(@alignCast(buf));
                    const x: InType = in_ptr.*;

                    // Zero-sized lambda: no environment needed.
                    var lam: MapLam = .{};

                    const out_ptr: *RetType = @ptrCast(@alignCast(buf));
                    out_ptr.* = if (ret_has_err)
                        try lam.call(x)
                    else
                        lam.call(x);
                }
            }.apply;
        }

        pub fn createByFn(map_fn: anytype) Allocator.Error!*Self {
            return Self.create(mapFnToLam(map_fn));
        }

        pub fn create(init_lam: anytype) Allocator.Error!*Self {
            const InitLam = @TypeOf(init_lam);
            comptime {
                if (A != MapLamInType(InitLam)) @compileError("create: input type mismatch.");
                if (B != MapLamRetType(InitLam)) @compileError("create: return type mismatch.");
                // Buffer stores payload only.
                assertAlignCapOk(A, _B_payload);
            }

            const composed = try Composed.init();
            errdefer composed.unref();

            var box_opt: ?*LamBox = null;
            errdefer {
                if (box_opt) |box| box.unref_fn(box);
            }

            const apply_fn = if (comptime isStatelessLam(InitLam))
                makeApplyStateless(InitLam)
            else blk: {
                box_opt = try newLamBox(init_lam);
                break :blk makeApplyBoxed(InitLam);
            };

            const frame: Frame = .{
                .box = box_opt,
                .apply = apply_fn,
                .inout_size = @max(@sizeOf(A), @sizeOf(_B_payload)),
                .inout_align = @max(@alignOf(A), @alignOf(_B_payload)),
                .trace_in_size = if (TRACE_INOUT_PARAMS) @sizeOf(A) else {},
                .trace_out_size = if (TRACE_INOUT_PARAMS) @sizeOf(_B_payload) else {},
                .trace_in_align = if (TRACE_INOUT_PARAMS) @alignOf(A) else {},
                .trace_out_align = if (TRACE_INOUT_PARAMS) @alignOf(_B_payload) else {},
            };

            try composed.frames.append(cfg.allocator, frame);
            composed.updateScratchNeed(frame.inout_size);

            // ownership transferred into composed
            box_opt = null;

            const self = try cfg.allocator.create(Self);
            self.* = .{ .composed = composed };
            return self;
        }

        pub fn strongRef(self: *Self) *Self {
            self.composed.ref();
            return self;
        }

        /// Ref sub-structure (composed chain); same semantics as base.ComposableLamNormal AppendedCompLam.refSubLam.
        pub fn refSubLam(self: *const Self) void {
            self.composed.ref();
        }

        /// Unref sub-structure (composed chain); same semantics as base.ComposableLamNormal AppendedCompLam.unrefSubLam.
        pub fn unrefSubLam(self: Self) void {
            self.composed.unref();
        }

        /// Release composed; same semantics as base.ComposableLamNormal AppendedCompLam.deinit.
        pub fn deinit(self: Self) void {
            self.composed.unref();
        }

        pub fn strongUnref(self: *Self) bool {
            const c = self.composed;
            const last = (c.ref_count == 1);
            c.unref();
            if (last) {
                cfg.allocator.destroy(self);
                return true;
            }
            return false;
        }

        pub fn appendFn(self: *Self, map_fn: anytype) Allocator.Error!*ComposableLamFast(cfg, A, AppendedRetType(B, MapFnToLamType(@TypeOf(map_fn)))) {
            return self.appendLam(mapFnToLam(map_fn));
        }

        pub fn appendLam(self: *Self, map_lam: anytype) Allocator.Error!*ComposableLamFast(cfg, A, AppendedRetType(B, @TypeOf(map_lam))) {
            const MapLam = @TypeOf(map_lam);
            const InType = MapLamInType(MapLam);
            comptime {
                if (_B_payload != InType) {
                    @compileError(std.fmt.comptimePrint(
                        "appendLam: input type mismatch. Expected {s}, got {s}.",
                        .{ @typeName(_B_payload), @typeName(InType) },
                    ));
                }
            }

            const RetType = AppendedRetType(B, MapLam);
            const ret_has_err, const RetPayload = comptime isErrorUnionOrVal(RetType);
            _ = ret_has_err;

            // New specialization for the extended pipeline.
            const ComposedLam = ComposableLamFast(cfg, A, RetType);

            const old_composed = self.composed;

            // Fast path: sole owner -> mutate in place (no frame copy) and re-type the composed pointer.
            if (old_composed.ref_count == 1) {
                const new_composed: *ComposedLam.Composed = @ptrCast(old_composed);

                var box_opt: ?*ComposedLam.LamBox = null;
                errdefer {
                    if (box_opt) |box| box.unref_fn(box);
                }

                const apply_fn = if (comptime ComposedLam.isStatelessLam(MapLam))
                    ComposedLam.makeApplyStateless(MapLam)
                else blk: {
                    box_opt = try ComposedLam.newLamBox(map_lam);
                    break :blk ComposedLam.makeApplyBoxed(MapLam);
                };

                const frame: ComposedLam.Frame = .{
                    .box = box_opt,
                    .apply = apply_fn,
                    .inout_size = @max(@sizeOf(_B_payload), @sizeOf(RetPayload)),
                    .inout_align = @max(@alignOf(_B_payload), @alignOf(RetPayload)),
                    .trace_in_size = if (TRACE_INOUT_PARAMS) @sizeOf(_B_payload) else {},
                    .trace_out_size = if (TRACE_INOUT_PARAMS) @sizeOf(RetPayload) else {},
                    .trace_in_align = if (TRACE_INOUT_PARAMS) @alignOf(_B_payload) else {},
                    .trace_out_align = if (TRACE_INOUT_PARAMS) @alignOf(RetPayload) else {},
                };

                try new_composed.frames.append(cfg.allocator, frame);
                new_composed.updateScratchNeed(frame.inout_size);

                const composed_lam = try cfg.allocator.create(ComposedLam);
                composed_lam.* = .{ .composed = new_composed };

                // safe to destroy handle because it is not shared (ref_count==1)
                cfg.allocator.destroy(self);
                return composed_lam;
            }

            // Shared path: copy existing frames into a fresh composed, then append.
            const new_composed = try createEmptyComposedFor(RetType);
            errdefer new_composed.unref();

            new_composed.max_size = old_composed.max_size;
            try new_composed.frames.ensureTotalCapacity(cfg.allocator, old_composed.frames.items.len + 1);

            for (old_composed.frames.items) |frame| {
                var new_box_opt: ?*ComposedLam.LamBox = null;
                if (frame.box) |box| {
                    box.ref_fn(box);
                    new_box_opt = @ptrCast(box);
                }

                const new_frame: ComposedLam.Frame = .{
                    .box = new_box_opt,
                    // Cast is ABI-safe: error sets are subsets; function pointers are just code addresses.
                    .apply = @ptrCast(frame.apply),
                    .inout_size = frame.inout_size,
                    .inout_align = frame.inout_align,
                    .trace_in_size = frame.trace_in_size,
                    .trace_out_size = frame.trace_out_size,
                    .trace_in_align = frame.trace_in_align,
                    .trace_out_align = frame.trace_out_align,
                };
                new_composed.frames.appendAssumeCapacity(new_frame);
            }

            var box_opt: ?*ComposedLam.LamBox = null;
            errdefer {
                if (box_opt) |box| box.unref_fn(box);
            }

            const apply_fn = if (comptime ComposedLam.isStatelessLam(MapLam))
                ComposedLam.makeApplyStateless(MapLam)
            else blk2: {
                box_opt = try ComposedLam.newLamBox(map_lam);
                break :blk2 ComposedLam.makeApplyBoxed(MapLam);
            };

            const frame: ComposedLam.Frame = .{
                .box = box_opt,
                .apply = apply_fn,
                .inout_size = @max(@sizeOf(_B_payload), @sizeOf(RetPayload)),
                .inout_align = @max(@alignOf(_B_payload), @alignOf(RetPayload)),
                .trace_in_size = if (TRACE_INOUT_PARAMS) @sizeOf(_B_payload) else {},
                .trace_out_size = if (TRACE_INOUT_PARAMS) @sizeOf(RetPayload) else {},
                .trace_in_align = if (TRACE_INOUT_PARAMS) @alignOf(_B_payload) else {},
                .trace_out_align = if (TRACE_INOUT_PARAMS) @alignOf(RetPayload) else {},
            };

            new_composed.frames.appendAssumeCapacity(frame);
            new_composed.updateScratchNeed(frame.inout_size);

            // ownership transferred into composed
            box_opt = null;

            const composed_lam = try cfg.allocator.create(ComposedLam);
            composed_lam.* = .{ .composed = new_composed };

            // Release exactly one owner share from the old composed (other owners keep using the existing handle).
            old_composed.unref();
            return composed_lam;
        }

        /// Single-loop interpreter execution using ping-pong scratch buffers.
        pub fn call(self: *const Self, a: A) B {
            const composed = self.composed;

            const stride = std.mem.alignForward(usize, composed.max_size, PARAMS_MAX_ALIGN_BYTES);

            // Stack fast path (cap is compile-time).
            const use_stack = (stride <= STACK_PARAMS_MAX_SIZE);

            var stack_buf: [STACK_PARAMS_MAX_SIZE]u8 align(PARAMS_MAX_ALIGN_BYTES) = undefined;
            var scratch: []u8 = undefined;

            if (use_stack) {
                scratch = stack_buf[0..stride];
            } else {
                // deterministic alignment: allocate with PARAMS_MAX_ALIGN; free with same alignment
                scratch = cfg.allocator.alignedAlloc(u8, PARAMS_MAX_ALIGN, stride) catch unreachable;
            }
            defer {
                if (!use_stack) {
                    cfg.allocator.rawFree(scratch, PARAMS_MAX_ALIGN, @returnAddress());
                }
            }

            // write initial input A
            const a_ptr: *A = @ptrCast(@alignCast(scratch.ptr));
            a_ptr.* = a;

            // run frames in order (composed.max_size invariant ensures stride is sufficient)
            if (has_err_final) {
                for (composed.frames.items) |frame| {
                    std.debug.assert(stride >= frame.inout_size);
                    const env_opt: ?*anyopaque = if (frame.box) |b| b.envPtr() else null;
                    try frame.apply(env_opt, scratch.ptr);
                }
            } else {
                for (composed.frames.items) |frame| {
                    std.debug.assert(stride >= frame.inout_size);
                    const env_opt: ?*anyopaque = if (frame.box) |b| b.envPtr() else null;
                    frame.apply(env_opt, scratch.ptr) catch unreachable;
                }
            }

            // Buffer holds payload only; for non-error unions payload == B.
            const p_ptr: *_B_payload = @ptrCast(@alignCast(scratch.ptr));
            return p_ptr.*;
        }
    };
}

// -------------------- Optional micro-benchmark --------------------
// This benchmark compares:
// - base.ComposableLam (recursive chain)
// - ComposableLamFast (single-loop frames)
// It assumes `base.zig` exists in the same directory.

const bench = struct {
    const Add1Lam = struct {
        pub fn call(_: *const @This(), x: u64) u64 {
            return x + 1;
        }
    };

    const LargeAdd1Lam = struct {
        local_buf: [128]u64 align(16) = undefined,

        pub fn call(_: *const @This(), x: u64) u64 {
            return x + 1000;
        }
    };

    fn runOnce(comptime N: usize, comptime allocator: std.mem.Allocator) !void {
        var stdout_buf: [512]u8 = undefined;
        var stdout_writer = std.fs.File.stdout().writer(&stdout_buf);
        const stdout = &stdout_writer.interface;

        const cfg = base.getDefaultBaseCfg(allocator);

        const lam = Add1Lam{};
        // const lam = LargeAdd1Lam{};

        var old = try base.ComposableLam(cfg, u64, u64).create(lam);
        // move semantics in base: old pointer replaced each append
        var i: usize = 1;
        while (i < N) : (i += 1) {
            old = try old.appendLam(lam);
        }

        var fast = try ComposableLamFast(cfg, u64, u64).create(lam);
        i = 1;
        while (i < N) : (i += 1) {
            fast = try fast.appendLam(lam);
        }

        // Warm-up
        _ = old.call(1);
        _ = fast.call(1);

        const iters: usize = 2_000_000;
        var sum_old: u64 = 0;
        var sum_fast: u64 = 0;

        var t = try std.time.Timer.start();
        i = 0;
        while (i < iters) : (i += 1) {
            const r = old.call(@intCast(i));
            sum_old +%= r;
        }
        const ns_old = t.read();

        t.reset();
        i = 0;
        while (i < iters) : (i += 1) {
            const r = fast.call(@intCast(i));
            sum_fast +%= r;
        }
        const ns_fast = t.read();

        // prevent optimization
        std.mem.doNotOptimizeAway(sum_old);
        std.mem.doNotOptimizeAway(sum_fast);

        const ns_per_old = @as(f64, @floatFromInt(ns_old)) / @as(f64, @floatFromInt(iters));
        const ns_per_fast = @as(f64, @floatFromInt(ns_fast)) / @as(f64, @floatFromInt(iters));
        const speedup = ns_per_old / ns_per_fast;

        try stdout.print(
            "N={d:4}  old: {d:8.3} ns/op   fast: {d:8.3} ns/op   speedup: {d:5.2}x\n",
            .{ N, ns_per_old, ns_per_fast, speedup },
        );
        try stdout.flush();

        _ = old.strongUnref();
        _ = fast.strongUnref();
    }
};

pub fn benchMain() !void {
    // var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    // defer _ = gpa.deinit();
    // const allocator = gpa.allocator();
    const allocator = std.heap.page_allocator;

    const Ns = [_]usize{ 8, 16, 24, 32, 64, 128, 512, 1024 };
    inline for (Ns) |N| {
        try bench.runOnce(N, allocator);
    }
}

pub fn main() !void {
    return benchMain();
}
