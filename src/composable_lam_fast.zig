const std = @import("std");
const base = @import("base.zig");

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

/// High-performance, dynamically-appendable, type-safe composable lambda pipeline.
/// Key properties:
/// - Dynamic append (runtime): appendLam builds a pipeline of frames (no nested recursion).
/// - Static strong typing for intermediate values: each stage is compiled for its exact types.
/// - No boxing of intermediate values: uses ping-pong scratch buffers (raw bytes), typed by each stage.
/// - Deterministic alignment via cfg.scratch_align_cap (comptime). Each append checks align requirements.
/// - Lambda environment storage uses LamBox with SBO (small-buffer optimization).
///

// The max size of a stack-allocated parameter buffer.
const STACK_PARAMS_MAX_SIZE: usize = 64;

/// Maximum alignment that params buffer will guarantee.
/// Typical desktop: 16. Typical MCU: 4 or 8 (8 is safer if u64/f64 appear).
const PARAMS_MAX_ALIGN: Alignment = Alignment.fromByteUnits(16);
const PARAMS_MAX_ALIGN_BYTES: usize = Alignment.toByteUnits(PARAMS_MAX_ALIGN);

// LamBox SBO capacity (bytes). Small lambdas with size <= this and align <= lam_sbo_align are stored inline.
const SBO_SIZE: usize = 32;

// LamBox SBO alignment. Must be >= max alignment of lambdas you want to store inline.
const SBO_ALIGN: Alignment = Alignment.fromByteUnits(16);

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

    return struct {
        composed: *Composed,

        const Self = @This();
        const Allocator = std.mem.Allocator;
        const ArrayList = std.ArrayListUnmanaged;

        const StorageTag = enum { sbo, heap };

        const LamBox = struct {
            ref_count: usize,
            tag: StorageTag,
            storage: union(StorageTag) {
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
            box: *LamBox,

            apply: *const fn (*anyopaque, [*]u8, [*]u8) anyerror!void,
            in_size: usize,
            out_size: usize,
            in_align: u29,
            out_align: u29,
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
                for (self.frames.items) |fr| fr.box.unref_fn(fr.box);
                self.frames.deinit(cfg.allocator);
                cfg.allocator.destroy(self);
            }

            fn clone(self: *Composed) Allocator.Error!*Composed {
                const composed_new = try Composed.init();
                errdefer composed_new.unref();

                composed_new.max_size = self.max_size;
                try composed_new.frames.ensureTotalCapacity(cfg.allocator, self.frames.items.len);
                for (self.frames.items) |frame| {
                    frame.box.ref_fn(frame.box);
                    composed_new.frames.appendAssumeCapacity(frame);
                }
                return composed_new;
            }

            fn ensureUniqueForAppend(self: *Composed) Allocator.Error!*Composed {
                if (self.ref_count == 1) return self;
                return self.clone();
            }

            fn updateScratchNeed(self: *Composed, in_size: usize, out_size: usize) void {
                self.max_size = @max(self.max_size, @max(in_size, out_size));
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

        fn newLamBox(lam_val: anytype) Allocator.Error!*LamBox {
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

        fn makeApply(
            comptime MapLam: type,
        ) *const fn (*anyopaque, [*]u8, [*]u8) anyerror!void {
            const InType = MapLamInType(MapLam);
            const ret_has_err, const RetType = comptime isErrorUnionOrVal(MapLamRetType(MapLam));
            comptime {
                // alignment cap check (compile-time)
                assertAlignCapOk(InType, RetType);
            }

            return struct {
                fn apply(env: *anyopaque, in_buf: [*]u8, out_buf: [*]u8) anyerror!void {
                    const in_ptr: *InType = @ptrCast(@alignCast(in_buf));
                    const x: InType = in_ptr.*;

                    const out_ptr: *RetType = @ptrCast(@alignCast(out_buf));
                    out_ptr.* = if (ret_has_err)
                        try lamCall(MapLam, env, x)
                    else
                        lamCall(MapLam, env, x);
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
                assertAlignCapOk(A, B);
            }

            const composed = try Composed.init();
            errdefer composed.unref();

            const box = try newLamBox(init_lam);
            errdefer box.unref_fn(box);

            const apply_fn = makeApply(InitLam);

            const frame: Frame = .{
                .box = box,
                .apply = apply_fn,
                .in_size = @sizeOf(A),
                .out_size = @sizeOf(B),
                .in_align = @alignOf(A),
                .out_align = @alignOf(B),
            };

            try composed.frames.append(cfg.allocator, frame);
            composed.updateScratchNeed(frame.in_size, frame.out_size);

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

            // Create new Composed for the new pipeline type (cfg, A, RetType), then copy existing frames into it
            const old_composed = self.composed;
            const ComposedLam = ComposableLamFast(cfg, A, RetType);
            const new_composed = try createEmptyComposedFor(RetType);
            errdefer new_composed.unref();

            new_composed.max_size = old_composed.max_size;
            try new_composed.frames.ensureTotalCapacity(cfg.allocator, old_composed.frames.items.len + 1);
            for (old_composed.frames.items) |fr| {
                fr.box.ref_fn(fr.box);
                // LamBox layout is identical across (cfg, A, _) instantiations; safe to reinterpret.
                const new_frame: ComposedLam.Frame = .{
                    .box = @ptrCast(fr.box),
                    .apply = fr.apply,
                    .in_size = fr.in_size,
                    .out_size = fr.out_size,
                    .in_align = fr.in_align,
                    .out_align = fr.out_align,
                };
                new_composed.frames.appendAssumeCapacity(new_frame);
            }

            const box = try newLamBox(map_lam);
            errdefer box.unref_fn(box);

            // compile-time alignment cap check is inside makeApply via assertAlignCapOk(B, RetType)
            const apply_fn = makeApply(MapLam);

            const frame: ComposedLam.Frame = .{
                .box = @ptrCast(box),
                .apply = apply_fn,
                .in_size = @sizeOf(B),
                .out_size = @sizeOf(RetType),
                .in_align = @alignOf(B),
                .out_align = @alignOf(RetType),
            };

            new_composed.frames.appendAssumeCapacity(frame);
            new_composed.updateScratchNeed(frame.in_size, frame.out_size);

            const composed_lam = try cfg.allocator.create(ComposedLam);
            composed_lam.* = .{ .composed = new_composed };

            // When ref_count > 1, another owner holds this pipeline (e.g. via strongRef()); do not destroy self to avoid double-free.
            const was_sole_owner = (old_composed.ref_count == 1);
            old_composed.unref();
            if (was_sole_owner) {
                cfg.allocator.destroy(self);
            }
            return composed_lam;
        }

        /// Single-loop interpreter execution using ping-pong scratch buffers.
        pub fn call(self: *const Self, a: A) B {
            const composed = self.composed;

            const stride = std.mem.alignForward(usize, composed.max_size, PARAMS_MAX_ALIGN_BYTES);
            const total = 2 * stride;

            // Stack fast path (cap is compile-time).
            const use_stack = (total <= STACK_PARAMS_MAX_SIZE);

            var stack_buf: [STACK_PARAMS_MAX_SIZE]u8 align(PARAMS_MAX_ALIGN_BYTES) = undefined;
            var scratch: []u8 = undefined;

            if (use_stack) {
                scratch = stack_buf[0..total];
            } else {
                // deterministic alignment: allocate with PARAMS_MAX_ALIGN; free with same alignment
                scratch = cfg.allocator.alignedAlloc(u8, PARAMS_MAX_ALIGN, total) catch unreachable;
            }
            defer {
                if (!use_stack) {
                    cfg.allocator.rawFree(scratch, PARAMS_MAX_ALIGN, @returnAddress());
                }
            }

            var in_buf = scratch[0..stride];
            const out_buf = scratch[stride..total];

            // write initial input A
            const a_ptr: *A = @ptrCast(@alignCast(in_buf.ptr));
            a_ptr.* = a;

            // run frames in order (stride is >= every frame's in_size/out_size by updateScratchNeed invariant)
            for (composed.frames.items) |frame| {
                std.debug.assert(stride >= frame.in_size and stride >= frame.out_size);
                const env = frame.box.envPtr();
                frame.apply(env, in_buf.ptr, out_buf.ptr) catch |e| {
                    if (has_err_final) {
                        return @errorCast(e);
                    } else {
                        unreachable;
                    }
                };
                in_buf = out_buf;
            }

            // When B is error!T, buffer only ever holds payload T (errors propagated via try); read as payload.
            if (has_err_final) {
                const p_ptr: *_B_payload = @ptrCast(@alignCast(in_buf.ptr));
                return p_ptr.*;
            } else {
                const b_ptr: *B = @ptrCast(@alignCast(in_buf.ptr));
                return b_ptr.*;
            }
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
