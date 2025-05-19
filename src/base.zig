//! All base types and functions for zig-cats
const std = @import("std");
const testing = std.testing;
const testu = @import("test_utils.zig");

const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

// pub usingnamespace @import("base_types.zig");

pub fn ConstraitType(comptime T: type) type {
    if (@hasDecl(T, "is_constraint") and T.is_constraint) {
        @compileError(std.fmt.comptimePrint("Type {any} is not a constrait!", .{@typeName(T)}));
    }
    return T;
}

pub fn TypeWithConstraits(comptime T: type, constraits: anytype) type {
    const Constraits = @TypeOf(constraits);
    const constraits_info = @typeInfo(Constraits);
    if (constraits_info != .@"struct") {
        @compileError("expected tuple or struct argument for constraits, found " ++ @typeName(Constraits));
    }

    const fields_info = constraits_info.@"struct".fields;
    if (constraits_info.@"struct".is_tuple) {
        inline for (0..fields_info.len) |i| {
            _ = ConstraitType(constraits[i]);
        }
    } else {
        inline for (fields_info) |field| {
            _ = ConstraitType(@field(constraits, field.name));
        }
    }

    return T;
}

pub fn isPureTypeClass(comptime Impl: type) bool {
    return Impl.Error == null;
}

/// A single-argument type function for type constructor
pub const TCtor = *const fn (comptime type) type;

pub fn GetPointerChild(comptime P: type) type {
    if (@typeInfo(P) != .pointer) {
        @compileError("The type P must be a Pointer type!");
    }
    return std.meta.Child(P);
}

pub fn MapFnInType(comptime MapFn: type) type {
    const _MapFn = if (@typeInfo(MapFn) == .pointer) std.meta.Child(MapFn) else MapFn;
    const info = @typeInfo(_MapFn);
    const len = info.@"fn".params.len;

    if (len != 1) {
        @compileError("The map function must has only one parameter!");
    }

    return info.@"fn".params[0].type.?;
}

pub fn MapFnRetType(comptime MapFn: type) type {
    const _MapFn = if (@typeInfo(MapFn) == .pointer) std.meta.Child(MapFn) else MapFn;
    const R = @typeInfo(_MapFn).@"fn".return_type.?;

    if (R == noreturn) {
        @compileError("The return type of map function must not be noreturn!");
    }
    return R;
}

pub fn MapLamInType(comptime MapLam: type) type {
    const _MapLam = if (@typeInfo(MapLam) == .pointer) std.meta.Child(MapLam) else MapLam;
    const info = @typeInfo(_MapLam);
    if (info != .@"struct") {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(_MapLam.call));
    const len = mapFnInfo.@"fn".params.len;

    if (len != 2) {
        @compileError("The call function of map lambda must have only two parameters!");
    }
    if (mapFnInfo.@"fn".params[0].type.? != *_MapLam and mapFnInfo.@"fn".params[0].type.? != *const _MapLam) {
        @compileError("The first parameter of call function must be a pointer of MapLam!");
    }

    return mapFnInfo.@"fn".params[1].type.?;
}

pub fn MapLamRetType(comptime MapLam: type) type {
    const _MapLam = if (@typeInfo(MapLam) == .pointer) std.meta.Child(MapLam) else MapLam;
    const info = @typeInfo(_MapLam);
    if (info != .@"struct") {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(_MapLam.call));
    const R = mapFnInfo.@"fn".return_type.?;

    if (R == noreturn) {
        @compileError("The return type of call function must not be noreturn!");
    }
    return R;
}

pub fn MapFnToLamType(comptime MapFn: type) type {
    return struct {
        map_fn: *const fn (a: MapFnInType(MapFn)) MapFnRetType(MapFn),

        const Self = @This();
        pub fn call(self: *const Self, a: MapFnInType(MapFn)) MapFnRetType(MapFn) {
            return self.map_fn(a);
        }
    };
}

pub fn mapFnToLam(map_fn: anytype) MapFnToLamType(@TypeOf(map_fn)) {
    const fn_info = @typeInfo(@TypeOf(map_fn));
    if (fn_info == .pointer) {
        return .{ .map_fn = map_fn };
    } else {
        return .{ .map_fn = &map_fn };
    }
}

pub fn AnyMapFn(a: anytype, b: anytype) type {
    return fn (@TypeOf(a)) @TypeOf(b);
}

/// The kind of map function for new a translated value or inplace replaced by
/// translated value.
pub const MapFnKind = enum {
    /// Need new a value for translated value, the caller should to free new
    /// value.
    NewValMap,
    /// Need new a value for translated value, the caller should to free new
    /// value.
    /// The input value of map function is a reference.
    /// The fa paramerter of fmap function is also a reference.
    NewValMapRef,
    /// Just inplace replace with translated value, the bitsize of translated
    /// value must equal bitsize of origin value.
    InplaceMap,
    /// Just inplace replace with translated value, the bitsize of translated
    /// value must equal bitsize of origin value.
    /// The input value of map function is a reference.
    /// The fa paramerter of fmap function is also a reference.
    InplaceMapRef,
};

pub fn isInplaceMap(comptime K: MapFnKind) bool {
    return K == .InplaceMap or K == .InplaceMapRef;
}

pub fn isMapRef(comptime K: MapFnKind) bool {
    return K == .NewValMapRef or K == .InplaceMapRef;
}

/// The mode of fmap is used to indicate whether the map function has a self
/// parameter.
pub const FMapMode = enum {
    /// The map function has only a input parameter.
    NormalMap,
    /// The map function is a lambda struct that has a map function with a
    /// self parameter.
    LambdaMap,
};

pub const RainbowColor = enum {
    Red,
    Orange,
    Yellow,
    Green,
    Blue,
    Indigo,
    Violet,
};

/// A identity function as unit of endofunctions
pub fn identity(a: anytype) @TypeOf(a) {
    return a;
}

pub fn getIdentityFn(comptime A: type) *const fn (A) A {
    return &struct {
        fn id(a: A) A {
            return a;
        }
    }.id;
}

pub fn getEffectIdentityFn(
    comptime E: ?type,
    comptime A: type,
) *const fn (A) EffectVal(E, A) {
    return &struct {
        fn impureId(a: A) EffectVal(E, A) {
            return a;
        }
    }.impureId;
}

pub fn IdentityLamType(comptime T: type) type {
    return struct {
        lam_ctx: void = {},

        const Self = @This();
        fn call(self: *Self, val: T) T {
            _ = self;
            return val;
        }
    };
}

pub fn getIdentityLam(comptime A: type) IdentityLamType(A) {
    return IdentityLamType(A){};
}

pub fn EffectIdentityLamType(E: ?type, T: type) type {
    return struct {
        lam_ctx: void = {},

        const Self = @This();
        fn call(self: *Self, val: T) EffectVal(E, T) {
            _ = self;
            return val;
        }
    };
}

pub fn getEffectIdentityLam(E: ?type, A: type) EffectIdentityLamType(E, A) {
    return EffectIdentityLamType(E, A){};
}

fn FnToImpureType(E: type, MapFn: type) type {
    return fn (MapFnInType(MapFn)) E!MapFnRetType(MapFn);
}

pub fn pureFnToImpure(E: type, comptime map_fn: anytype) FnToImpureType(E, @TypeOf(map_fn)) {
    const MapFn = @TypeOf(map_fn);
    return struct {
        fn impureFn(a: MapFnInType(MapFn)) E!MapFnRetType(MapFn) {
            return map_fn(a);
        }
    }.impureFn;
}

pub fn EffectVal(comptime E: ?type, comptime A: type) type {
    return if (E == null) A else E.?!A;
}

/// Any signle-argument function type
pub const AnyFnType = fn (usize) usize;
pub const AnyFnPtr = *const AnyFnType;

/// Any signle-argument lambda type
pub const AnyLamType = struct {
    lam_ctx: *anyopaque,
    const Self = @This();
    pub fn call(self: *Self, a: usize) usize {
        _ = self;
        _ = a;
    }
};

const BaseContextCfg = struct {
    allocator: Allocator,
    errors: ?type,
};

pub fn getDefaultBaseCfg(allocator: Allocator) BaseContextCfg {
    return .{
        .allocator = allocator,
        .errors = Allocator.Error,
    };
}

/// Define a lambda type for composable lambda that can compose functions and lambdas.
/// No matter how many functions and lambdas are combined, the composable lambda can be
/// considered as a single lambda containing the call function A->B.
/// The parameter cfg must has allocator field.
pub fn ComposableLam(
    comptime cfg: anytype,
    comptime A: type,
    comptime B: type,
) type {
    const has_err, const _B = comptime isErrorUnionOrVal(B);
    return struct {
        ref_count: usize,
        any_lam: *anyopaque,
        call_fn: *const fn (*anyopaque, A) B,
        ref_fn: *const fn (*Self) *Self,
        unref_fn: *const fn (*Self) bool,

        const Self = @This();
        const self_cfg = cfg;

        pub fn createByFn(map_fn: anytype) Allocator.Error!*Self {
            // @compileLog("createByFn map_fn type: " ++ @typeName(@TypeOf(map_fn)));
            return Self.create(mapFnToLam(map_fn));
        }

        pub fn create(init_lam: anytype) Allocator.Error!*Self {
            const InitLam = @TypeOf(init_lam);
            if (B != MapLamRetType(InitLam)) {
                @compileLog("init init_lam type: " ++ @typeName(@TypeOf(init_lam)));
                @compileLog("init RetType type: " ++ @typeName(MapLamRetType(InitLam)));
                @compileLog("init B type: " ++ @typeName(B));
            }
            comptime assert(A == MapLamInType(InitLam));
            comptime assert(B == MapLamRetType(InitLam));
            var any_lam: *anyopaque = undefined;
            const comp_lam = try cfg.allocator.create(Self);
            // std.debug.print("create comp_lam = {*}\n", .{comp_lam});
            comp_lam.* = if (@sizeOf(InitLam) <= @sizeOf(*anyopaque)) blk_t: {
                var any_lam_bytes = std.mem.asBytes(&any_lam);
                const tmp_lam = try copyOrCloneOrRef(init_lam);
                const tmp_lam_bytes = std.mem.asBytes(&tmp_lam);
                @memcpy(any_lam_bytes[0..@sizeOf(InitLam)], tmp_lam_bytes);

                const SmallLamFns = struct {
                    fn ref(self: *Self) *Self {
                        const self_any_lam_bytes = std.mem.asBytes(&self.any_lam);
                        var lam: InitLam = undefined;
                        const lam_bytes = std.mem.asBytes(&lam);
                        @memcpy(lam_bytes, self_any_lam_bytes[0..@sizeOf(InitLam)]);
                        if (@hasDecl(InitLam, "refSubLam"))
                            lam.refSubLam()
                        else
                            _ = tryStrongRef(lam);
                        self.ref_count += 1;
                        // std.debug.print("ref ref_count={d}, SmallLam = {*}\n", .{ self.ref_count, self });
                        return self;
                    }

                    fn unref(self: *Self) bool {
                        const self_any_lam_bytes = std.mem.asBytes(&self.any_lam);
                        var lam: InitLam = undefined;
                        const lam_bytes = std.mem.asBytes(&lam);
                        @memcpy(lam_bytes, self_any_lam_bytes[0..@sizeOf(InitLam)]);
                        // std.debug.print("unref ref_count={d}, SmallLam = {*}\n", .{ self.ref_count, self });

                        if (self.ref_count > 1) {
                            self.ref_count -= 1;
                            if (@hasDecl(InitLam, "unrefSubLam"))
                                unreachable
                                // lam.unrefSubLam()
                            else
                                tryStrongUnref(lam);
                            return false;
                        }

                        deinitOrUnref(lam);
                        // std.debug.print("destroy SmallLam comp_lam = {*}\n", .{self});
                        self.ref_count = 0;
                        cfg.allocator.destroy(self);
                        return true;
                    }

                    fn call(self_any_lam: *anyopaque, a: A) B {
                        const self_any_lam_bytes = std.mem.asBytes(&self_any_lam);
                        var lam: InitLam = undefined;
                        const lam_bytes = std.mem.asBytes(&lam);
                        @memcpy(lam_bytes, self_any_lam_bytes[0..@sizeOf(InitLam)]);
                        return lam.call(a);
                    }
                };
                break :blk_t .{
                    .ref_count = 1,
                    .any_lam = any_lam,
                    .call_fn = SmallLamFns.call,
                    .ref_fn = SmallLamFns.ref,
                    .unref_fn = SmallLamFns.unref,
                };
            } else blk_f: {
                const lam = try cfg.allocator.create(InitLam);
                // std.debug.print("create NormalLam = {*}\n", .{lam});
                lam.* = try copyOrCloneOrRef(init_lam);
                any_lam = @ptrCast(lam);

                const NormalLamFns = struct {
                    fn ref(self: *Self) *Self {
                        const real_lam: *InitLam = @alignCast(@ptrCast(self.any_lam));
                        if (@hasDecl(InitLam, "refSubLam"))
                            real_lam.refSubLam()
                        else
                            _ = tryStrongRef(real_lam);
                        self.ref_count += 1;
                        // std.debug.print("ref ref_count={d}, NormalLam = {*}\n", .{ self.ref_count, self });
                        return self;
                    }

                    fn unref(self: *Self) bool {
                        const real_lam: *InitLam = @alignCast(@ptrCast(self.any_lam));
                        // std.debug.print("unref ref_count={d}, NormalLam = {*}\n", .{ self.ref_count, self });
                        if (self.ref_count > 1) {
                            self.ref_count -= 1;
                            if (@hasDecl(InitLam, "unrefSubLam"))
                                real_lam.unrefSubLam()
                            else
                                tryStrongUnref(real_lam);
                            return false;
                        }

                        deinitOrUnref(real_lam.*);
                        // unreference real_lam self
                        tryStrongUnref(real_lam);
                        // std.debug.print("destroy NormalLam = {*}\n", .{real_lam});
                        cfg.allocator.destroy(real_lam);
                        self.ref_count = 0;
                        // std.debug.print("destroy NormalLam comp_lam = {*}\n", .{self});
                        cfg.allocator.destroy(self);
                        return true;
                    }

                    fn call(self_any_lam: *anyopaque, a: A) B {
                        const real_lam: *InitLam = @alignCast(@ptrCast(self_any_lam));
                        return real_lam.call(a);
                    }
                };
                break :blk_f .{
                    .ref_count = 1,
                    .any_lam = any_lam,
                    .call_fn = NormalLamFns.call,
                    .ref_fn = NormalLamFns.ref,
                    .unref_fn = NormalLamFns.unref,
                };
            };
            return comp_lam;
        }

        pub fn strongRef(self: *Self) *Self {
            _ = self.ref_fn(self);
            return self;
        }

        pub fn strongUnref(self: *Self) bool {
            return self.unref_fn(self);
        }

        fn AppendedRetType(comptime InType: type, comptime Lam: type) type {
            const in_info = @typeInfo(InType);
            const LamRet = MapLamRetType(Lam);
            if (in_info != .error_union) {
                return LamRet;
            }

            const ret_info = @typeInfo(LamRet);
            const InError = in_info.error_union.error_set;
            const OutError, const RetType = if (ret_info == .error_union)
                .{ InError || ret_info.error_union.error_set, ret_info.error_union.payload }
            else
                .{ InError, LamRet };
            return OutError!RetType;
        }

        /// Append a single argument function to a composable lambda.
        /// Note: this function will consume the self.
        pub fn appendFn(
            self: *Self,
            map_fn: anytype,
        ) Allocator.Error!*ComposableLam(cfg, A, AppendedRetType(B, MapFnToLamType(@TypeOf(map_fn)))) {
            return self.appendLam(mapFnToLam(map_fn));
        }

        /// Append a single argument lambda to a composable lambda.
        /// Note: this function will consume the self.
        pub fn appendLam(
            self: *Self,
            map_lam: anytype,
        ) Allocator.Error!*ComposableLam(cfg, A, AppendedRetType(B, @TypeOf(map_lam))) {
            const MapLam = @TypeOf(map_lam);
            const InType = MapLamInType(MapLam);
            comptime assert(_B == InType);
            const RetType = AppendedRetType(B, MapLam);

            const AppendedCompLam = struct {
                comp_lam: *Self,
                append_lam: MapLam,

                const SelfNew = @This();
                pub fn refSubLam(self_new: *const SelfNew) void {
                    // std.debug.print("appended_comp_lam refSubLam comp_lam={*}\n", .{self_new.comp_lam});
                    _ = self_new.comp_lam.strongRef();
                    _ = tryStrongRef(self_new.append_lam);
                }

                pub fn unrefSubLam(self_new: SelfNew) void {
                    // std.debug.print("appended_comp_lam unrefSubLam comp_lam={*}\n", .{self_new.comp_lam});
                    _ = self_new.comp_lam.strongUnref();
                    tryStrongUnref(self_new.append_lam);
                }

                pub fn deinit(self_new: SelfNew) void {
                    // std.debug.print("appended_comp_lam deinit comp_lam={*}\n", .{self_new.comp_lam});
                    _ = self_new.comp_lam.strongUnref();
                    deinitOrUnref(self_new.append_lam);
                }

                pub fn call(self_new: *SelfNew, a: A) RetType {
                    if (has_err) {
                        return self_new.append_lam.call(try self_new.comp_lam.call(a));
                    } else {
                        return self_new.append_lam.call(self_new.comp_lam.call(a));
                    }
                }
            };

            const appended_comp_lam = AppendedCompLam{
                .comp_lam = self,
                .append_lam = try copyOrCloneOrRef(map_lam),
            };
            // std.debug.print("appended_comp_lam comp_lam={*}\n", .{appended_comp_lam.comp_lam});
            return ComposableLam(cfg, A, RetType).create(appended_comp_lam);
        }

        pub fn call(self: *const Self, a: A) B {
            return self.call_fn(self.any_lam, a);
        }
    };
}

test ComposableLam {
    const cfg = getDefaultBaseCfg(testing.allocator);
    var add_pi_lam = testu.Add_x_f64_Lam{ ._x = 3.14 };
    _ = &add_pi_lam;
    var div_5_lam = testu.Div_x_u32_Lam{ ._x = 5 };
    _ = &div_5_lam;
    var add_e_f32_lam = testu.Add_x_f32_Lam{ ._x = 2.72 };
    _ = &add_e_f32_lam;
    var point_move_lam = testu.Point3_offset_u32_Lam{ ._point = .{ 46.2, 26.83, 72.56 } };
    _ = &point_move_lam;

    const comp1 = try ComposableLam(cfg, u32, f64).create(add_pi_lam);
    const comp2 = try comp1.appendLam(div_5_lam);
    try testing.expectEqual(8, comp2.call(40));
    const comp3 = try comp2.appendLam(add_e_f32_lam);
    try testing.expectEqual(10.72, comp3.call(40));
    _ = comp3.strongUnref();

    const comp11 = try ComposableLam(cfg, u32, f64).create(add_pi_lam);
    const comp12 = try comp11.appendLam(div_5_lam);
    const comp13 = try comp12.appendLam(point_move_lam);
    try testing.expectEqual(.{ 54.2, 34.83, 80.56 }, comp13.call(40));
    _ = comp13.strongUnref();
}

pub fn LamWrapper(comptime cfg: anytype, comptime Lam: type) type {
    if (@typeInfo(Lam) != .@"struct") {
        @compileError("The parameter lam must be a struct!");
    }

    const A = MapLamInType(Lam);
    const B = MapLamRetType(Lam);

    return struct {
        lam_self: *anyopaque,
        const Self = @This();

        pub fn init(lam: Lam) Self {
            const lam_self = try cfg.allocator.create(Lam);
            @memcpy(lam_self, &lam);
            return .{ .lam_self = @ptrCast(lam_self) };
        }

        pub fn deinit(self: Self) void {
            const lam_self: *Lam = @alignCast(@ptrCast(self.lam_self));
            deinitOrUnref(lam_self.*);
            cfg.allocator.destroy(lam_self);
        }

        pub fn call(self: *Self, a: A) B {
            const lam_self: *Lam = @alignCast(@ptrCast(self.lam_self));
            Lam.call(lam_self, a);
        }
    };
}

pub fn anyLamFromLam(comptime cfg: anytype, lam: anytype) !AnyLamType {
    const Lam = @TypeOf(lam);
    const lam_wrap = try LamWrapper(cfg, Lam).init(lam);
    return @bitCast(lam_wrap);
}

fn FnOrLamInType(comptime FnOrLam: type) type {
    switch (@typeInfo(FnOrLam)) {
        .@"fn" => return MapFnInType(FnOrLam),
        .@"struct" => return MapLamInType(FnOrLam),
        else => @compileError("Expect FnOrLam be a function or lambda, found '" ++ @typeName(FnOrLam) ++ "'"),
    }
}

fn FnOrLamRetType(comptime FnOrLam: type) type {
    switch (@typeInfo(FnOrLam)) {
        .@"fn" => return MapFnRetType(FnOrLam),
        .@"struct" => return MapLamRetType(FnOrLam),
        else => @compileError("Expect FnOrLam be a function or lambda, found '" ++ @typeName(FnOrLam) ++ "'"),
    }
}

fn manyTupleAllTypes(comptime ManyTuple: type) []const type {
    const tuple_info = @typeInfo(ManyTuple);
    if (tuple_info != .@"struct") {
        @compileError("Expect ManyTuple be a tuple, found '" ++ @typeName(ManyTuple) ++ "'");
    }

    const fields = tuple_info.@"struct".fields;
    if (fields.len == 0) {
        @compileError("The ManyTuple(" ++ @typeName(ManyTuple) ++ ") is a empty tuple!");
    }
    var types: [fields.len]type = undefined;
    types[0] = fields[0].type;
    if (fields.len == 1) {
        return types[0..];
    }

    // check that all types match each other
    for (fields[1..], 1..) |field, i| {
        types[i] = field.type;
        const PrevRetType = FnOrLamRetType(types[i - 1]);
        const InType = FnOrLamInType(types[i]);
        comptime assert(PrevRetType == InType);
    }

    return types[0..];
}

pub fn ComposedFnType(many_tuple: anytype) type {
    const ManyTuple = @TypeOf(many_tuple);
    const all_types = manyTupleAllTypes(ManyTuple);
    const InType = FnOrLamInType(all_types[0]);
    const RetType = FnOrLamRetType(all_types[all_types.len - 1]);

    return fn (InType) RetType;
}

/// Compose many functions or lambdas to a single function in comptime.
/// Parameter many_tuple is a tuple of many functions or lambdas.
// This function is inspired from mcomposefns by YangMiao<sdzx-1>
pub fn comptimeCompose(many_tuple: anytype) ComposedFnType(many_tuple) {
    const ManyTuple = @TypeOf(many_tuple);
    const tuple_info = @typeInfo(ManyTuple);

    const fields = tuple_info.@"struct".fields;
    return struct {
        const A = FnOrLamInType(fields[0].type);
        const B = FnOrLamRetType(fields[fields.len - 1].type);
        fn callSubFns(comptime i: usize, in: A) FnOrLamRetType(fields[i].type) {
            const fn_or_lam = @field(many_tuple, fields[i].name);
            switch (@typeInfo(fields[i].type)) {
                .@"fn" => {
                    if (i == 0) {
                        return @call(.auto, fn_or_lam, .{in});
                    } else {
                        return @call(.auto, fn_or_lam, .{callSubFns(i - 1, in)});
                    }
                },
                .@"struct" => {
                    const Lam = @TypeOf(fn_or_lam);
                    if (i == 0) {
                        return @call(.auto, Lam.call, .{ &fn_or_lam, in });
                    } else {
                        return @call(.auto, Lam.call, .{ &fn_or_lam, callSubFns(i - 1, in) });
                    }
                },
                else => @compileError("comptimeCompose can not support type: " ++ @typeName(fields[i].type)),
            }
        }

        fn composedFn(a: A) B {
            return callSubFns(fields.len - 1, a);
        }
    }.composedFn;
}

test comptimeCompose {
    const f1 = comptimeCompose(.{ testu.add4, testu.add_pi_f64 });
    try testing.expectEqual(47.14, f1(40));
    const f2 = comptimeCompose(.{ div3FromF64, testu.add_pi_f32 });
    try testing.expectEqual(18.14, f2(47.14));

    const f1f2 = comptimeCompose(.{ f1, f2 });
    try testing.expectEqual(18.14, f1f2(40));

    const add_pi_lam = testu.Add_x_f64_Lam{ ._x = 3.14 };
    const f3 = comptimeCompose(.{ testu.add10, add_pi_lam });
    try testing.expectEqual(53.14, f3(40));
    const div_5_lam = testu.Div_x_u32_Lam{ ._x = 5 };
    const f4 = comptimeCompose(.{ div_5_lam, add_pi_lam });
    try testing.expectEqual(13.14, f4(53.14));

    const f3f4 = comptimeCompose(.{ f3, f4 });
    try testing.expectEqual(13.14, f3f4(40));

    // test invalid struct for lambda
    // const bad_lam = struct { a: u32, b: f64 }{ .a = 3, .b = 2.73 };
    // const bad_f = comptimeCompose(.{ testu.add10, bad_lam });
    // try testing.expectEqual(5.73, bad_f(42));

    // test composing incorrect type
    // const bad_lam1 = union { a: u32, b: f64 }{ .a = 3 };
    // const bad_f1 = comptimeCompose(.{ testu.add10, bad_lam1 });
    // try testing.expectEqual(5.73, bad_f1(42));
}

fn ComposedTwoFn(comptime A: type, comptime B: type, comptime C: type) type {
    return struct {
        first_fn: *const fn (A) B,
        second_fn: *const fn (B) C,
        const SelfComp = @This();
        fn call(selfComp: *const SelfComp, a: A) C {
            return selfComp.second_fn(selfComp.first_fn(a));
        }
    };
}

fn ComposedManyFn(
    comptime N: comptime_int,
    comptime TS: [N]type,
) type {
    if (N < 4) {
        @compileError("Too less types for ComposedManyFn");
    }
    return struct {
        fns_array: ArrayList(AnyFnPtr),

        const Self = @This();
        const N_FNS = N - 1;
        pub fn FnsTypes() [N_FNS]type {
            comptime var fn_types: [N_FNS]type = undefined;
            inline for (TS[0..N_FNS], 0..) |T, i| {
                fn_types[i] = *const fn (T) TS[i + 1];
            }
            return fn_types;
        }

        pub fn call(self: *const Self, a: TS[0]) TS[N - 1] {
            assert(N_FNS == self.fns_array.items.len);
            var results: std.meta.Tuple(TS[0..]) = undefined;
            results[0] = a;
            comptime var i = 0;
            inline while (i < N - 1) : (i += 1) {
                const fn_ptr = @as(FnsTypes()[i], @ptrCast(self.fns_array.items[i]));
                results[i + 1] = fn_ptr(results[i]);
            }
            return results[N - 1];
        }
    };
}

/// Define a lambda type for composable function for function composition
pub fn ComposableFn(comptime cfg: anytype, comptime N: comptime_int, TS: [N]type) type {
    // The CompsableFn must has a function.
    comptime assert(N >= 2);
    return union(enum) {
        single_fn: if (N == 2) *const fn (A) B else void,
        composed_two: if (N == 3) ComposedTwoFn(A, TS[1], TS[2]) else void,
        composed_many: if (N > 3) ComposedManyFn(N, TS) else void,

        const Self = @This();
        const Error: ?type = cfg.errors;
        const CompN = N;
        const CompTS = TS;
        const A = TS[0];
        const B = TS[N - 1];

        pub fn init(map_fn: *const fn (TS[0]) TS[1]) Self {
            return .{ .single_fn = map_fn };
        }

        pub fn initTwo(
            map_fn1: *const fn (TS[0]) TS[1],
            map_fn2: *const fn (TS[1]) TS[2],
        ) Self {
            return .{ .composed_two = .{
                .first_fn = map_fn1,
                .second_fn = map_fn2,
            } };
        }

        pub fn deinit(self: Self) void {
            if (N > 3) {
                self.composed_many.fns_array.deinit();
            }
        }

        fn ComposeType(comptime CompFn: type) type {
            const M = CompFn.CompN;
            const TS1 = CompFn.CompTS;
            return ComposableFn(cfg, N + M - 1, TS ++ TS1[1..].*);
        }

        /// The parameter compfn1 is a ComposableFn
        pub fn compose(
            self: Self,
            compfn1: anytype,
        ) EffectVal(Error, ComposeType(@TypeOf(compfn1))) {
            const M = @TypeOf(compfn1).CompN;
            const TS1 = @TypeOf(compfn1).CompTS;
            const InType = TS1[0];
            const RetType = TS1[M - 1];
            comptime assert(B == InType);
            // @compileLog(std.fmt.comptimePrint("A is: {any}", .{A}));
            // @compileLog(std.fmt.comptimePrint("B is: {any}", .{B}));
            // @compileLog(std.fmt.comptimePrint("TS is: {any}", .{TS}));
            // @compileLog(std.fmt.comptimePrint("RetType is: {any}", .{RetType}));

            if (N == 2) {
                switch (M) {
                    2 => {
                        // return a new composable function
                        return .{ .composed_two = ComposedTwoFn(A, B, RetType){
                            .first_fn = self.single_fn,
                            .second_fn = compfn1.single_fn,
                        } };
                    },
                    3 => {
                        var fns_array = try ArrayList(AnyFnPtr).initCapacity(cfg.allocator, N + 2);
                        fns_array.appendAssumeCapacity(@ptrCast(self.single_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(compfn1.composed_two.first_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(compfn1.composed_two.second_fn));
                        const NewTS = TS ++ TS1[1..].*;
                        // return a new composable function
                        return .{ .composed_many = ComposedManyFn(N + M - 1, NewTS){
                            .fns_array = fns_array,
                        } };
                    },
                    else => {
                        var fns_array = try ArrayList(AnyFnPtr).initCapacity(cfg.allocator, N + 2);
                        fns_array.appendAssumeCapacity(@ptrCast(self.single_fn));
                        try fns_array.appendSlice(compfn1.composed_many.fns_array.items);
                        const NewTS = TS ++ TS1[1..].*;
                        // return a new composable function
                        return .{ .composed_many = ComposedManyFn(N + M - 1, NewTS){
                            .fns_array = fns_array,
                        } };
                    },
                }
            } else if (N == 3) {
                var fns_array = try ArrayList(AnyFnPtr).initCapacity(cfg.allocator, N + 1);
                switch (M) {
                    2 => {
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.first_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.second_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(compfn1.single_fn));
                    },
                    3 => {
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.first_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.second_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(compfn1.composed_two.first_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(compfn1.composed_two.second_fn));
                    },
                    else => {
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.first_fn));
                        fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.second_fn));
                        try fns_array.appendSlice(compfn1.composed_many.fns_array.items);
                    },
                }
                const NewTS = TS ++ TS1[1..].*;
                // return a new composable function
                return .{ .composed_many = ComposedManyFn(N + M - 1, NewTS){
                    .fns_array = fns_array,
                } };
            } else {
                // @compileLog(std.fmt.comptimePrint("many_fn TS is: {any}", .{TS}));
                var fns_array = self.composed_many.fns_array;
                switch (M) {
                    2 => {
                        try fns_array.append(@ptrCast(compfn1.single_fn));
                    },
                    3 => {
                        try fns_array.append(@ptrCast(compfn1.composed_two.first_fn));
                        try fns_array.append(@ptrCast(compfn1.composed_two.second_fn));
                    },
                    else => {
                        try fns_array.appendSlice(compfn1.composed_many.fns_array.items);
                    },
                }
                const NewTS = TS ++ TS1[1..].*;
                // return a new composable function
                return .{ .composed_many = ComposedManyFn(N + M - 1, NewTS){
                    .fns_array = fns_array,
                } };
            }
        }

        /// This function append a map_fn to a composable function, the map_fn must be
        /// a single parameter function
        pub fn append(
            self: Self,
            map_fn: anytype,
        ) EffectVal(Error, ComposableFn(cfg, N + 1, TS ++ [1]type{MapFnRetType(@TypeOf(map_fn))})) {
            const InType = MapFnInType(@TypeOf(map_fn));
            const RetType = MapFnRetType(@TypeOf(map_fn));
            comptime assert(B == InType);

            if (N == 2) {
                // return a new composable function
                return .{ .composed_two = ComposedTwoFn(A, B, RetType){
                    .first_fn = self.single_fn,
                    .second_fn = map_fn,
                } };
            } else {
                var fns_array: ArrayList(AnyFnPtr) = undefined;
                if (N == 3) {
                    fns_array = try ArrayList(AnyFnPtr).initCapacity(cfg.allocator, N + 1);
                    fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.first_fn));
                    fns_array.appendAssumeCapacity(@ptrCast(self.composed_two.second_fn));
                    fns_array.appendAssumeCapacity(@ptrCast(map_fn));
                } else {
                    fns_array = self.composed_many.fns_array;
                    try fns_array.append(@ptrCast(map_fn));
                }
                const NewTS = TS ++ [_]type{RetType};
                // return a new composable function
                return .{ .composed_many = ComposedManyFn(N + 1, NewTS){
                    .fns_array = fns_array,
                } };
            }
        }

        pub fn clone(self: Self) EffectVal(Error, Self) {
            if (N > 3) {
                return .{ .composed_many = .{
                    .fns_array = try self.composed_many.fns_array.clone(),
                } };
            }
            return self;
        }

        pub fn call(self: *const Self, a: A) B {
            if (N == 2) {
                return self.single_fn(a);
            } else if (N == 3) {
                return self.composed_two.call(a);
            } else {
                return self.composed_many.call(a);
            }
        }
    };
}

fn ComposedTwoLam(comptime LAM1: type, comptime LAM2: type) type {
    return struct {
        first_lam: LAM1,
        second_lam: LAM2,

        const Self = @This();
        const A = MapLamInType(LAM1);
        const B = MapLamRetType(LAM2);
        fn call(self: *const Self, a: A) B {
            return self.second_lam.call(self.first_lam.call(a));
        }
    };
}

fn ComposedManyLam(
    comptime cfg: anytype,
    comptime Num: comptime_int,
    comptime LamTypes: [Num]type,
) type {
    // if (N < 3) {
    //     @compileError("Too less types for ComposedManyFn");
    // }
    return struct {
        const Self = @This();
        const N = Num;
        const LAMS = LamTypes;
        const A = MapLamInType(LAMS[0]);
        const B = MapLamRetType(LAMS[N - 1]);

        fn initSliceWithTuple(lams: []AnyLamType, lams_tuple: anytype) void {
            const fields = std.meta.fields(@TypeOf(lams_tuple));
            assert(lams_tuple.len == N);
            inline for (fields, 0..) |field, i| {
                comptime assert(LAMS[i] == field.type);
                lams[i] = anyLamFromLam(cfg, lams_tuple[i]);
            }
        }

        fn deinitSlice(lams: []AnyLamType) []AnyLamType {
            assert(N <= lams.len);
            var i: usize = 0;
            while (i < N) : (i += 1) {
                const map_lam: LamWrapper(cfg, LAMS[i]) = @bitCast(lams[i]);
                deinitOrUnref(map_lam);
            }
            return lams[N..];
        }

        fn AppendLam(comptime Lam: type) type {
            const InType = MapLamInType(Lam);
            comptime assert(B == InType);
            return ComposedManyLam(cfg, Self.N + 1, Self.LAMS ++ [1]type{Lam});
        }

        fn ValTypes() [N + 1]type {
            comptime var val_types: [N + 1]type = undefined;
            val_types[0] = MapLamInType(LAMS[0]);
            inline for (LAMS, 0..) |LAM, i| {
                val_types[i + 1] = MapLamRetType(LAM);
            }
            return val_types;
        }

        fn callSlice(lam_and_a: struct { []AnyLamType, A }) struct { []AnyLamType, B } {
            const lams, const a = lam_and_a;
            assert(N <= lams.len);
            var results: std.meta.Tuple(ValTypes[0..]) = undefined;
            results[0] = a;
            comptime var i = 0;
            inline while (i < N) : (i += 1) {
                const map_lam: LAMS[i] = @bitCast(lams[i]);
                results[i + 1] = map_lam.call(results[i]);
            }
            return .{ lams[N..], results[N] };
        }
    };
}

pub fn ComposedLamType(comptime cfg: anytype, many_tuple: anytype) type {
    const ManyTuple = @TypeOf(many_tuple);
    const all_types = comptime manyTupleAllTypes(ManyTuple);
    const A = MapLamInType(all_types[0]);
    const B = MapLamRetType(all_types[all_types.len - 1]);

    return ComposeManyLams(cfg, A, B);
}

pub fn composeLams(
    comptime cfg: anytype,
    lams_tuple: anytype,
) ComposedLamType(cfg, lams_tuple) {
    const CompLam = ComposedLamType(cfg, lams_tuple);
    const all_types = comptime manyTupleAllTypes(@TypeOf(lams_tuple));
    const ManyLamType = ComposedManyLam(cfg, all_types.len, all_types[0..]);
    return CompLam.init(ManyLamType, lams_tuple);
}

/// Define a lambda type for composable lambda for function composition
/// The parameter cfg must has allocator field.
pub fn ComposeManyLams(
    comptime cfg: anytype,
    comptime InType: type,
    comptime RetType: type,
) type {
    const cfg_has_allocator = @hasField(@TypeOf(cfg), "allocator");
    if (!cfg_has_allocator) {
        @compileError("The parameter cfg(" ++ @typeName(@TypeOf(cfg)) ++ ") must has allocator field!");
    }

    // The CompsableLam must has a lambda.
    return struct {
        lams_array: ArrayList(AnyLamType),
        deinit_slice: *const fn ([]AnyLamType) []AnyLamType,
        call_slice: *const fn (struct { []AnyLamType, A }) struct { []AnyLamType, B },

        const Self = @This();
        const Error: ?type = cfg.errors;
        const A = InType;
        const B = RetType;

        pub fn init(comptime ManyLamType: type, lams_tuple: anytype) EffectVal(Error, Self) {
            const len: usize = @max(4, lams_tuple.len);
            var lams_array = try ArrayList(AnyLamType).initCapacity(cfg.allotcator, len);
            _ = &lams_array;
            ManyLamType.initSliceWithTuple(lams_array.items, lams_tuple);
            return Self{
                .lams_array = lams_array,
                .deinit_slice = ManyLamType.deinitSlice,
                .call_slice = ManyLamType.callSlice,
            };
        }

        pub fn deinit(self: Self) void {
            self.deinit_slice(self.lams_array.items);
            self.lams_array.deinit();
        }

        fn ComposedType(comptime CompLam: type) type {
            const C = CompLam.A;
            const D = CompLam.B;
            comptime assert(B == C);
            return ComposeManyLams(cfg, A, D);
        }

        /// The parameter complam1 is a ComposeManyLams
        pub fn compose(
            self: Self,
            complam1: anytype,
        ) EffectVal(Error, ComposedType(@TypeOf(complam1))) {
            const CompLam = @TypeOf(complam1);
            const C = CompLam.A;
            const D = CompLam.B;
            comptime assert(B == C);
            // @compileLog(std.fmt.comptimePrint("A is: {any}", .{A}));
            // @compileLog(std.fmt.comptimePrint("B is: {any}", .{B}));
            // @compileLog(std.fmt.comptimePrint("D is: {any}", .{D}));

            const RetCompLam = ComposeManyLams(cfg, A, D);
            var lams_array = self.lams_array;
            try lams_array.appendSlice(complam1.lams_array.items);
            return RetCompLam{
                .lams_array = lams_array,
                .deinit_slice = comptimeCompose(self.deinit_slice, complam1.deinit_slice),
                .call_slice = comptimeCompose(self.call_slice, complam1.call_slice),
            };
        }

        fn AppendedType(comptime Lam: type) type {
            const C = MapLamInType(Lam);
            const D = MapLamRetType(Lam);
            comptime assert(B == C);
            // ManyLamType.AppendLam(Lam);
            return ComposeManyLams(cfg, A, D);
        }

        /// This function append a map_lam to a composable function, the map_lam must be
        /// a single parameter lambda
        pub fn append(
            self: Self,
            map_lam: anytype,
        ) EffectVal(Error, AppendedType(@TypeOf(map_lam))) {
            const MapLam = @TypeOf(map_lam);
            const C = MapLamInType(MapLam);
            // const D = MapLamRetType(MapLam);
            comptime assert(B == C);
            // const CompLam = AppendedType(MapLam);

            const map_lam_wrapped = anyLamFromLam(cfg, map_lam);
            try self.lams_array.append(map_lam_wrapped);
        }

        pub fn clone(self: Self) EffectVal(Error, Self) {
            return .{
                .lams_array = try self.lams_array.clone(),
                .deinit_slice = self.deinit_slice,
                .call_slice = self.call_slice,
            };
        }

        pub fn call(self: *const Self, a: A) B {
            // if (N == 1) {
            //     return self.single_lam.call(a);
            // } else if (N == 2) {
            //     return self.composed_two.call(a);
            // } else {
            //     return self.composed_many.call(a);
            // }
            const rem_lams, const ret_val = self.call_slice(.{ self.lams_array.items, a });
            assert(rem_lams.len == 0);
            return ret_val;
        }
    };
}

fn div3FromF64(x: f64) u32 {
    const a: u32 = @intFromFloat(x);
    return @divFloor(a, 3);
}

fn rainbowColorFromU32(a: u32) RainbowColor {
    return @enumFromInt(@mod(a, 7));
}

test ComposableFn {
    const allocator = testing.allocator;
    const cfg = comptime getDefaultBaseCfg(allocator);
    const add10_types = [_]type{ u32, u32 };

    // test append function
    const comp_fn1 = ComposableFn(cfg, 2, add10_types).init(&testu.add10);
    defer comp_fn1.deinit();
    const comp_fn2 = try (try comp_fn1.clone()).append(&testu.add_pi_f64);
    defer comp_fn2.deinit();
    const comp_fn3 = try (try comp_fn2.clone()).append(&div3FromF64);
    defer comp_fn3.deinit();
    const comp_fn4 = try (try comp_fn3.clone()).append(&rainbowColorFromU32);
    defer comp_fn4.deinit();

    try testing.expectEqual(33, comp_fn1.call(23));
    try testing.expectEqual(36.14, comp_fn2.call(23));
    try testing.expectEqual(12, comp_fn3.call(23));
    try testing.expectEqual(.Indigo, comp_fn4.call(23));

    // test compose function
    const comp_fn11 = try (try comp_fn1.clone()).compose(comp_fn1);
    defer comp_fn11.deinit();
    const comp_fn12 = try (try comp_fn1.clone()).compose(comp_fn2);
    defer comp_fn12.deinit();
    const comp_fn13 = try (try comp_fn1.clone()).compose(comp_fn3);
    defer comp_fn13.deinit();
    const comp_fn14 = try (try comp_fn1.clone()).compose(comp_fn4);
    defer comp_fn14.deinit();

    try testing.expectEqual(43, comp_fn11.call(23));
    try testing.expectEqual(46.14, comp_fn12.call(23));
    try testing.expectEqual(15, comp_fn13.call(23));
    try testing.expectEqual(.Orange, comp_fn14.call(23));

    const comp_two = ComposableFn(cfg, 3, [_]type{ u32, f64, u32 }).initTwo(
        &testu.add_pi_f64,
        &div3FromF64,
    );
    const comp_fn21 = try comp_two.compose(comp_fn1);
    defer comp_fn21.deinit();
    const comp_fn22 = try (try comp_two.clone()).compose(comp_fn2);
    defer comp_fn22.deinit();
    const comp_fn23 = try (try comp_two.clone()).compose(comp_fn3);
    defer comp_fn23.deinit();
    const comp_fn24 = try (try comp_two.clone()).compose(comp_fn4);
    defer comp_fn24.deinit();

    try testing.expectEqual(18, comp_fn21.call(23));
    try testing.expectEqual(21.14, comp_fn22.call(23));
    try testing.expectEqual(7, comp_fn23.call(23));
    try testing.expectEqual(.Red, comp_fn24.call(23));

    const comp_fn31 = try (try comp_fn3.clone()).compose(comp_fn1);
    defer comp_fn31.deinit();
    const comp_fn32 = try (try comp_fn3.clone()).compose(comp_fn2);
    defer comp_fn32.deinit();
    const comp_fn33 = try (try comp_fn3.clone()).compose(comp_fn3);
    defer comp_fn33.deinit();
    const comp_fn34 = try (try comp_fn3.clone()).compose(comp_fn4);
    defer comp_fn34.deinit();

    try testing.expectEqual(22, comp_fn31.call(23));
    try testing.expectEqual(25.14, comp_fn32.call(23));
    try testing.expectEqual(8, comp_fn33.call(23));
    try testing.expectEqual(.Orange, comp_fn34.call(23));
}

fn ComposeTwoFn(map_fn1: anytype, map_fn2: anytype) type {
    const A = MapFnInType(@TypeOf(map_fn1));
    const B = MapFnRetType(@TypeOf(map_fn1));
    const B1 = MapFnInType(@TypeOf(map_fn2));
    const C = MapFnRetType(@TypeOf(map_fn2));
    comptime assert(B == B1);

    return struct {
        first_fn: *const fn (A) B,
        second_fn: *const fn (B) C,

        const Self = @This();
        pub fn call(self: *Self, a: A) C {
            return self.second_fn(self.first_fn(a));
        }
    };
}

fn composeTwoFn(map_fn1: anytype, map_fn2: anytype) ComposeTwoFn(map_fn1, map_fn2) {
    return .{ .first_fn = map_fn1, .second_fn = map_fn2 };
}

/// Check the type EA whether it is a ErrorUnion, if true then return a under
/// type of ErrorUnion, else just return type EA.
pub fn isErrorUnionOrVal(comptime EA: type) struct { bool, type } {
    const info = @typeInfo(EA);
    const has_error = if (info == .error_union) true else false;
    const A = if (has_error) info.error_union.payload else EA;
    return .{ has_error, A };
}

pub fn castInplaceValue(comptime T: type, val: anytype) T {
    const info = @typeInfo(@TypeOf(val));
    switch (info) {
        .optional => {
            const v = val orelse return null;
            return castInplaceValue(std.meta.Child(T), v);
        },
        .@"struct" => {
            if (info.@"struct".layout == .auto) {
                @compileError("Can't inplace cast struct with auto layout");
            }
            return @bitCast(val);
        },
        else => {
            return @bitCast(val);
        },
    }
}

pub fn defaultVal(comptime T: type) T {
    const info_a = @typeInfo(T);
    if (info_a == .@"fn") {
        return getDefaultFn(T);
    } else if (info_a == .pointer and @typeInfo(std.meta.Child(T)) == .@"fn") {
        return getDefaultFn(std.meta.Child(T));
    }
    return std.mem.zeroes(T);
}

pub fn getDefaultFn(comptime Fn: type) fn (MapFnInType(Fn)) MapFnRetType(Fn) {
    return struct {
        const A = MapFnInType(Fn);
        const B = MapFnRetType(Fn);
        fn defaultFn(a: A) B {
            _ = a;
            return std.mem.zeroes(B);
        }
    }.defaultFn;
}

pub fn Maybe(comptime A: type) type {
    return ?A;
}

pub fn Array(comptime len: usize) TCtor {
    return struct {
        fn ArrayF(comptime A: type) type {
            return [len]A;
        }
    }.ArrayF;
}

pub fn FreeTFn(comptime T: type) type {
    return *const fn (T) void;
}

/// Get a empty free function that do nothing
pub fn getFreeNothing(comptime T: type) FreeTFn(T) {
    return struct {
        fn freeT(a: T) void {
            _ = a;
        }
    }.freeT;
}

/// A empty free function, do nothing
pub fn freeNothing(a: anytype) void {
    _ = a;
    return;
}

/// Try to referance a pointer, else do nothing
pub fn tryStrongRef(a: anytype) @TypeOf(a) {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .pointer => {
            const Child = info.pointer.child;
            const child_info = @typeInfo(Child);
            if (info.pointer.size != .one) {
                @compileError("tryRef only for pointer that has only one element!");
            }
            switch (child_info) {
                .@"struct", .@"enum", .@"union", .@"opaque" => {
                    if (@hasDecl(Child, "strongRef")) {
                        return a.strongRef();
                    }
                },
                else => {},
            }
        },
        else => {},
    }

    return a;
}

/// Clone a constructed data or referance a pointer
pub fn copyOrCloneOrRef(a: anytype) !@TypeOf(a) {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => {
            if (@hasDecl(T, "clone")) {
                return a.clone();
            }
        },
        .pointer => {
            const Child = info.pointer.child;
            const child_info = @typeInfo(Child);
            if (info.pointer.size != .one) {
                @compileError("copyOrCloneOrRef only for pointer that has only one element!");
            }
            switch (child_info) {
                .@"struct", .@"enum", .@"union", .@"opaque" => {
                    if (@hasDecl(Child, "strongRef")) {
                        return a.strongRef();
                    }
                },
                else => {},
            }
        },
        else => {},
    }

    return a;
}

/// get a normal deinit or unreference function for free some memory
pub fn getDeinitOrUnref(comptime T: type) FreeTFn(T) {
    return struct {
        fn freeT(a: T) void {
            deinitOrUnref(a);
        }
    }.freeT;
}

/// Try to unreferance a pointer, else do nothing
pub fn tryStrongUnref(a: anytype) void {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .pointer => {
            const Child = info.pointer.child;
            const child_info = @typeInfo(Child);
            if (info.pointer.size != .one) {
                @compileError("nothingOrUnref only for pointer that has only one element!");
            }
            switch (child_info) {
                .@"struct", .@"enum", .@"union", .@"opaque" => {
                    if (@hasDecl(Child, "strongUnref")) {
                        _ = a.strongUnref();
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}

/// Deinit a constructed data or unreferance a pointer
pub fn deinitOrUnref(a: anytype) void {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .@"struct", .@"enum", .@"union", .@"opaque" => {
            if (@hasDecl(T, "deinit")) {
                a.deinit();
            }
        },
        .pointer => {
            const Child = info.pointer.child;
            const child_info = @typeInfo(Child);
            if (info.pointer.size != .one) {
                @compileError("deinitOrUnref only for pointer that has only one element!");
            }
            switch (child_info) {
                .@"struct", .@"enum", .@"union", .@"opaque" => {
                    if (@hasDecl(Child, "strongUnref")) {
                        _ = a.strongUnref();
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}
