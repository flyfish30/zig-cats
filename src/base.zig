//! All base types and functions for zig-cats
const std = @import("std");
const testing = std.testing;
const testu = @import("test_utils.zig");

const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

// pub usingnamespace @import("base_types.zig");

/// A single-argument type function for type constructor
pub const TCtor = *const fn (comptime type) type;

pub fn GetPointerChild(comptime P: type) type {
    if (@typeInfo(P) != .Pointer) {
        @compileError("The type P must be a Pointer type!");
    }
    return std.meta.Child(P);
}

pub fn MapFnInType(comptime MapFn: type) type {
    const _MapFn = if (@typeInfo(MapFn) == .Pointer) std.meta.Child(MapFn) else MapFn;
    const info = @typeInfo(_MapFn);
    const len = info.Fn.params.len;

    if (len != 1) {
        @compileError("The map function must has only one parameter!");
    }

    return info.Fn.params[0].type.?;
}

pub fn MapFnRetType(comptime MapFn: type) type {
    const _MapFn = if (@typeInfo(MapFn) == .Pointer) std.meta.Child(MapFn) else MapFn;
    const R = @typeInfo(_MapFn).Fn.return_type.?;

    if (R == noreturn) {
        @compileError("The return type of map function must not be noreturn!");
    }
    return R;
}

pub fn MapLamInType(comptime MapLam: type) type {
    const info = @typeInfo(MapLam);
    if (info != .Struct) {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(MapLam.call));
    const len = mapFnInfo.Fn.params.len;

    if (len != 2) {
        @compileError("The call function of map lambda must have only two parameters!");
    }
    if (mapFnInfo.Fn.params[0].type.? != *MapLam and mapFnInfo.Fn.params[0].type.? != *const MapLam) {
        @compileError("The first parameter of call function must be a pointer of MapLam!");
    }

    return mapFnInfo.Fn.params[1].type.?;
}

pub fn MapLamRetType(comptime MapLam: type) type {
    const info = @typeInfo(MapLam);
    if (info != .Struct) {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(MapLam.call));
    const R = mapFnInfo.Fn.return_type.?;

    if (R == noreturn) {
        @compileError("The return type of call function must not be noreturn!");
    }
    return R;
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
fn identity(a: anytype) @TypeOf(a) {
    return a;
}

pub fn getIdentityFn(comptime A: type) *const fn (A) A {
    return &struct {
        fn id(a: A) A {
            return a;
        }
    }.id;
}

pub fn IdentityLamType(comptime T: type) type {
    return struct {
        lam_ctx: void = {},

        const Self = @This();
        fn call(self: Self, val: T) T {
            _ = self;
            return val;
        }
    };
}

pub fn getIdentityLam(comptime A: type) IdentityLamType(A) {
    return IdentityLamType(A){};
}

pub const AnyFnType = fn (usize) usize;
pub const AnyFnPtr = *const AnyFnType;

pub fn AnyLamFromFn(
    comptime A: type,
    comptime B: type,
    comptime lam_fn: *const fn (*anyopaque, A) B,
) type {
    return struct {
        lam_ctx: *anyopaque,
        const Self = @This();
        pub fn call(self: Self, a: A) B {
            return lam_fn(self.lam_ctx, a);
        }
    };
}

fn ComposedTwoFn(comptime A: type, comptime B: type, comptime C: type) type {
    return struct {
        first_fn: *const fn (A) B,
        second_fn: *const fn (B) C,
        const SelfComp = @This();
        fn call(selfComp: SelfComp, a: A) C {
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

        pub fn call(self: Self, a: TS[0]) TS[N - 1] {
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
        const Error = cfg.error_set;
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

        /// The parametr compfn1 is a ComposableFn
        pub fn compose(
            self: Self,
            compfn1: anytype,
        ) Error!ComposeType(@TypeOf(compfn1)) {
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
        ) Error!ComposableFn(cfg, N + 1, TS ++ [1]type{MapFnRetType(@TypeOf(map_fn))}) {
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

        pub fn clone(self: Self) Error!Self {
            if (N > 3) {
                return .{ .composed_many = .{
                    .fns_array = try self.composed_many.fns_array.clone(),
                } };
            }
            return self;
        }

        pub fn call(self: Self, a: A) B {
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

const ComposeCfg = struct {
    allocator: Allocator,
    error_set: type,
};

fn getDefaultComposeCfg(allocator: Allocator) ComposeCfg {
    return .{
        .allocator = allocator,
        .error_set = Allocator.Error,
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
    const cfg = comptime getDefaultComposeCfg(allocator);
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
        pub fn call(self: Self, a: A) C {
            return self.second_fn(self.first_fn(a));
        }
    };
}

fn composeTwoFn(map_fn1: anytype, map_fn2: anytype) ComposeTwoFn(map_fn1, map_fn2) {
    return .{ .first_fn = map_fn1, .second_fn = map_fn2 };
}

/// Check the type E whether it is a ErrorUnion, if true then return a under
/// type of ErrorUnion, else just return type E.
pub fn isErrorUnionOrVal(comptime E: type) struct { bool, type } {
    const info = @typeInfo(E);
    const has_error = if (info == .ErrorUnion) true else false;
    const A = if (has_error) info.ErrorUnion.payload else E;
    return .{ has_error, A };
}

pub fn castInplaceValue(comptime T: type, val: anytype) T {
    const info = @typeInfo(@TypeOf(val));
    switch (info) {
        .Optional => {
            const v = val orelse return null;
            return castInplaceValue(std.meta.Child(T), v);
        },
        .Struct => {
            if (info.Struct.layout == .auto) {
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
    if (info_a == .Fn) {
        return getDefaultFn(T);
    } else if (info_a == .Pointer and @typeInfo(std.meta.Child(T)) == .Fn) {
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

/// A empty free function, do nothing
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

/// Clone a constructed data or referance a pointer
pub fn copyOrCloneOrRef(a: anytype) !@TypeOf(a) {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .Struct, .Enum, .Union, .Opaque => {
            if (@hasDecl(T, "clone")) {
                return a.clone();
            }
        },
        .Pointer => {
            const Child = info.Pointer.child;
            const child_info = @typeInfo(Child);
            if (info.Pointer.size != .One) {
                @compileError("deinitOrUnref only for pointer that has only one element!");
            }
            switch (child_info) {
                .Struct, .Enum, .Union, .Opaque => {
                    if (@hasDecl(T, "strongRef")) {
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

/// Deinit a constructed data or unreferance a pointer
pub fn deinitOrUnref(a: anytype) void {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .Struct, .Enum, .Union, .Opaque => {
            if (@hasDecl(T, "deinit")) {
                a.deinit();
            }
        },
        .Pointer => {
            const Child = info.Pointer.child;
            const child_info = @typeInfo(Child);
            if (info.Pointer.size != .One) {
                @compileError("deinitOrUnref only for pointer that has only one element!");
            }
            switch (child_info) {
                .Struct, .Enum, .Union, .Opaque => {
                    if (@hasDecl(T, "strongUnref")) {
                        _ = a.strongUnref();
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}
