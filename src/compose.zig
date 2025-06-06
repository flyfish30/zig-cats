const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");
const listm = @import("array_list_monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
const TCtor = base.TCtor;
var maybe_error = maybe.maybe_error;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const ApplyFnInType = base.ApplyFnInType;
const ApplyFnRetType = base.ApplyFnRetType;
const ApplyLamInType = base.ApplyLamInType;
const ApplyLamRetType = base.ApplyLamRetType;

const MapFnKind = base.MapFnKind;
const FMapMode = base.FMapMode;

const Functor = functor.Functor;
const FunctorFromImpl = functor.FunctorFromImpl;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;
const ApplicativeFromImpl = applicative.ApplicativeFromImpl;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;

const getFreeNothing = base.getFreeNothing;

/// Compose two Type constructor to one Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn ComposeFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Composed(comptime A: type) type {
            return F(G(A));
        }
    }.Composed;
}

pub fn ComposeFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        instanceF: ImplF,
        instanceG: ImplG,

        const Self = @This();
        const FunctorF = FunctorFromImpl(ImplF);
        const FunctorG = FunctorFromImpl(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = ComposeFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            return ImplG.BaseType(ImplF.BaseType(FGA));
        }

        /// Error set of ComposeFunctorImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error: ?type = maybe_error.mappend(ImplF.Error, ImplG.Error);

        const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // F(G(A))
            comptime free_fn: *const fn (BaseType(@TypeOf(fga))) void,
        ) void {
            const free_ga_fn = struct {
                fn freeGa(ga: ImplF.BaseType(@TypeOf(fga))) void {
                    ImplG.deinitFa(ga, free_fn);
                }
            }.freeGa;
            ImplF.deinitFa(fga, free_ga_fn);
        }

        pub fn fmap(
            self: *const Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            const MapFn = @TypeOf(map_fn);
            const map_lam = struct {
                map_fn: *const fn (a: MapFnInType(MapFn)) MapFnRetType(MapFn),

                const MapSelf = @This();
                pub fn call(map_self: *const MapSelf, a: MapFnInType(MapFn)) MapFnRetType(MapFn) {
                    return map_self.map_fn(a);
                }
            }{ .map_fn = &map_fn };

            return fmapLam(self, K, map_lam, fga);
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const MapLam = @TypeOf(map_lam);
            const map_inner = struct {
                inner_g: *const ImplG,
                map_lam: MapLam,

                const InnerSelf = @This();
                pub fn call(
                    inner_self: *const InnerSelf,
                    ga: FunctorG.FaLamType(K, MapLam),
                ) FunctorG.FbLamType(MapLam) {
                    return inner_self.inner_g.fmapLam(K, inner_self.map_lam, ga);
                }
            }{
                .inner_g = &self.instanceG,
                .map_lam = map_lam,
            };

            return self.instanceF.fmapLam(K, map_inner, fga);
        }
    };
}

pub fn ComposeApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        functor_sup: SupImpl,

        const Self = @This();
        pub const SupImpl = ComposeFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        pub const BaseType = SupImpl.BaseType;

        /// Error set of ComposeApplicativeImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error: ?type = SupImpl.Error;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub inline fn deinitFa(
            fga: anytype, // F(G(A))
            comptime free_fn: *const fn (BaseType(@TypeOf(fga))) void,
        ) void {
            return SupImpl.deinitFa(fga, free_fn);
        }

        pub fn fmap(
            self: *const Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return self.functor_sup.fmap(K, map_fn, fga);
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return self.functor_sup.fmapLam(K, map_lam, fga);
        }

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            return self.functor_sup.instanceF.pure(self.functor_sup.instanceG.pure(a));
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // fgf: F(*const fn (A) B),
            fgf: anytype,
            fga: F(ApplyFnInType(Self, @TypeOf(fgf))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(fgf))) {
            const A = ApplyFnInType(Self, @TypeOf(fgf));
            const B = ApplyFnRetType(Self, @TypeOf(fgf));
            return fapplyGeneric(self, .NormalMap, A, B, fgf, fga);
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            fglam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fga: F(ApplyLamInType(Self, @TypeOf(fglam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(fglam))) {
            const A = ApplyLamInType(Self, @TypeOf(fglam));
            const B = ApplyLamRetType(Self, @TypeOf(fglam));
            return fapplyGeneric(self, .LambdaMap, A, B, fglam, fga);
        }

        fn fapplyGeneric(
            self: *const Self,
            comptime M: FMapMode,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            // inner_fapply: G (a -> b) -> G a -> G b
            // outer_fapply: F (G a -> G b) -> F (G a) -> F (G b)
            // fmap inner_fapply: F (G (a -> b)) -> F (G a -> G b)
            // outer_fapply (fmap inner_fapply): F (G (a -> b)) -> F (G a) -> F (G b)
            // fapply = outer_fapply (fmap inner_fapply)

            // A function with type *const fn (A) B
            // or a lambda that has function *const fn (LamSelf, A) B
            const FnOrLambdaType = BaseType(@TypeOf(fgf));

            const inner_fapply = struct {
                inner_instance: *const ImplG,

                const InnerSelf = @This();
                const ApplyLam = struct {
                    apply_instanceG: *const ImplG,
                    apply_gf_p: *ImplG.F(FnOrLambdaType),

                    const ApplySelf = @This();
                    // applyFn: G a -> G b
                    pub fn call(applySelf: *const ApplySelf, ga: ImplG.F(A)) ImplG.AFbType(B) {
                        if (M == .NormalMap) {
                            return applySelf.apply_instanceG.fapply(applySelf.apply_gf_p.*, ga);
                        } else {
                            return applySelf.apply_instanceG.fapplyLam(applySelf.apply_gf_p.*, ga);
                        }
                    }
                };

                // mapFn \gf_p -> apply_lam : G (a -> b) -> G a -> G b
                pub fn call(
                    inner_self: *const InnerSelf,
                    gf_p: *ImplG.F(FnOrLambdaType),
                ) ApplyLam {
                    // apply lambda \ga -> fapply instanceG gf ga : G a -> G b
                    return ApplyLam{
                        .apply_instanceG = inner_self.inner_instance,
                        .apply_gf_p = gf_p,
                    };
                }
            }{ .inner_instance = &self.functor_sup.instanceG };

            const flam = if (ImplF.Error == null)
                self.functor_sup.instanceF.fmapLam(.NewValMapRef, inner_fapply, @constCast(&fgf))
            else
                try self.functor_sup.instanceF.fmapLam(.NewValMapRef, inner_fapply, @constCast(&fgf));
            defer ImplF.deinitFa(flam, getFreeNothing(@TypeOf(inner_fapply).ApplyLam));
            return self.functor_sup.instanceF.fapplyLam(flam, fga);
        }
    };
}

/// Compose two Functor to one Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ComposeFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const FGImpl = ComposeFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return FunctorFromImpl(FGImpl);
}

/// Compose two Applicative Functor to one Applicative Functor, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ComposeApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const FGImpl = ComposeApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
    return ApplicativeFromImpl(FGImpl);
}

// These functions are defined for unit test
const add4 = testu.add4;
const add10 = testu.add10;
const mul2 = testu.mul2;
const mul3 = testu.mul3;
const add_pi_f32 = testu.add_pi_f32;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const add_e_f64 = testu.add_e_f64;
const mul_e_f64 = testu.mul_e_f64;

const monad = @import("monad.zig");
const ArrayListMonadImpl = listm.ArrayListMonadImpl;
const MaybeMonadImpl = maybe.MaybeMonadImpl;

const Maybe = base.Maybe;
const ARRAY_LEN = 4;
const Array = base.Array;
const ArrayF = Array(ARRAY_LEN);
const ArrayList = std.ArrayList;

// Deinit the array3 with type ArrayList(Maybe(ArrayList(A))
fn array3Deinit(array3: anytype) void {
    for (array3.items) |item| {
        if (item) |arr| {
            arr.deinit();
        }
    }
    array3.deinit();
}

// Create a array3 with type ArrayList(Maybe(ArrayList(A)) from slices
fn array3FromSlices(
    comptime T: type,
    comptime Len: usize,
    allocator: Allocator,
    slices: []?[Len]T,
) !ArrayList(Maybe(ArrayList(T))) {
    var array3 = ArrayList(Maybe(ArrayList(T))).init(allocator);
    for (slices) |as| {
        const array = if (as) |_as| ints_val: {
            var array_tmp = ArrayList(T).init(allocator);
            try array_tmp.appendSlice(&_as);
            break :ints_val array_tmp;
        } else null;
        try array3.append(array);
    }
    return array3;
}

// Convert the array3 with type ArrayList(Maybe(ArrayList(A)) to slices
fn array3ToSlices(
    comptime T: type,
    comptime Len: usize,
    allocator: Allocator,
    array3: ArrayList(Maybe(ArrayList(T))),
) ![]?[Len]T {
    var slices: []?[Len]T = try allocator.alloc(?[Len]T, array3.items.len);
    for (array3.items, 0..) |item, i| {
        if (item) |arr| {
            for (arr.items, 0..) |a, j| {
                slices[i].?[j] = a;
            }
        } else {
            slices[i] = null;
        }
    }
    return slices;
}

test "Compose Functor fmap" {
    // test (ArrayList ∘ Maybe) composed functor
    const allocator = testing.allocator;
    const ArrayListFunctor = Functor(ArrayList);
    const MaybeFunctor = Functor(Maybe);
    const ArrayMaybeFunctor = ComposeFunctor(ArrayListFunctor, MaybeFunctor);
    const array_maybe = ArrayMaybeFunctor.InstanceImpl{
        .instanceF = .{ .allocator = allocator },
        .instanceG = .{},
    };

    var array_a = ArrayList(Maybe(u32)).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]?u32{ null, 1, 2, null });
    array_a = try array_maybe.fmap(.InplaceMap, add10, array_a);
    try testing.expectEqualSlices(?u32, &[_]?u32{ null, 11, 12, null }, array_a.items);

    const array_f32 = try array_maybe.fmap(.InplaceMap, add_pi_f32, array_a);
    // Don't free items of array_f32, because inplace map ensure the array_f32
    // and array_a share the same items slice.
    // defer array_f32.deinit();
    try testing.expectEqualSlices(?f32, &[_]?f32{ null, 14.14, 15.14, null }, array_f32.items);

    array_a.clearRetainingCapacity();
    try array_a.appendSlice(&[_]?u32{ null, 11, 12, null });
    const array_f64 = try array_maybe.fmap(.NewValMap, mul_pi_f64, array_a);
    defer array_f64.deinit();
    for (&[_]?f64{ null, 34.54, 37.68, null }, 0..) |a, i| {
        if (a) |_a| {
            try testing.expectApproxEqRel(_a, array_f64.items[i].?, std.math.floatEps(f64));
        } else {
            try testing.expectEqual(a, array_f64.items[i]);
        }
    }

    // test ((ArrayList ∘ Maybe) ∘ ArrayList) composed functor
    const ArrayMaybeArrayFunctor = ComposeFunctor(ArrayMaybeFunctor, ArrayListFunctor);
    const array_maybe_array = ArrayMaybeArrayFunctor.InstanceImpl{
        .instanceF = array_maybe,
        .instanceG = ArrayListFunctor.InstanceImpl{ .allocator = allocator },
    };

    const array3_ints_slice = &ArrayF(Maybe(ArrayF(u32))){
        null,
        [_]u32{ 10, 11, 12, 13 },
        [_]u32{ 15, 17, 21, 23 },
        null,
    };
    const array3_a = try array3FromSlices(u32, ARRAY_LEN, allocator, @constCast(array3_ints_slice));
    defer array3Deinit(array3_a);

    const array3_f32 = try array_maybe_array.fmap(.NewValMap, add_pi_f32, array3_a);
    defer array3Deinit(array3_f32);
    try testing.expectEqual(4, array3_f32.items.len);
    try testing.expectEqual(null, array3_f32.items[0]);
    for (&[_]f32{ 13.14, 14.14, 15.14, 16.14 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f32.items[1].?.items[i], std.math.floatEps(f32));
    }
    for (&[_]f32{ 18.14, 20.14, 24.14, 26.14 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f32.items[2].?.items[i], std.math.floatEps(f32));
    }
    try testing.expectEqual(null, array3_f32.items[3]);

    const array3_f64 = try array_maybe_array.fmap(.NewValMap, mul_pi_f64, array3_a);
    defer array3Deinit(array3_f64);
    try testing.expectEqual(4, array3_f64.items.len);
    try testing.expectEqual(null, array3_f64.items[0]);
    for (&[_]f64{ 31.4, 34.54, 37.68, 40.82 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f64.items[1].?.items[i], std.math.floatEps(f64));
    }
    for (&[_]f64{ 47.1, 53.38, 65.94, 72.22 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f64.items[2].?.items[i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, array3_f64.items[3]);
}

// Pretty print the array3 with type ArrayList(Maybe(ArrayList(A))
fn array3PrettyPrint(array3: anytype) void {
    std.debug.print("{{ \n", .{});
    var j: u32 = 0;
    for (array3.items) |item| {
        if (item) |arr| {
            std.debug.print(" {{ ", .{});
            for (arr.items) |a| {
                std.debug.print("{any},", .{a});
            }
            std.debug.print(" }},", .{});
        } else {
            std.debug.print(" {any},", .{item});
        }

        j += 1;
        if (j == 16) {
            j = 0;
            std.debug.print("\n", .{});
        }
    }
    std.debug.print("}}\n", .{});
}

test "Compose Applicative pure and fapply" {
    const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;
    const allocator = testing.allocator;

    // test (ArrayList ∘ Maybe) composed applicative
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const ArrayMaybeApplicative = ComposeApplicative(ArrayListApplicative, MaybeApplicative);
    const array_maybe = ArrayMaybeApplicative.InstanceImpl{ .functor_sup = .{
        .instanceF = .{ .allocator = allocator },
        .instanceG = .{},
    } };

    const array_pured = try array_maybe.pure(@as(u32, 42));
    defer array_pured.deinit();
    try testing.expectEqualSlices(?u32, &[_]?u32{42}, array_pured.items);

    var array_a = ArrayList(Maybe(u32)).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]Maybe(u32){ null, 20, 30, 40 });
    var array_fns = ArrayList(Maybe(IntToFloatFn)).init(allocator);
    defer array_fns.deinit();
    try array_fns.appendSlice(&[_]Maybe(IntToFloatFn){ add_pi_f64, mul_pi_f64, null, mul_e_f64 });

    const array_f64 = try array_maybe.fapply(array_fns, array_a);
    defer array_f64.deinit();
    try testing.expectEqual(16, array_f64.items.len);
    for (&[_]?f64{
        // 0..3
        null, 23.14,   33.14,   43.14,
        // 4..7
        null, 62.8,    94.2,    125.6,
        // 8..11
        null, null,    null,    null,
        // 12..15
        null, 54.3656, 81.5484, 108.7312,
    }, 0..) |a, i| {
        if (a) |_a| {
            try testing.expectApproxEqRel(_a, array_f64.items[i].?, std.math.floatEps(f64));
        } else {
            try testing.expectEqual(a, array_f64.items[i]);
        }
    }

    // test ((ArrayList ∘ Maybe) ∘ ArrayList) composed applicative
    const ArrayMaybeArrayApplicative = ComposeApplicative(ArrayMaybeApplicative, ArrayListApplicative);
    const array_maybe_array = ArrayMaybeArrayApplicative.InstanceImpl{ .functor_sup = .{
        .instanceF = array_maybe,
        .instanceG = ArrayListApplicative.InstanceImpl{ .allocator = allocator },
    } };

    const array3_pured = try array_maybe_array.pure(@as(u32, 42));
    defer array3Deinit(array3_pured);
    try testing.expectEqual(1, array3_pured.items.len);
    try testing.expectEqualSlices(u32, &[_]u32{42}, array3_pured.items[0].?.items);

    const array3_ints_slice = &ArrayF(Maybe(ArrayF(u32))){
        null,
        [_]u32{ 1, 2, 3, 4 },
        [_]u32{ 5, 7, 11, 13 },
        null,
    };
    const array3_a = try array3FromSlices(u32, ARRAY_LEN, allocator, @constCast(array3_ints_slice));
    defer array3Deinit(array3_a);

    const array3_fns_slice = &ArrayF(Maybe(ArrayF(IntToIntFn))){
        null,
        [_]IntToIntFn{ add4, add10, mul2, mul3 },
        [_]IntToIntFn{ add10, mul2, mul3, add4 },
        null,
    };
    const array3_fns = try array3FromSlices(IntToIntFn, ARRAY_LEN, allocator, @constCast(array3_fns_slice));
    defer array3Deinit(array3_fns);

    const array3_b = try array_maybe_array.fapply(array3_fns, array3_a);
    defer array3Deinit(array3_b);
    // std.debug.print("array3_b: ", .{});
    // array3PrettyPrint(array3_b);
    const array3_b_slices = try array3ToSlices(u32, 16, allocator, array3_b);
    defer allocator.free(array3_b_slices);
    try testing.expectEqualSlices(?[16]u32, &[_]?[16]u32{
        // 0..3
        null, null,                                                          null,                                                                    null,
        // 4..7
        null, [_]u32{ 5, 6, 7, 8, 11, 12, 13, 14, 2, 4, 6, 8, 3, 6, 9, 12 }, [_]u32{ 9, 11, 15, 17, 15, 17, 21, 23, 10, 14, 22, 26, 15, 21, 33, 39 }, null,
        // 8..11
        null, [_]u32{ 11, 12, 13, 14, 2, 4, 6, 8, 3, 6, 9, 12, 5, 6, 7, 8 }, [_]u32{ 15, 17, 21, 23, 10, 14, 22, 26, 15, 21, 33, 39, 9, 11, 15, 17 }, null,
        // 12..15
        null, null,                                                          null,                                                                    null,
    }, array3_b_slices);
}
