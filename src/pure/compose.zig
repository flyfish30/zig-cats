const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_monad.zig");

const testing = std.testing;
const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const MapFnKind = base.MapFnKind;
const FMapMode = base.FMapMode;

const Functor = functor.Functor;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;

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
        const FunctorF = Functor(ImplF);
        const FunctorG = Functor(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = ComposeFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            return ImplG.BaseType(ImplF.BaseType(FGA));
        }

        pub const FxTypes = FunctorFxTypes(F);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // F(G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            const free_ga_fn = struct {
                fn freeGa(ga: ImplF.BaseType(@TypeOf(fga))) void {
                    ImplG.deinitFa(ga, free_fn);
                }
            }.freeGa;
            ImplF.deinitFa(fga, free_ga_fn);
        }

        pub fn fmap(
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            const MapFn = @TypeOf(map_fn);
            const map_lam = struct {
                map_fn: *const fn (a: MapFnInType(MapFn)) MapFnRetType(MapFn),

                const MapSelf = @This();
                pub fn call(mapSelf: *const MapSelf, a: MapFnInType(MapFn)) MapFnRetType(MapFn) {
                    return mapSelf.map_fn(a);
                }
            }{ .map_fn = &map_fn };

            return fmapLam(K, map_lam, fga);
        }

        pub fn fmapLam(
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const MapLam = @TypeOf(map_lam);
            const map_inner = struct {
                map_lam: MapLam,

                const InnerSelf = @This();
                pub fn call(
                    inner_self: *const InnerSelf,
                    ga: FunctorG.FaLamType(K, MapLam),
                ) FunctorG.FbLamType(MapLam) {
                    return ImplG.fmapLam(K, inner_self.map_lam, ga);
                }
            }{
                .map_lam = map_lam,
            };

            return ImplF.fmapLam(K, map_inner, fga);
        }
    };
}

pub fn ComposeApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        pub const SupImpl = ComposeFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        pub const BaseType = SupImpl.BaseType;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        pub const deinitFa = SupImpl.deinitFa;
        pub const fmap = SupImpl.fmap;
        pub const fmapLam = SupImpl.fmapLam;

        pub fn pure(a: anytype) F(@TypeOf(a)) {
            return ImplF.pure(ImplG.pure(a));
        }

        pub fn fapply(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) F(B) {
            return fapplyGeneric(.NormalMap, A, B, fgf, fga);
        }

        pub fn fapplyLam(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) F(B) {
            return fapplyGeneric(.LambdaMap, A, B, fgf, fga);
        }

        fn fapplyGeneric(
            comptime M: FMapMode,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) F(B) {
            // inner_fapply: G (a -> b) -> G a -> G b
            // outer_fapply: F (G a -> G b) -> F (G a) -> F (G b)
            // fmap inner_fapply: F (G (a -> b)) -> F (G a -> G b)
            // outer_fapply (fmap inner_fapply): F (G (a -> b)) -> F (G a) -> F (G b)
            // fapply = outer_fapply (fmap inner_fapply)

            // A function with type *const fn (A) B
            // or a lambda that has function *const fn (LamSelf, A) B
            const FnOrLambdaType = BaseType(@TypeOf(fgf));

            const InnerApply = struct {
                pub const ApplyLam = struct {
                    apply_gf_p: *ImplG.F(FnOrLambdaType),

                    const ApplySelf = @This();
                    // applyFn: G a -> G b
                    pub fn call(applySelf: *const ApplySelf, ga: ImplG.F(A)) ImplG.F(B) {
                        if (M == .NormalMap) {
                            return ImplG.fapply(A, B, applySelf.apply_gf_p.*, ga);
                        } else {
                            return ImplG.fapplyLam(A, B, applySelf.apply_gf_p.*, ga);
                        }
                    }
                };

                // mapFn \gf_p -> apply_lam : G (a -> b) -> G a -> G b
                fn fapply(
                    gf_p: *ImplG.F(FnOrLambdaType),
                ) ApplyLam {
                    const apply_lam = .{
                        .apply_gf_p = gf_p,
                    };
                    // apply lambda \ga -> fapply instanceG gf ga : G a -> G b
                    return apply_lam;
                }
            };

            const free_fn = struct {
                fn free_fn(lam: InnerApply.ApplyLam) void {
                    _ = lam;
                }
            }.free_fn;

            const inner_fapply = InnerApply.fapply;
            const flam = ImplF.fmap(.NewValMapRef, inner_fapply, @constCast(&fgf));
            defer ImplF.deinitFa(flam, free_fn);
            return ImplF.fapplyLam(
                ImplG.F(A),
                ImplG.F(B),
                flam,
                fga,
            );
        }
    };
}

/// Compose two Functor to one Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ComposeFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const ImplFG = ComposeFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(ImplFG);
}

/// Compose two Applicative Functor to one Applicative Functor, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ComposeApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const ImplFG = ComposeApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
    return Applicative(ImplFG);
}

// These functions are defined for unit test
const add4 = struct {
    fn f(a: u32) u32 {
        return a + 4;
    }
}.f;

const add10 = struct {
    fn f(a: u32) u32 {
        return a + 10;
    }
}.f;

const mul2 = struct {
    fn f(a: u32) u32 {
        return a * 2;
    }
}.f;

const mul3 = struct {
    fn f(a: u32) u32 {
        return a * 3;
    }
}.f;

const add_pi_f32 = struct {
    fn f(a: u32) f32 {
        return @as(f32, @floatFromInt(a)) + 3.14;
    }
}.f;

const add_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 3.14;
    }
}.f;

const mul_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 3.14;
    }
}.f;

const add_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 2.71828;
    }
}.f;

const mul_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 2.71828;
    }
}.f;

const monad = @import("monad.zig");
const ArrayMonadImpl = arraym.ArrayMonadImpl;
const MaybeMonadImpl = maybe.MaybeMonadImpl;

const Maybe = base.Maybe;
const Array = base.Array;
const ARRAY_LEN = 4;
const ArrayF = Array(ARRAY_LEN);

test "Compose Functor fmap" {
    // test (ArrayF ∘ Maybe) composed functor
    const ArrayFunctor = Functor(ArrayMonadImpl(ARRAY_LEN));
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const ArrayMaybeFunctor = ComposeFunctor(ArrayFunctor, MaybeFunctor);

    var array_a = ArrayF(Maybe(u32)){ null, 1, 2, null };
    array_a = ArrayMaybeFunctor.fmap(.InplaceMap, add10, array_a);
    try testing.expectEqualSlices(?u32, &[_]?u32{ null, 11, 12, null }, &array_a);

    const array_f32 = ArrayMaybeFunctor.fmap(.InplaceMap, add_pi_f32, array_a);
    try testing.expectEqualSlices(?f32, &[_]?f32{ null, 14.14, 15.14, null }, &array_f32);

    const array_f64 = ArrayMaybeFunctor.fmap(.NewValMap, mul_pi_f64, array_a);
    for (&[_]?f64{ null, 34.54, 37.68, null }, 0..) |a, i| {
        if (a) |_a| {
            try testing.expectApproxEqRel(_a, array_f64[i].?, std.math.floatEps(f64));
        } else {
            try testing.expectEqual(a, array_f64[i]);
        }
    }

    // test ((ArrayF ∘ Maybe) ∘ ArrayF) composed functor
    const ArrayMaybeArrayFunctor = ComposeFunctor(ArrayMaybeFunctor, ArrayFunctor);

    var array3_a = ArrayF(Maybe(ArrayF(u32))){
        null,
        [_]u32{ 0, 1, 2, 3 },
        [_]u32{ 5, 7, 11, 13 },
        null,
    };
    array3_a = ArrayMaybeArrayFunctor.fmap(.InplaceMap, add10, array3_a);
    try testing.expectEqualSlices(
        ?[4]u32,
        &[_]?[4]u32{ null, [_]u32{ 10, 11, 12, 13 }, [_]u32{ 15, 17, 21, 23 }, null },
        &array3_a,
    );

    const array3_f32 = ArrayMaybeArrayFunctor.fmap(.InplaceMap, add_pi_f32, array3_a);
    try testing.expectEqual(null, array3_f32[0]);
    for (&[_]f32{ 13.14, 14.14, 15.14, 16.14 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f32[1].?[i], std.math.floatEps(f32));
    }
    for (&[_]f32{ 18.14, 20.14, 24.14, 26.14 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f32[2].?[i], std.math.floatEps(f32));
    }
    try testing.expectEqual(null, array3_f32[3]);

    const array3_f64 = ArrayMaybeArrayFunctor.fmap(.NewValMap, mul_pi_f64, array3_a);
    try testing.expectEqual(null, array3_f64[0]);
    for (&[_]f64{ 31.4, 34.54, 37.68, 40.82 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f64[1].?[i], std.math.floatEps(f64));
    }
    for (&[_]f64{ 47.1, 53.38, 65.94, 72.22 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array3_f64[2].?[i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, array3_f64[3]);
}

test "Compose Applicative pure and fapply" {
    const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;

    // test (ArrayF ∘ Maybe) composed applicative
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);
    const ArrayMaybeApplicative = ComposeApplicative(ArrayApplicative, MaybeApplicative);

    const array_pured = ArrayMaybeApplicative.pure(@as(u32, 42));
    try testing.expectEqualSlices(?u32, &[_]?u32{ 42, 42, 42, 42 }, &array_pured);

    const array_a = ArrayF(Maybe(u32)){ null, 20, 30, 40 };
    const array_fns = ArrayF(Maybe(IntToFloatFn)){ add_pi_f64, mul_pi_f64, null, mul_e_f64 };
    const array_f64 = ArrayMaybeApplicative.fapply(u32, f64, array_fns, array_a);
    try testing.expectEqual(4, array_f64.len);
    for (&[_]?f64{ null, 62.8, null, 108.7312 }, 0..) |a, i| {
        if (a) |_a| {
            try testing.expectApproxEqRel(_a, array_f64[i].?, std.math.floatEps(f64));
        } else {
            try testing.expectEqual(a, array_f64[i]);
        }
    }

    // test ((ArrayF ∘ Maybe) ∘ ArrayF) composed applicative
    const ArrayMaybeArrayApplicative = ComposeApplicative(ArrayMaybeApplicative, ArrayApplicative);

    const array3_pured = ArrayMaybeArrayApplicative.pure(@as(u32, 42));
    for (0..4) |i| {
        try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 42, 42 }, &array3_pured[i].?);
    }

    const array3_a = ArrayF(Maybe(ArrayF(u32))){
        null,
        [_]u32{ 1, 2, 3, 4 },
        [_]u32{ 5, 7, 11, 13 },
        null,
    };
    var array3_fns = ArrayF(Maybe(ArrayF(IntToIntFn))){
        null,
        [_]IntToIntFn{ add4, add10, mul2, mul3 },
        [_]IntToIntFn{ add10, mul2, mul3, add4 },
        null,
    };
    var array3_b = ArrayMaybeArrayApplicative.fapply(u32, u32, array3_fns, array3_a);
    try testing.expectEqual(null, array3_b[0]);
    try testing.expectEqualSlices(u32, &[_]u32{ 5, 12, 6, 12 }, &array3_b[1].?);
    try testing.expectEqualSlices(u32, &[_]u32{ 15, 14, 33, 17 }, &array3_b[2].?);
    try testing.expectEqual(null, array3_b[3]);

    array3_fns = ArrayF(Maybe(ArrayF(IntToIntFn))){ null, [_]IntToIntFn{ add4, add10, mul2, mul3 }, null, [_]IntToIntFn{ add10, mul2, mul3, add4 } };
    array3_b = ArrayMaybeArrayApplicative.fapply(u32, u32, array3_fns, array3_a);
    try testing.expectEqual(null, array3_b[0]);
    try testing.expectEqualSlices(u32, &[_]u32{ 5, 12, 6, 12 }, &array3_b[1].?);
    try testing.expectEqual(null, array3_b[2]);
    try testing.expectEqual(null, array3_b[3]);
}
