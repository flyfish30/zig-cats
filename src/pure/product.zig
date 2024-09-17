const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");

const testing = std.testing;
const assert = std.debug.assert;
const TCtor = base.TCtor;

const MapFnKind = base.MapFnKind;

const Functor = functor.Functor;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;

/// Get a Product Type constructor from two Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn ProductFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Producted(comptime A: type) type {
            return struct { F(A), G(A) };
        }
    }.Producted;
}

/// Get tuple of left and right type of product
pub fn getProductTypeTuple(comptime P: type) struct { type, type } {
    const info = @typeInfo(P);
    comptime assert(info == .Struct and info.Struct.is_tuple == true);
    comptime assert(info.Struct.fields.len == 2);

    const l_type = info.Struct.fields[0].type;
    const r_type = info.Struct.fields[1].type;
    return .{ l_type, r_type };
}

pub fn ProductFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        const FunctorF = Functor(ImplF);
        const FunctorG = Functor(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = ProductFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            const l_type, const r_type = getProductTypeTuple(FGA);
            comptime assert(ImplF.BaseType(l_type) == ImplG.BaseType(r_type));
            return ImplF.BaseType(l_type);
        }

        pub const FxTypes = FunctorFxTypes(F);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            ImplF.deinitFa(fga[0], free_fn);
            ImplG.deinitFa(fga[1], free_fn);
        }

        pub fn fmap(
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return .{
                ImplF.fmap(K, map_fn, fga[0]),
                ImplG.fmap(K, map_fn, fga[1]),
            };
        }

        pub fn fmapLam(
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return .{
                ImplF.fmapLam(K, map_lam, fga[0]),
                ImplG.fmapLam(K, map_lam, fga[1]),
            };
        }
    };
}

pub fn ProductApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        pub const SupImpl = ProductFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
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
            return .{
                ImplF.pure(a),
                ImplG.pure(a),
            };
        }

        pub fn fapply(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) F(B) {
            return .{
                ImplF.fapply(A, B, fgf[0], fga[0]),
                ImplG.fapply(A, B, fgf[1], fga[1]),
            };
        }

        pub fn fapplyLam(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) F(B) {
            return .{
                ImplF.fapplyLam(A, B, fgf[0], fga[0]),
                ImplG.fapplyLam(A, B, fgf[1], fga[1]),
            };
        }
    };
}

/// Get a Product Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ProductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const ImplFG = ProductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(ImplFG);
}

/// Get a Product Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ProductApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const ImplFG = ProductApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
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
const ArrayMonadImpl = monad.ArrayMonadImpl;
const MaybeMonadImpl = maybe.MaybeMonadImpl;

const Maybe = base.Maybe;
const ARRAY_LEN = 4;
const Array = base.Array;
const ArrayF = Array(ARRAY_LEN);

test "Compose Functor fmap" {
    // test (ArrayF, Maybe) product functor
    const ArrayAndMaybe = ProductFG(ArrayF, Maybe);
    const ArrayFunctor = Functor(ArrayMonadImpl(ARRAY_LEN));
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const ArrayAndMaybeFunctor = ProductFunctor(ArrayFunctor, MaybeFunctor);

    const array_a = ArrayF(u32){ 1, 2, 3, 4 };
    var arr_maybe_a = ArrayAndMaybe(u32){ array_a, 42 };
    arr_maybe_a = ArrayAndMaybeFunctor.fmap(.InplaceMap, add10, arr_maybe_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 11, 12, 13, 14 }, &arr_maybe_a[0]);
    try testing.expectEqual(52, arr_maybe_a[1]);

    arr_maybe_a[1] = null; // (array_a, null)
    arr_maybe_a = ArrayAndMaybeFunctor.fmap(.InplaceMap, mul3, arr_maybe_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 33, 36, 39, 42 }, &arr_maybe_a[0]);
    try testing.expectEqual(null, arr_maybe_a[1]);

    var arr_maybe_b = ArrayAndMaybeFunctor.fmap(.NewValMap, add4, arr_maybe_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 37, 40, 43, 46 }, &arr_maybe_b[0]);
    try testing.expectEqual(null, arr_maybe_b[1]);

    arr_maybe_b[1] = 18; // (array_a, 18)
    const arr_maybe_c = ArrayAndMaybeFunctor.fmap(.NewValMap, mul2, arr_maybe_b);
    try testing.expectEqualSlices(u32, &[_]u32{ 74, 80, 86, 92 }, &arr_maybe_c[0]);
    try testing.expectEqual(36, arr_maybe_c[1]);
}

test "Compose Applicative pure and fapply" {
    // const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;

    // test (ArrayF, Maybe) product applicative
    const ArrayAndMaybe = ProductFG(ArrayF, Maybe);
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);
    const ArrayAndMaybeApplicative = ProductApplicative(ArrayApplicative, MaybeApplicative);

    const arr_maybe_pured = ArrayAndMaybeApplicative.pure(@as(u32, 7));
    try testing.expectEqualSlices(u32, &[_]u32{ 7, 7, 7, 7 }, &arr_maybe_pured[0]);
    try testing.expectEqual(7, arr_maybe_pured[1]);

    const array_a = ArrayF(u32){ 1, 2, 3, 4 };
    var arr_maybe_a = ArrayAndMaybe(u32){ array_a, 42 };

    const array_fns = ArrayF(IntToFloatFn){ add_pi_f64, mul_pi_f64, add_e_f64, mul_e_f64 };
    var arr_maybe_fns = ArrayAndMaybe(IntToFloatFn){ array_fns, add_pi_f64 };
    const arr_maybe_b = ArrayAndMaybeApplicative.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    for (&[_]f64{ 4.14, 6.28, 5.71828, 10.87312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_b[0][i], std.math.floatEps(f64));
    }
    try testing.expectEqual(45.14, arr_maybe_b[1]);

    arr_maybe_a[1] = null; // (array_a, null)
    const arr_maybe_c = ArrayAndMaybeApplicative.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    for (&[_]f64{ 4.14, 6.28, 5.71828, 10.87312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_c[0][i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, arr_maybe_c[1]);

    arr_maybe_fns[1] = null; // (array_fns, null)
    arr_maybe_a[1] = 23; // (array_a, 23)
    const arr_maybe_d = ArrayAndMaybeApplicative.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    for (&[_]f64{ 4.14, 6.28, 5.71828, 10.87312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_d[0][i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, arr_maybe_d[1]);
}
