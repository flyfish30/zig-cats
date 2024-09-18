//! Definition pure Maybe struct, these is a instance of
//! Functor|Applicative|Monad typeclass. The PureMaybe is pure mode Maybe.

const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const testu = @import("../test_utils.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
const Maybe = base.Maybe;

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const FMapMode = base.FMapMode;
const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

pub const MaybeMonadImpl = struct {
    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = Maybe;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime MaybeA: type) type {
        return std.meta.Child(MaybeA);
    }
    pub const FxTypes = FunctorFxTypes(F);
    pub const FaType = FxTypes.FaType;
    pub const FbType = FxTypes.FbType;
    pub const FaLamType = FxTypes.FaLamType;
    pub const FbLamType = FxTypes.FbLamType;

    pub fn deinitFa(
        fa: anytype, // Maybe(A)
        comptime free_fn: fn (BaseType(@TypeOf(fa))) void,
    ) void {
        if (fa) |a| {
            free_fn(a);
        }
    }

    pub fn fmap(
        comptime K: MapFnKind,
        map_fn: anytype,
        fa: FaType(K, @TypeOf(map_fn)),
    ) FbType(@TypeOf(map_fn)) {
        if (comptime isMapRef(K)) {
            if (fa.* != null) {
                return map_fn(&(fa.*.?));
            }
        } else {
            if (fa) |a| {
                return map_fn(a);
            }
        }

        return null;
    }

    pub fn fmapLam(
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        if (comptime isMapRef(K)) {
            if (fa.* != null) {
                return map_lam.call(@constCast(&(fa.*.?)));
            }
        } else {
            if (fa) |a| {
                return map_lam.call(a);
            }
        }

        return null;
    }

    pub fn pure(a: anytype) F(@TypeOf(a)) {
        return a;
    }

    pub fn fapply(
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        ff: F(*const fn (A) B),
        fa: F(A),
    ) F(B) {
        if (ff) |f| {
            if (fa) |a| {
                return f(a);
            }
        }
        return null;
    }

    pub fn fapplyLam(
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        flam: anytype, // a F(lambda) that present F(*const fn (A) B),
        fa: F(A),
    ) F(B) {
        if (flam) |lam| {
            if (fa) |a| {
                return lam.call(a);
            }
        }
        return null;
    }

    pub fn bind(
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (A) F(B),
    ) F(B) {
        if (ma) |a| {
            return k(a);
        }
        return null;
    }

    pub fn bindLam(
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        klam: anytype, // a lambda with function *const fn(Self, A) F(B)
    ) F(B) {
        if (ma) |a| {
            return klam.call(a);
        }
        return null;
    }
};

// These functions are used for unit test
const add10 = testu.add10;
const add_pi_f32 = testu.add_pi_f32;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const add_e_f64 = testu.add_e_f64;
const mul_e_f64 = testu.mul_e_f64;

test "pure Maybe Functor fmap" {
    const MaybeFunctor = Functor(MaybeMonadImpl);

    var maybe_a: ?u32 = null;
    maybe_a = MaybeFunctor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(null, maybe_a);

    maybe_a = 32;
    maybe_a = MaybeFunctor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(42, maybe_a);

    maybe_a = null;
    var maybe_b = MaybeFunctor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 32;
    maybe_b = MaybeFunctor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(32 + 3.14, maybe_b);
}

test "pure Maybe Applicative pure and fapply" {
    const MaybeApplicative = Applicative(MaybeMonadImpl);

    const add24_from_f64 = &struct {
        fn f(x: f64) u32 {
            return @intFromFloat(@floor(x) + 24);
        }
    }.f;
    const fapply_fn = MaybeApplicative.pure(add24_from_f64);

    var maybe_a: ?f64 = null;
    var maybe_b = MaybeApplicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 1.68;
    maybe_b = MaybeApplicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(1 + 24, maybe_b);

    maybe_b = MaybeApplicative.fapply(u32, u32, null, maybe_b);
    try testing.expectEqual(null, maybe_b);
}

test "pure Maybe Monad bind" {
    const MaybeMonad = Monad(MaybeMonadImpl);

    const cont_fn = &struct {
        fn k(x: f64) MaybeMonad.MbType(u32) {
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.k;

    const cont_lam = struct {
        a: u32 = 7,
        const Self = @This();
        fn call(self: Self, x: f64) MaybeMonad.MbType(u32) {
            if (x == 3.14) {
                return null;
            } else {
                return @as(u32, @intFromFloat(@floor(x * 4.0))) + self.a;
            }
        }
    }{};

    var maybe_a: ?f64 = null;
    var maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(32, maybe_b);

    maybe_a = null;
    maybe_b = MaybeMonad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = MaybeMonad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = MaybeMonad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(39, maybe_b);
}
