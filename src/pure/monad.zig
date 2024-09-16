const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

const testing = std.testing;
const assert = std.debug.assert;

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
const castInplaceValue = base.castInplaceValue;

const Functor = functor.Functor;
const Applicative = applicative.Applicative;

const FunctorFxTypes = functor.FunctorFxTypes;

const Maybe = base.Maybe;
const Array = base.Array;

/// Monad typeclass like in Haskell, it inherit from Applicative Functor.
/// M is instance of Monad typeclass, such as Maybe, List
pub fn Monad(comptime MonadImpl: type) type {
    const M = MonadImpl.F;
    const has_sup_impl = @hasField(MonadImpl, "SupImpl");

    const InstanceType = struct {
        pub const InstanceImpl = MonadImpl;
        const ApplicativeSup = if (has_sup_impl)
            Applicative(InstanceImpl.SupImpl)
        else
            Applicative(InstanceImpl);

        pub const MbType = M;
        const BindType = @TypeOf(struct {
            fn bindFn(
                comptime A: type,
                comptime B: type,
                // monad function: (a -> M b), ma: M a
                ma: M(A),
                k: *const fn (*InstanceImpl, A) M(B),
            ) M(B) {
                _ = ma;
                _ = k;
            }
        }.bindFn);

        pub fn init() void {
            if (@TypeOf(InstanceImpl.bind) != BindType) {
                @compileError("Incorrect type of bind for Monad instance " ++ @typeName(InstanceImpl));
            }
        }

        pub const fmap = ApplicativeSup.fmap;
        pub const fmapLam = ApplicativeSup.fmapLam;
        pub const pure = ApplicativeSup.pure;
        pub const fapply = ApplicativeSup.fapply;
        pub const fapplyLam = ApplicativeSup.fapplyLam;
        pub const bind = InstanceImpl.bind;
    };

    InstanceType.init();
    return InstanceType;
}

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
};

// These functions are defined for unit test
const add10 = struct {
    fn f(a: u32) u32 {
        return a + 10;
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

test "Maybe Functor fmap" {
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

test "Maybe Applicative pure and fapply" {
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

test "Maybe Monad bind" {
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

    var maybe_a: ?f64 = null;
    var maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(32, maybe_b);
}

pub fn ArrayMonadImpl(comptime len: usize) type {
    return struct {
        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = Array(len);

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime ArrayA: type) type {
            return std.meta.Child(ArrayA);
        }

        pub const FxTypes = FunctorFxTypes(F);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        fn FaFnOrLamType(
            comptime K: MapFnKind,
            comptime M: FMapMode,
            comptime FnOrLam: type,
        ) type {
            if (M == .NormalMap) {
                return FaType(K, FnOrLam);
            } else {
                return FaLamType(K, FnOrLam);
            }
        }

        fn FbFnOrLamType(comptime M: FMapMode, comptime FnOrLam: type) type {
            if (M == .NormalMap) {
                return FbType(FnOrLam);
            } else {
                return FbLamType(FnOrLam);
            }
        }

        pub fn deinitFa(
            fa: anytype, // Array(len)(A)
            comptime free_fn: fn (BaseType(@TypeOf(fa))) void,
        ) void {
            for (fa) |item| {
                free_fn(item);
            }
        }

        /// If the returned array list of inplace map function assign to a new
        /// variable, then the array list in original variable should be reset
        /// to empty.
        pub fn fmap(
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return fmapGeneric(K, .NormalMap, map_fn, fa);
        }

        pub fn fmapLam(
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return fmapGeneric(K, .LambdaMap, map_lam, fa);
        }

        pub fn fmapGeneric(
            comptime K: MapFnKind,
            comptime M: FMapMode,
            fn_or_lam: anytype,
            fa: FaFnOrLamType(K, M, @TypeOf(fn_or_lam)),
        ) FbFnOrLamType(M, @TypeOf(fn_or_lam)) {
            comptime assert(fa.len == len);

            if (comptime isInplaceMap(K)) {
                const fb = mapInplace(K, M, fn_or_lam, fa);
                return fb;
            } else {
                const fb = mapNewValue(K, M, fn_or_lam, fa);
                return fb;
            }
        }

        fn mapInplace(
            comptime K: MapFnKind,
            comptime M: FMapMode,
            fn_or_lam: anytype,
            fa: FaFnOrLamType(K, M, @TypeOf(fn_or_lam)),
        ) FbFnOrLamType(M, @TypeOf(fn_or_lam)) {
            const A = if (M == .NormalMap)
                MapFnInType(@TypeOf(fn_or_lam))
            else
                MapLamInType(@TypeOf(fn_or_lam));

            const B = if (M == .NormalMap)
                MapFnRetType(@TypeOf(fn_or_lam))
            else
                MapLamRetType(@TypeOf(fn_or_lam));

            const ValA = if (comptime isMapRef(K)) std.meta.Child(A) else A;
            if (@bitSizeOf(ValA) != @bitSizeOf(B)) {
                @compileError("The bitsize of translated value is not equal origin value, failed to map it");
            }

            // const arr = if (comptime isMapRef(K)) fa.* else fa;
            var slice = @constCast(fa[0..len]);
            var i: usize = 0;
            while (i < slice.len) : (i += 1) {
                const a = if (comptime isMapRef(K)) &slice[i] else slice[i];
                if (M == .NormalMap) {
                    slice[i] = castInplaceValue(A, fn_or_lam(a));
                } else {
                    slice[i] = castInplaceValue(A, fn_or_lam.call(a));
                }
            }
            return @bitCast(slice.*);
        }

        fn mapNewValue(
            comptime K: MapFnKind,
            comptime M: FMapMode,
            fn_or_lam: anytype,
            fa: FaFnOrLamType(K, M, @TypeOf(fn_or_lam)),
        ) FbFnOrLamType(M, @TypeOf(fn_or_lam)) {
            const B = if (M == .NormalMap)
                MapFnRetType(@TypeOf(fn_or_lam))
            else
                MapLamRetType(@TypeOf(fn_or_lam));
            var fb: [len]B = undefined;

            var slice = fa[0..len];
            var i: usize = 0;
            while (i < len) : (i += 1) {
                const a = if (comptime isMapRef(K)) &slice[i] else slice[i];
                fb[i] = if (M == .NormalMap) fn_or_lam(a) else fn_or_lam.call(a);
            }
            return fb;
        }

        pub fn pure(a: anytype) F(@TypeOf(a)) {
            return [1]@TypeOf(a){a} ** len;
        }

        pub fn fapply(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            ff: F(*const fn (A) B),
            fa: F(A),
        ) F(B) {
            return fapplyGeneric(.NormalMap, A, B, ff, fa);
        }

        pub fn fapplyLam(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(A),
        ) F(B) {
            return fapplyGeneric(.LambdaMap, A, B, flam, fa);
        }

        fn fapplyGeneric(
            comptime M: FMapMode,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            ff: anytype,
            fa: F(A),
        ) F(B) {
            var fb: [len]B = undefined;

            var i: usize = 0;
            while (i < len) : (i += 1) {
                if (M == .NormalMap) {
                    fb[i] = ff[i](fa[i]);
                } else {
                    fb[i] = ff[i].call(fa[i]);
                }
            }
            return fb;
        }

        fn imap(
            comptime A: type,
            comptime B: type,
            map_lam: anytype,
            fa: F(A),
        ) F(B) {
            var fb: [len]B = undefined;
            var i: usize = 0;
            while (i < len) : (i += 1) {
                fb[i] = map_lam.call(i, fa[i]);
            }

            return fb;
        }

        pub fn bind(
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (A) F(B),
        ) F(B) {
            const imap_lam = struct {
                cont_fn: *const fn (A) F(B),
                fn call(map_self: @This(), i: usize, a: A) B {
                    return map_self.cont_fn(a)[i];
                }
            }{ .cont_fn = k };

            return imap(A, B, imap_lam, ma);
        }
    };
}

const ARRAY_LEN = 4;
const ArrayF = Array(ARRAY_LEN);

test "Array Functor fmap" {
    const ArrayFunctor = Functor(ArrayMonadImpl(ARRAY_LEN));

    var array_a = ArrayF(u32){ 0, 1, 2, 3 };
    array_a = ArrayFunctor.fmap(.InplaceMap, add10, array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 10, 11, 12, 13 }, &array_a);

    const array_f32 = ArrayFunctor.fmap(.InplaceMap, add_pi_f32, array_a);
    try testing.expectEqualSlices(f32, &[_]f32{ 13.14, 14.14, 15.14, 16.14 }, &array_f32);

    const array_f64 = ArrayFunctor.fmap(.NewValMap, mul_pi_f64, array_a);
    try testing.expectEqual(4, array_f64.len);
    for (&[_]f64{ 31.4, 34.54, 37.68, 40.82 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64[i], std.math.floatEps(f64));
    }
}

test "Array Applicative pure and fapply" {
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));

    const array_pured = ArrayApplicative.pure(@as(u32, 42));
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 42, 42 }, &array_pured);

    const array_a = ArrayF(u32){ 10, 20, 30, 40 };
    const IntToFloatFn = *const fn (u32) f64;
    const array_fns = ArrayF(IntToFloatFn){ add_pi_f64, mul_pi_f64, add_e_f64, mul_e_f64 };
    const array_f64 = ArrayApplicative.fapply(u32, f64, array_fns, array_a);
    try testing.expectEqual(4, array_f64.len);
    for (&[_]f64{ 13.14, 62.8, 32.71828, 108.7312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64[i], std.math.floatEps(f64));
    }
}

test "Array Monad bind" {
    const ArrayMonad = Monad(ArrayMonadImpl(ARRAY_LEN));

    const array_a = ArrayF(f64){ 10, 20, 30, 40 };
    const array_binded = ArrayMonad.bind(f64, u32, array_a, struct {
        fn f(a: f64) ArrayMonad.MbType(u32) {
            var array_b: ArrayF(u32) = undefined;
            var j: usize = 0;
            while (j < array_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    array_b[j] = @intFromFloat(@ceil(a * 4.0));
                } else {
                    array_b[j] = @intFromFloat(@ceil(a * 9.0));
                }
            }
            return array_b;
        }
    }.f);
    try testing.expectEqualSlices(u32, &[_]u32{ 40, 180, 120, 360 }, &array_binded);
}
