const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const testu = @import("../test_utils.zig");

const testing = std.testing;
const assert = std.debug.assert;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const FMapMode = base.FMapMode;
const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const castInplaceValue = base.castInplaceValue;

const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const impure_functor = @import("../functor.zig");
const FunctorFxTypes = impure_functor.FunctorFxTypes;

const Maybe = base.Maybe;
const Array = base.Array;

pub fn ArrayMonadImpl(comptime len: usize) type {
    return struct {
        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = Array(len);

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime ArrayA: type) type {
            return std.meta.Child(ArrayA);
        }

        pub const FxTypes = FunctorFxTypes(F, null);
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
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
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
            return bindGeneric(A, B, void, {}, ma, k);
        }

        pub fn bindWithCtx(
            comptime A: type,
            comptime B: type,
            ctx: anytype,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k_ctx: *const fn (@TypeOf(ctx), A) F(B),
        ) F(B) {
            return bindGeneric(A, B, @TypeOf(ctx), ctx, ma, k_ctx);
        }

        pub fn bindGeneric(
            comptime A: type,
            comptime B: type,
            comptime Ctx: type,
            ctx: Ctx,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k_fn_ctx: if (Ctx == void) *const fn (A) F(B) else *const fn (Ctx, A) F(B),
        ) F(B) {
            const imap_lam = struct {
                cont_ctx: Ctx,
                cont_fn_ctx: @TypeOf(k_fn_ctx),
                fn call(map_self: @This(), i: usize, a: A) B {
                    if (Ctx == void) {
                        return map_self.cont_fn_ctx(a)[i];
                    } else {
                        return map_self.cont_fn_ctx(map_self.cont_ctx, a)[i];
                    }
                }
            }{ .cont_ctx = ctx, .cont_fn_ctx = k_fn_ctx };

            return imap(A, B, imap_lam, ma);
        }
    };
}

// These functions are used for unit test
const add10 = testu.add10;
const add_pi_f32 = testu.add_pi_f32;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const add_e_f64 = testu.add_e_f64;
const mul_e_f64 = testu.mul_e_f64;

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
            var array_b: ArrayF(u32) = [_]u32{ 1, 2, 3, 4 };
            var j: usize = 0;
            while (j < array_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    array_b[j] += @intFromFloat(@ceil(a * 4.0));
                } else {
                    array_b[j] += @intFromFloat(@ceil(a * 9.0));
                }
            }
            return array_b;
        }
    }.f);
    try testing.expectEqualSlices(u32, &[_]u32{ 41, 182, 123, 364 }, &array_binded);

    const cont_ctx = struct {
        m: f64 = 3.14,
    }{};

    const array_c = ArrayMonad.bindWithCtx(u32, f64, cont_ctx, array_binded, struct {
        fn f(ctx: @TypeOf(cont_ctx), a: u32) ArrayMonad.MbType(f64) {
            var array_b: ArrayF(f64) = [_]f64{ 2, 4, 6, 8 };
            var j: usize = 0;
            while (j < array_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    array_b[j] += @as(f64, @floatFromInt(a)) * ctx.m;
                } else {
                    array_b[j] += @as(f64, @floatFromInt(a)) + ctx.m;
                }
            }
            return array_b;
        }
    }.f);
    try testing.expectEqualSlices(f64, &[_]f64{ 130.74, 189.14, 392.22, 375.14 }, &array_c);
}
