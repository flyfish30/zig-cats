const std = @import("std");
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const testu = @import("test_utils.zig");

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

const Monoid = monoid.Monoid;
const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

const Array = base.Array;

/// The instance of Monoid Array(T).
/// Like `instance Monoid Array(T)` in haskell.
pub fn ArrayMonoidImpl(comptime len: u32, comptime T: type) type {
    return struct {
        child_impl: ChildImpl,

        const Self = @This();
        const ChildImpl = Monoid(T).InstanceImpl;
        pub const Error: ?type = ChildImpl.Error;

        /// The type M is a monoid, so the Monoid(M) is a Constrait.
        pub const M = [len]T;
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = if (Error) |Err| Err!M else M;

        pub fn mempty(self: *const Self) EM {
            const a: [len]T = if (Error == null)
                @splat(self.child_impl.mempty())
            else
                @splat(try self.child_impl.mempty());
            return a;
        }

        pub fn mappend(self: *const Self, ma: M, mb: M) EM {
            var mc: M = undefined;
            for (ma[0..], mb[0..], mc[0..]) |a, b, *c| {
                c.* = if (Error == null)
                    self.child_impl.mappend(a, b)
                else
                    try self.child_impl.mappend(a, b);
            }
            return mc;
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            return monoid.commonMconcat(M, EM, self, xs);
        }
    };
}

const ArrayList = std.ArrayList;

test "Monoid Array(A) mempty and mappend" {
    const U32Monoid = Monoid(u32);
    const monoid_u32 = U32Monoid.InstanceImpl{};
    const Array4U32Monoid = Monoid([4]u32);
    const array4_u32_m = Array4U32Monoid.InstanceImpl{ .child_impl = monoid_u32 };
    try testing.expect(base.isPureTypeClass(@TypeOf(array4_u32_m)));

    const array4_u32_unit = array4_u32_m.mempty();
    try testing.expectEqualSlices(u32, &[_]u32{ 0, 0, 0, 0 }, &array4_u32_unit);

    const a1: [4]u32 = @splat(42);
    const a2: [4]u32 = @splat(37);
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 42, 42 }, &array4_u32_m.mappend(array4_u32_unit, a1));
    try testing.expectEqualSlices(u32, &[_]u32{ 79, 79, 79, 79 }, &array4_u32_m.mappend(a1, a2));

    const allocator = testing.allocator;
    const ArraylU32Monoid = Monoid(ArrayList(u32));
    const arrayl_monoid = ArraylU32Monoid.InstanceImpl{
        .allocator = allocator,
    };
    const Array2ArraylMonoid = Monoid([2]ArrayList(u32));
    const array2_arrayl_m = Array2ArraylMonoid.InstanceImpl{
        .child_impl = arrayl_monoid,
    };
    try testing.expect(!base.isPureTypeClass(@TypeOf(array2_arrayl_m)));

    const array2_arrayl_unit = try array2_arrayl_m.mempty();
    try testing.expectEqualSlices(u32, &[_]u32{}, array2_arrayl_unit[0].items);
    try testing.expectEqualSlices(u32, &[_]u32{}, array2_arrayl_unit[1].items);

    const slice1: [2]u32 = @splat(42);
    const slice2: [2]u32 = @splat(37);
    var array1_1 = ArrayList(u32).init(allocator);
    defer array1_1.deinit();
    try array1_1.appendSlice(&slice1);
    var array1_2 = ArrayList(u32).init(allocator);
    defer array1_2.deinit();
    try array1_2.appendSlice(&slice2);
    const array_a1 = [2]ArrayList(u32){ array1_1, array1_2 };

    var array2_1 = ArrayList(u32).init(allocator);
    defer array2_1.deinit();
    try array2_1.appendSlice(&slice2);
    var array2_2 = ArrayList(u32).init(allocator);
    defer array2_2.deinit();
    try array2_2.appendSlice(&slice1);
    const array_a2 = [2]ArrayList(u32){ array2_1, array2_2 };

    const appended_unit_a1 = try array2_arrayl_m.mappend(array2_arrayl_unit, array_a1);
    defer {
        appended_unit_a1[0].deinit();
        appended_unit_a1[1].deinit();
    }
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42 }, appended_unit_a1[0].items);
    try testing.expectEqualSlices(u32, &[_]u32{ 37, 37 }, appended_unit_a1[1].items);
    const append_a1a2 = try array2_arrayl_m.mappend(array_a1, array_a2);
    defer {
        append_a1a2[0].deinit();
        append_a1a2[1].deinit();
    }
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37 }, append_a1a2[0].items);
    try testing.expectEqualSlices(u32, &[_]u32{ 37, 37, 42, 42 }, append_a1a2[1].items);
}

pub fn ArrayMonadImpl(comptime len: usize) type {
    return struct {
        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = Array(len);
        pub const Error: ?type = null;

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime ArrayA: type) type {
            return std.meta.Child(ArrayA);
        }

        pub const FxTypes = FunctorFxTypes(F, null);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub const MbType = MonadFxTypes(F, Error).MbType;

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
            self: *const Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            _ = self;
            return fmapGeneric(K, .NormalMap, map_fn, fa);
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            return fmapGeneric(K, .LambdaMap, map_lam, fa);
        }

        fn fmapGeneric(
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

        pub fn pure(self: *const Self, a: anytype) F(@TypeOf(a)) {
            _ = self;
            return [1]@TypeOf(a){a} ** len;
        }

        pub fn fapply(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            ff: F(*const fn (A) B),
            fa: F(A),
        ) F(B) {
            _ = self;
            return fapplyGeneric(.NormalMap, A, B, ff, fa);
        }

        pub fn fapplyLam(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(A),
        ) F(B) {
            _ = self;
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
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*const Self, A) F(B),
        ) F(B) {
            return bindGeneric(self, .NormalMap, A, B, ma, k);
        }

        pub fn bindLam(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            klam: anytype,
        ) F(B) {
            return bindGeneric(self, .LambdaMap, A, B, ma, klam);
        }

        pub fn bindGeneric(
            self: *const Self,
            comptime M: FMapMode,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: anytype,
        ) F(B) {
            const imap_lam = struct {
                impl_self: *const Self,
                fn_or_lam: @TypeOf(k),
                fn call(map_self: *const @This(), i: usize, a: A) B {
                    if (M == .NormalMap) {
                        return map_self.fn_or_lam(map_self.impl_self, a)[i];
                    } else {
                        return map_self.fn_or_lam.call(map_self.impl_self, a)[i];
                    }
                }
            }{ .impl_self = self, .fn_or_lam = k };

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
    const ArrayFunctor = Functor(ArrayF);
    const array_functor = ArrayFunctor.InstanceImpl{};

    var array_a = ArrayF(u32){ 0, 1, 2, 3 };
    array_a = array_functor.fmap(.InplaceMap, add10, array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 10, 11, 12, 13 }, &array_a);

    const array_f32 = array_functor.fmap(.InplaceMap, add_pi_f32, array_a);
    try testing.expectEqualSlices(f32, &[_]f32{ 13.14, 14.14, 15.14, 16.14 }, &array_f32);

    const array_f64 = array_functor.fmap(.NewValMap, mul_pi_f64, array_a);
    try testing.expectEqual(4, array_f64.len);
    for (&[_]f64{ 31.4, 34.54, 37.68, 40.82 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64[i], std.math.floatEps(f64));
    }
}

test "Array Applicative pure and fapply" {
    const ArrayApplicative = Applicative(ArrayF);
    const array_applicative = ArrayApplicative.InstanceImpl{};

    const array_pured = array_applicative.pure(@as(u32, 42));
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 42, 42 }, &array_pured);

    const array_a = ArrayF(u32){ 10, 20, 30, 40 };
    const IntToFloatFn = *const fn (u32) f64;
    const array_fns = ArrayF(IntToFloatFn){ add_pi_f64, mul_pi_f64, add_e_f64, mul_e_f64 };
    const array_f64 = array_applicative.fapply(u32, f64, array_fns, array_a);
    try testing.expectEqual(4, array_f64.len);
    for (&[_]f64{ 13.14, 62.8, 32.71828, 108.7312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64[i], std.math.floatEps(f64));
    }
}

test "Array Monad bind" {
    const ArrayMonad = Monad(ArrayF);
    const array_monad = ArrayMonad.InstanceImpl{};
    const ArrayFImpl = @TypeOf(array_monad);

    const array_a = ArrayF(f64){ 10, 20, 30, 40 };
    const array_binded = array_monad.bind(f64, u32, array_a, struct {
        fn f(impl: *const ArrayFImpl, a: f64) ArrayFImpl.MbType(u32) {
            _ = impl;
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

    const lam = struct {
        m: f64 = 3.14,

        const Self = @This();
        fn call(self: *const Self, impl: *const ArrayFImpl, a: u32) ArrayFImpl.MbType(f64) {
            _ = impl;
            var array_b: ArrayF(f64) = [_]f64{ 2, 4, 6, 8 };
            var j: usize = 0;
            while (j < array_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    array_b[j] += @as(f64, @floatFromInt(a)) * self.m;
                } else {
                    array_b[j] += @as(f64, @floatFromInt(a)) + self.m;
                }
            }
            return array_b;
        }
    }{};

    const array_c = array_monad.bindLam(u32, f64, array_binded, lam);
    try testing.expectEqualSlices(f64, &[_]f64{ 130.74, 189.14, 392.22, 375.14 }, &array_c);
}

test "runDo Array" {
    const input1: i32 = 42;

    const ArrayMonad = Monad(ArrayF);
    const array_monad = ArrayMonad.InstanceImpl{};
    const ArrayFImpl = @TypeOf(array_monad);
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: ArrayFImpl,
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = ArrayFImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *ArrayFImpl) ArrayFImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            const array = [_]i32{ 17, ctx.param1 } ** 2;
            return array;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *ArrayFImpl, a: i32) ArrayFImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            const tmp = @abs(a);
            return [_]u32{ tmp + 2, tmp * 2, tmp * 3, tmp + 4 };
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *ArrayFImpl, b: u32) ArrayFImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;

            const array = [_]f64{
                @floatFromInt(@abs(ctx.a) + b),
                @as(f64, @floatFromInt(b)) + 3.14,
                @floatFromInt(@abs(ctx.a) * b),
                @as(f64, @floatFromInt(b)) * 3.14,
            };
            return array;
        }
    }{ .monad_impl = array_monad, .param1 = input1 };
    const out = runDo(&do_ctx);
    try testing.expectEqualSlices(
        f64,
        &[_]f64{ 36, 87.14, 867, 144.44 },
        &out,
    );
}

test "comptime runDo Array" {
    const input1: i32 = 42;

    const ArrayMonad = Monad(ArrayF);
    const array_monad = ArrayMonad.InstanceImpl{};
    const ArrayFImpl = @TypeOf(array_monad);

    comptime var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: ArrayFImpl,
        param1: i32,

        const Ctx = @This();
        pub const Error: ?type = ArrayFImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *ArrayFImpl) ArrayFImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            const array = [_]i32{ 17, ctx.param1 } ** 2;
            return array;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *ArrayFImpl, a: i32) ArrayFImpl.MbType(u32) {
            _ = impl;
            const tmp = @abs(a);
            return [_]u32{ tmp + 2, tmp * 2, tmp * 3, tmp + 4 };
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *ArrayFImpl, b: u32) ArrayFImpl.MbType(f64) {
            _ = impl;
            const array = [_]f64{
                @floatFromInt(17 + b),
                @as(f64, @floatFromInt(b)) + 3.14,
                @floatFromInt(17 * b),
                @as(f64, @floatFromInt(b)) * 3.14,
            };
            return array;
        }
    }{ .monad_impl = array_monad, .param1 = input1 };
    const out = comptime runDo(&do_ctx);
    try testing.expectEqualSlices(
        f64,
        &[_]f64{ 36, 87.14, 867, 144.44 },
        &out,
    );
}
