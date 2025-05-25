const std = @import("std");
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

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

const Monoid = monoid.Monoid;
const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

fn ArrayListBaseType(comptime ArrayA: type) type {
    return std.meta.Child(ArrayA.Slice);
}

/// The instance of Monoid ArrayList(T).
/// Like `instance Monoid ArrayList(T)` in haskell.
pub fn ArrayListMonoidImpl(comptime T: type) type {
    return struct {
        allocator: Allocator,

        const Self = @This();
        pub const Error: ?type = Allocator.Error;
        /// The type M is a monoid, so the Monoid(M) is a Constrait.
        pub const M = ArrayList(T);
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = if (Error) |Err| Err!M else M;

        pub const F = ArrayList;
        /// Get base type of M(A), it is must just is A.
        pub const BaseType = ArrayListBaseType;

        pub fn mempty(self: *const Self) EM {
            return ArrayList(T).init(self.allocator);
        }

        pub fn mappend(self: *const Self, ma: M, mb: M) EM {
            var mc = try ArrayList(T).initCapacity(self.allocator, ma.items.len + mb.items.len);
            mc.appendSliceAssumeCapacity(ma.items);
            mc.appendSliceAssumeCapacity(mb.items);
            return mc;
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            var acc = try self.mempty();
            for (xs) |x| {
                try acc.appendSlice(x.items);
            }

            return acc;
        }
    };
}

test "Monoid ArrayList(A) mconcat" {
    const allocator = testing.allocator;
    const ArrayMonoid = Monoid(ArrayList(u32));
    const array_monoid = ArrayMonoid.InstanceImpl{
        .allocator = allocator,
    };

    const array1: [2]u32 = @splat(42);
    const array2: [2]u32 = @splat(37);
    const array3: [3]u32 = @splat(13);
    var array_m1: ArrayList(u32) = .init(allocator);
    defer array_m1.deinit();
    var array_m2: ArrayList(u32) = .init(allocator);
    defer array_m2.deinit();
    var array_m3: ArrayList(u32) = .init(allocator);
    defer array_m3.deinit();

    try array_m1.appendSlice(&array1);
    try array_m2.appendSlice(&array2);
    try array_m3.appendSlice(&array3);
    const arrays = &[_]ArrayList(u32){ array_m1, array_m2, array_m3 };
    const concated = try array_monoid.mconcat(arrays);
    defer concated.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37, 13, 13, 13 }, concated.items);
}

pub const ArrayListMonadImpl = struct {
    allocator: Allocator,

    const Self = @This();

    const ARRAY_DEFAULT_LEN = 4;

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = ArrayList;

    /// Get base type of F(A), it is must just is A.
    pub const BaseType = ArrayListBaseType;

    pub const Error: ?type = Allocator.Error;

    pub const FxTypes = FunctorFxTypes(F, Error);
    pub const FaType = FxTypes.FaType;
    pub const FbType = FxTypes.FbType;
    pub const FaLamType = FxTypes.FaLamType;
    pub const FbLamType = FxTypes.FbLamType;

    const AFxTypes = ApplicativeFxTypes(F, Error);
    pub const APaType = AFxTypes.APaType;
    pub const AFbType = AFxTypes.AFbType;

    pub const MbType = MonadFxTypes(F, Error).MbType;

    pub fn deinitFa(
        fa: anytype, // ArrayList(A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
    ) void {
        for (fa.items) |item| {
            free_fn(item);
        }
        fa.deinit();
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
        const MapFn = @TypeOf(map_fn);
        const map_lam = struct {
            map_fn: *const fn (a: MapFnInType(MapFn)) MapFnRetType(MapFn),

            const MapSelf = @This();
            pub fn call(
                map_self: *const MapSelf,
                a: MapFnInType(MapFn),
            ) MapFnRetType(MapFn) {
                return map_self.map_fn(a);
            }
        }{ .map_fn = &map_fn };

        return fmapLam(self, K, map_lam, fa);
    }

    pub fn fmapLam(
        self: *const Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        if (comptime isInplaceMap(K)) {
            return self.mapInplace(K, map_lam, fa);
        } else {
            return self.mapNewValue(K, map_lam, fa);
        }
    }

    fn mapInplace(
        self: *const Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        const A = MapLamInType(@TypeOf(map_lam));
        const has_err, const B = comptime isErrorUnionOrVal(MapLamRetType(@TypeOf(map_lam)));
        const ValA = if (comptime isMapRef(K)) std.meta.Child(A) else A;
        if (@bitSizeOf(ValA) != @bitSizeOf(B)) {
            @compileError("The bitsize of translated value is not equal origin value, failed to map it");
        }

        const array = if (@typeInfo(@TypeOf(fa)) == .pointer)
            @constCast(fa).moveToUnmanaged()
        else
            @constCast(&fa).moveToUnmanaged();
        var slice = array.items;
        var i: usize = 0;
        while (i < slice.len) : (i += 1) {
            const a = if (comptime isMapRef(K)) &slice[i] else slice[i];
            const b = if (has_err) try map_lam.call(a) else map_lam.call(a);
            slice[i] = castInplaceValue(A, b);
        }

        var array_b: ArrayListUnmanaged(B) = .{
            .items = @ptrCast(slice),
            .capacity = array.capacity,
        };
        return array_b.toManaged(self.allocator);
    }

    fn mapNewValue(
        self: *const Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        const has_err, const B = comptime isErrorUnionOrVal(MapLamRetType(@TypeOf(map_lam)));
        var fb = try ArrayList(B).initCapacity(self.allocator, fa.items.len);

        var i: usize = 0;
        while (i < fa.items.len) : (i += 1) {
            const a = if (comptime isMapRef(K)) @constCast(&fa.items[i]) else fa.items[i];
            const b = if (has_err) try map_lam.call(a) else map_lam.call(a);
            fb.appendAssumeCapacity(b);
        }
        return fb;
    }

    pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
        const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
        var array = try ArrayList(_A).initCapacity(self.allocator, ARRAY_DEFAULT_LEN);

        const _a: _A = if (has_err) try a else a;
        array.appendAssumeCapacity(_a);
        return array;
    }

    pub fn fapply(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        ff: F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        return fapplyGeneric(self, .NormalMap, A, B, ff, fa);
    }

    pub fn fapplyLam(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        flam: anytype, // a F(lambda) that present F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        return fapplyGeneric(self, .LambdaMap, A, B, flam, fa);
    }

    fn fapplyGeneric(
        self: *const Self,
        comptime M: FMapMode,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        ff: anytype,
        fa: F(A),
    ) AFbType(B) {
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        var fb = try ArrayList(_B)
            .initCapacity(self.allocator, ff.items.len * fa.items.len);

        for (ff.items) |f| {
            for (fa.items) |item| {
                const b = if (M == .NormalMap) f(item) else f.call(item);
                fb.appendAssumeCapacity(if (has_err) try b else b);
            }
        }
        return fb;
    }

    pub fn bind(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (*const Self, A) MbType(B),
    ) MbType(B) {
        var mb = ArrayList(B).init(self.allocator);
        for (ma.items) |a| {
            const tmp_mb = try k(self, a);
            defer tmp_mb.deinit();
            try mb.appendSlice(tmp_mb.items);
        }
        return mb;
    }

    pub fn join(
        self: *const Self,
        comptime A: type,
        mma: F(F(A)),
    ) MbType(A) {
        var res_ma = ArrayList(A).init(self.allocator);
        for (mma.items) |ma| {
            if (ma.items.len > 0)
                try res_ma.appendSlice(ma.items);
        }
        return res_ma;
    }
};

// These functions are defined for unit test
const add10 = testu.add10;
const add_pi_f32 = testu.add_pi_f32;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;

test "ArrayList Functor fmap" {
    const allocator = testing.allocator;
    const ArrayFunctor = Functor(ArrayList);
    const array_functor = ArrayFunctor.InstanceImpl{ .allocator = allocator };

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();

    try array_a.appendSlice(&[_]u32{ 0, 1, 2, 3 });
    array_a = try array_functor.fmap(.InplaceMap, add10, array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 10, 11, 12, 13 }, array_a.items);

    const array_f32 = try array_functor.fmap(.InplaceMap, add_pi_f32, array_a);
    array_a.clearRetainingCapacity();
    try testing.expectEqualSlices(f32, &[_]f32{ 13.14, 14.14, 15.14, 16.14 }, array_f32.items);

    try array_a.appendSlice(&[_]u32{ 10, 20, 30, 40 });
    const array_f64 = try array_functor.fmap(.NewValMap, mul_pi_f64, array_a);
    defer array_f64.deinit();
    try testing.expectEqual(4, array_f64.items.len);
    for (&[_]f64{ 31.4, 62.8, 94.2, 125.6 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64.items[i], std.math.floatEps(f64));
    }
}

test "ArrayList Applicative pure and fapply" {
    const allocator = testing.allocator;
    const ArrayApplicative = Applicative(ArrayList);
    const array_applicative = ArrayApplicative.InstanceImpl{ .allocator = allocator };

    const array_pured = try array_applicative.pure(@as(u32, 42));
    defer array_pured.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{42}, array_pured.items);

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]u32{ 10, 20, 30, 40 });

    const IntToFloatFn = *const fn (u32) f64;
    var array_fns = ArrayList(IntToFloatFn).init(allocator);
    defer array_fns.deinit();
    try array_fns.appendSlice(&[_]IntToFloatFn{ add_pi_f64, mul_pi_f64 });

    const array_f64 = try array_applicative.fapply(u32, f64, array_fns, array_a);
    defer array_f64.deinit();
    try testing.expectEqual(8, array_f64.items.len);
    for (&[_]f64{ 13.14, 23.14, 33.14, 43.14, 31.4, 62.8, 94.2, 125.6 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_f64.items[i], std.math.floatEps(f64));
    }
}

test "ArrayList Monad bind" {
    const allocator = testing.allocator;
    const ArrayListMonad = Monad(ArrayList);
    const array_monad = ArrayListMonad.InstanceImpl{ .allocator = allocator };
    const ArrayListMImpl = @TypeOf(array_monad);

    var array_a = ArrayList(f64).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]f64{ 10, 20, 30, 40 });
    const array_binded = try array_monad.bind(f64, u32, array_a, struct {
        fn f(impl: *const ArrayListMImpl, a: f64) ArrayListMonad.MbType(u32) {
            var arr_b = try ArrayList(u32).initCapacity(impl.allocator, 2);
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 4.0)));
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 9.0)));
            return arr_b;
        }
    }.f);
    defer array_binded.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 40, 90, 80, 180, 120, 270, 160, 360 }, array_binded.items);
}

test "runDo Arraylist" {
    const input1: i32 = 42;

    const allocator = testing.allocator;
    const ArrayListMonad = Monad(ArrayList);
    const array_monad = ArrayListMonad.InstanceImpl{ .allocator = allocator };
    const ArrayListMImpl = @TypeOf(array_monad);
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: ArrayListMImpl,
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = ArrayListMImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *ArrayListMImpl) ArrayListMImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            const as = &([_]i32{ 17, ctx.param1 } ** 2);
            var array = ArrayList(i32).init(impl.allocator);
            try array.appendSlice(as);
            return array;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *ArrayListMImpl, a: i32) ArrayListMImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            return try impl.pure(@abs(a) + 2);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *ArrayListMImpl, b: u32) ArrayListMImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;

            const as = &[_]f64{
                @floatFromInt(@abs(ctx.a) + b),
                @as(f64, @floatFromInt(b)) + 3.14,
            };
            var array = ArrayList(f64).init(impl.allocator);
            try array.appendSlice(as);
            return array;
        }
    }{ .monad_impl = array_monad, .param1 = input1 };
    const out = try runDo(&do_ctx);
    defer out.deinit();
    try testing.expectEqual(8, out.items.len);
    try testing.expectEqualSlices(
        f64,
        &[_]f64{ 36, 22.14, 86, 47.14, 36, 22.14, 86, 47.14 },
        out.items,
    );
}
