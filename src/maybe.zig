//! Definition Maybe struct, these is a instance of
//! Functor|Applicative|Monad typeclass.

const std = @import("std");
const base = @import("base.zig");
const semi_grp = @import("semigroup.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const array = @import("array_list_monad.zig");
const testu = @import("test_utils.zig");

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

const Monoid = monoid.Monoid;
const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

/// The instance of Monoid Maybe(T), the type T must be a SemiGroup.
/// Like `instance SemiGroup T => Monoid (Maybe T)` in haskell.
pub fn MaybeMonoidImpl(comptime T: type) type {
    return struct {
        child_impl: ChildImpl,

        const Self = @This();
        const ChildImpl = semi_grp.SemiGroup(T).InstanceImpl;
        pub const Error: ?type = ChildImpl.Error;

        /// The type M is a monoid, so the Monoid(M) is a Constrait.
        pub const M = Maybe(T);
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = if (Error) |Err| Err!M else M;

        pub fn mempty(self: *const Self) EM {
            _ = self;
            return null;
        }

        pub fn mappend(self: *const Self, ma: M, mb: M) EM {
            if (ma == null) return mb;
            if (mb == null) return ma;
            if (Error == null) {
                return self.child_impl.mappend(ma.?, mb.?);
            } else {
                return try self.child_impl.mappend(ma.?, mb.?);
            }
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            return monoid.commonMconcat(M, EM, self, xs);
        }
    };
}

const MaybeErrorImpl = struct {
    const Self = @This();
    pub const Error: ?type = null;

    // the M is Maybe(error_set)
    pub const M = ?type;
    pub const EM = M;

    pub fn mempty(self: Self) ?type {
        _ = self;
        return null;
    }

    pub fn mappend(self: Self, ma: M, mb: M) EM {
        _ = self;
        if (ma == null) return mb;
        if (mb == null) return ma;
        return ma.? || mb.?;
    }
};

pub const maybe_error: MaybeErrorImpl = MaybeErrorImpl{};

const ArrayList = std.ArrayList;
const SemiGroup = semi_grp.SemiGroup;

test "Monoid Maybe(A) mempty and mappend" {
    const U32SemiGroup = SemiGroup(u32);
    const semi_grp_u32 = U32SemiGroup.InstanceImpl{};
    const MaybeU32Monoid = Monoid(?u32);
    const maybe_u32_m = MaybeU32Monoid.InstanceImpl{ .child_impl = semi_grp_u32 };
    try testing.expect(base.isPureTypeClass(@TypeOf(maybe_u32_m)));

    const maybe_unit = maybe_u32_m.mempty();
    try testing.expectEqual(null, maybe_unit);

    const m1: ?u32 = 42;
    const m2: ?u32 = 37;
    try testing.expectEqual(42, maybe_u32_m.mappend(maybe_unit, m1));
    try testing.expectEqual(79, maybe_u32_m.mappend(m1, m2));

    const allocator = testing.allocator;
    const ArrayU32SemiGroup = SemiGroup(ArrayList(u32));
    const semi_grp_array = ArrayU32SemiGroup.InstanceImpl{
        .allocator = allocator,
    };
    const MaybeArrayMonoid = Monoid(?ArrayList(u32));
    const maybe_array_m = MaybeArrayMonoid.InstanceImpl{
        .child_impl = semi_grp_array,
    };
    try testing.expect(!base.isPureTypeClass(@TypeOf(maybe_array_m)));

    const maybe_array_unit = try maybe_array_m.mempty();
    try testing.expectEqual(null, maybe_array_unit);
    const array1: [2]u32 = @splat(42);
    const array2: [2]u32 = @splat(37);
    var array_m1: ?ArrayList(u32) = .init(allocator);
    defer array_m1.?.deinit();
    var array_m2: ?ArrayList(u32) = .init(allocator);
    defer array_m2.?.deinit();

    try array_m1.?.appendSlice(&array1);
    try array_m2.?.appendSlice(&array2);
    const appended_unit_m1 = try maybe_array_m.mappend(maybe_array_unit, array_m1);
    // mappend with a unit in Maybe(A) monoid, the returned Maybe(A) is just same as
    // the inpute Maybe(A), so it don't call appended_unit_m1.?.deinit().
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42 }, appended_unit_m1.?.items);
    const append_m1m2 = try maybe_array_m.mappend(array_m1, array_m2);
    defer append_m1m2.?.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37 }, append_m1m2.?.items);
}

test "Monoid Maybe(A) mconcat" {
    const allocator = testing.allocator;
    const ArrayU32SemiGroup = SemiGroup(ArrayList(u32));
    const semi_grp_array = ArrayU32SemiGroup.InstanceImpl{
        .allocator = allocator,
    };
    const MaybeArrayMonoid = Monoid(?ArrayList(u32));
    var maybe_array_m = MaybeArrayMonoid.InstanceImpl{
        .child_impl = semi_grp_array,
    };
    try testing.expect(!base.isPureTypeClass(@TypeOf(maybe_array_m)));

    const array1: [2]u32 = @splat(42);
    const array2: [2]u32 = @splat(37);
    var array_m1: ?ArrayList(u32) = .init(allocator);
    defer array_m1.?.deinit();
    var array_m2: ?ArrayList(u32) = .init(allocator);
    defer array_m2.?.deinit();

    try array_m1.?.appendSlice(&array1);
    try array_m2.?.appendSlice(&array2);
    const maybe_arrays = &[_]?ArrayList(u32){
        array_m1,
        null,
        array_m2,
    };

    const concated = try maybe_array_m.mconcat(maybe_arrays);
    defer concated.?.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37 }, concated.?.items);
}

pub const MaybeMonadImpl = struct {
    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = Maybe;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime MaybeA: type) type {
        return std.meta.Child(MaybeA);
    }

    pub const Error: ?type = null;

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
        fa: anytype, // Maybe(A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
    ) void {
        if (fa) |a| {
            free_fn(a);
        }
    }

    pub fn fmap(
        self: *const Self,
        comptime K: MapFnKind,
        map_fn: anytype,
        fa: FaType(K, @TypeOf(map_fn)),
    ) FbType(@TypeOf(map_fn)) {
        _ = self;
        const MapFn = @TypeOf(map_fn);
        const has_err, const B = comptime isErrorUnionOrVal(MapFnRetType(MapFn));
        if (comptime isMapRef(K)) {
            if (fa.* != null) {
                const b = map_fn(&(fa.*.?));
                const fb: ?B = if (has_err) try b else b;
                return fb;
            }
        } else {
            if (fa) |a| {
                const b = map_fn(a);
                const fb: ?B = if (has_err) try b else b;
                return fb;
            }
        }

        return null;
    }

    pub fn fmapLam(
        self: *const Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        _ = self;
        const MapLam = @TypeOf(map_lam);
        const has_err, const B = comptime isErrorUnionOrVal(MapLamRetType(MapLam));
        if (comptime isMapRef(K)) {
            if (fa.* != null) {
                const b = map_lam.call(@constCast(&(fa.*.?)));
                const fb: ?B = if (has_err) try b else b;
                return fb;
            }
        } else {
            if (fa) |a| {
                const b = map_lam.call(a);
                const fb: ?B = if (has_err) try b else b;
                return fb;
            }
        }

        return null;
    }

    pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
        _ = self;
        const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
        const fa: ?_A = if (has_err) try a else a;
        return fa;
    }

    pub fn fapply(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        ff: F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        _ = self;
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        if (ff) |f| {
            if (fa) |a| {
                const b = f(a);
                const fb: ?_B = if (has_err) try b else b;
                return fb;
            }
        }
        return null;
    }

    pub fn fapplyLam(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        flam: anytype, // a F(lambda) that present F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        _ = self;
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        if (flam) |lam| {
            if (fa) |a| {
                const b = lam.call(a);
                const fb: ?_B = if (has_err) try b else b;
                return fb;
            }
        }
        return null;
    }

    pub fn bind(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (*const Self, A) MbType(B),
    ) MbType(B) {
        if (ma) |a| {
            return k(self, a);
        }
        return null;
    }

    pub fn bindLam(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        klam: anytype,
    ) MbType(B) {
        if (ma) |a| {
            return klam.call(self, a);
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

// unit tests for impure Maybe monad
test "Maybe Functor fmap" {
    const MaybeFunctor = Functor(Maybe);
    const maybe_functor = MaybeFunctor.InstanceImpl{};

    var maybe_a: ?u32 = null;
    maybe_a = maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(null, maybe_a);

    maybe_a = 32;
    maybe_a = maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(42, maybe_a);

    maybe_a = null;
    var maybe_b = maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 32;
    maybe_b = maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(32 + 3.14, maybe_b);
}

test "Maybe Applicative pure and fapply" {
    const MaybeApplicative = Applicative(Maybe);
    const maybe_applicative = MaybeApplicative.InstanceImpl{};

    const add24_from_f64 = &struct {
        fn f(x: f64) u32 {
            return @intFromFloat(@floor(x) + 24);
        }
    }.f;
    const fapply_fn = maybe_applicative.pure(add24_from_f64);

    var maybe_a: ?f64 = null;
    var maybe_b = maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 1.68;
    maybe_b = maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(1 + 24, maybe_b);

    maybe_b = maybe_applicative.fapply(u32, u32, null, maybe_b);
    try testing.expectEqual(null, maybe_b);
}

test "Maybe Monad bind" {
    const MaybeMonad = Monad(Maybe);
    const maybe_monad = MaybeMonad.InstanceImpl{};

    const cont_fn = &struct {
        fn k(impl: *const MaybeMonadImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = impl;
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.k;

    var maybe_a: ?f64 = null;
    var maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(32, maybe_b);
}

test "runDo Maybe" {
    const input1: i32 = 42;

    const MaybeMonad = Monad(Maybe);
    const maybe_monad = MaybeMonad.InstanceImpl{};
    const MaybeMImpl = @TypeOf(maybe_monad);
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: MaybeMImpl,
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = MaybeMImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *MaybeMImpl) MaybeMImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *MaybeMImpl, a: i32) MaybeMImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *MaybeMImpl, b: u32) MaybeMImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;
            return @as(f64, @floatFromInt(b)) + 3.14;
        }
    }{ .monad_impl = maybe_monad, .param1 = input1 };
    const out = runDo(&do_ctx);
    try testing.expectEqual(47.14, out);
}

// unit tests for pure Maybe monad
test "pure Maybe Functor fmap" {
    const MaybeFunctor = Functor(Maybe);
    const maybe_functor = MaybeFunctor.InstanceImpl{};

    var maybe_a: ?u32 = null;
    maybe_a = maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(null, maybe_a);

    maybe_a = 32;
    maybe_a = maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(42, maybe_a);

    maybe_a = null;
    var maybe_b = maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 32;
    maybe_b = maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(32 + 3.14, maybe_b);
}

test "pure Maybe Applicative pure and fapply" {
    const MaybeApplicative = Applicative(Maybe);
    const maybe_applicative = MaybeApplicative.InstanceImpl{};

    const add24_from_f64 = &struct {
        fn f(x: f64) u32 {
            return @intFromFloat(@floor(x) + 24);
        }
    }.f;
    const fapply_fn = maybe_applicative.pure(add24_from_f64);

    var maybe_a: ?f64 = null;
    var maybe_b = maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 1.68;
    maybe_b = maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(1 + 24, maybe_b);

    maybe_b = maybe_applicative.fapply(u32, u32, null, maybe_b);
    try testing.expectEqual(null, maybe_b);
}

test "pure Maybe Monad bind" {
    const MaybeMonad = Monad(Maybe);
    const maybe_monad = MaybeMonad.InstanceImpl{};
    const MaybeMImpl = @TypeOf(maybe_monad);

    const cont1_f64 = &struct {
        fn k(impl: *const MaybeMImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = impl;
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.k;

    const cont_lam = struct {
        a: u32 = 7,
        fn call(self: *const @This(), impl: *const MaybeMImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = impl;
            if (x == 3.14) {
                return null;
            } else {
                return @as(u32, @intFromFloat(@floor(x * 4.0))) + self.a;
            }
        }
    }{};

    var maybe_a: ?f64 = null;
    var maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = maybe_monad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(32, maybe_b);

    maybe_a = null;
    maybe_b = maybe_monad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = maybe_monad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = maybe_monad.bindLam(f64, u32, maybe_a, cont_lam);
    try testing.expectEqual(39, maybe_b);
}

test "runDo pure Maybe" {
    const input1: i32 = 42;

    const MaybeMonad = Monad(Maybe);
    const maybe_monad = MaybeMonad.InstanceImpl{};
    const MaybeMImpl = @TypeOf(maybe_monad);
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: MaybeMImpl = .{},
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = MaybeMImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *MaybeMImpl) MaybeMImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *MaybeMImpl, a: i32) MaybeMImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *MaybeMImpl, b: u32) MaybeMImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;
            return @as(f64, @floatFromInt(b + @abs(ctx.a))) + 3.14;
        }
    }{ .param1 = input1 };
    const out = runDo(&do_ctx);
    try testing.expectEqual(89.14, out);
}

test "comptime runDo pure Maybe" {
    const input1: i32 = 42;

    const MaybeMonad = Monad(Maybe);
    const maybe_monad = MaybeMonad.InstanceImpl{};
    const MaybeMImpl = @TypeOf(maybe_monad);
    comptime var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: MaybeMImpl = .{},
        param1: i32,

        const Ctx = @This();
        pub const Error: ?type = MaybeMImpl.Error;

        // the do context struct must has startDo function
        pub fn startDo(impl: *MaybeMImpl) MaybeMImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *MaybeMImpl, a: i32) MaybeMImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = ctx;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *MaybeMImpl, b: u32) MaybeMImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = ctx;
            return @as(f64, @floatFromInt(b)) + 3.14;
        }
    }{ .param1 = input1 };
    const out = comptime runDo(&do_ctx);
    try testing.expectEqual(47.14, out);
}
