//! Definition Maybe struct, these is a instance of
//! Functor|Applicative|Monad typeclass.
//! The PureMaybeMonadImpl is pure mode Maybe monad.

const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const pure_functor = @import("pure/functor.zig");
const pure_applicative = @import("pure/applicative.zig");
const pure_monad = @import("pure/monad.zig");
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

const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;
const PureFunctor = pure_functor.Functor;
const PureApplicative = pure_applicative.Applicative;
const PureMonad = pure_monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

pub const MaybeMonadImpl = struct {
    none: void,

    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = Maybe;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime MaybeA: type) type {
        return std.meta.Child(MaybeA);
    }

    pub const Error = error{};

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
        self: *Self,
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

    pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
        _ = self;
        const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
        const fa: ?_A = if (has_err) try a else a;
        return fa;
    }

    pub fn fapply(
        self: *Self,
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
        self: *Self,
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
        self: *Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (*Self, A) MbType(B),
    ) MbType(B) {
        if (ma) |a| {
            return k(self, a);
        }
        return null;
    }
};

pub const PureMaybeMonadImpl = struct {
    none: void = {},

    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = Maybe;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime MaybeA: type) type {
        return std.meta.Child(MaybeA);
    }
    pub const FxTypes = FunctorFxTypes(F, null);
    pub const FaType = FxTypes.FaType;
    pub const FbType = FxTypes.FbType;
    pub const FaLamType = FxTypes.FaLamType;
    pub const FbLamType = FxTypes.FbLamType;

    pub const MbType = Maybe;

    pub fn deinitFa(
        fa: anytype, // Maybe(A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
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

    pub fn bindWithCtx(
        comptime A: type,
        comptime B: type,
        ctx: anytype,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (@TypeOf(ctx), A) F(B),
    ) F(B) {
        if (ma) |a| {
            return k(ctx, a);
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
    const MaybeFunctor = Functor(MaybeMonadImpl);
    var maybe_functor = MaybeFunctor.init(.{ .none = {} });

    var maybe_a: ?u32 = null;
    maybe_a = try maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(null, maybe_a);

    maybe_a = 32;
    maybe_a = try maybe_functor.fmap(.InplaceMap, add10, maybe_a);
    try testing.expectEqual(42, maybe_a);

    maybe_a = null;
    var maybe_b = try maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 32;
    maybe_b = try maybe_functor.fmap(.NewValMap, add_pi_f64, maybe_a);
    try testing.expectEqual(32 + 3.14, maybe_b);
}

test "Maybe Applicative pure and fapply" {
    const MaybeApplicative = Applicative(MaybeMonadImpl);
    var maybe_applicative = MaybeApplicative.init(.{ .none = {} });

    const add24_from_f64 = &struct {
        fn f(x: f64) u32 {
            return @intFromFloat(@floor(x) + 24);
        }
    }.f;
    const fapply_fn = try maybe_applicative.pure(add24_from_f64);

    var maybe_a: ?f64 = null;
    var maybe_b = try maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 1.68;
    maybe_b = try maybe_applicative.fapply(f64, u32, fapply_fn, maybe_a);
    try testing.expectEqual(1 + 24, maybe_b);

    maybe_b = try maybe_applicative.fapply(u32, u32, null, maybe_b);
    try testing.expectEqual(null, maybe_b);
}

test "Maybe Monad bind" {
    const MaybeMonad = Monad(MaybeMonadImpl);
    var maybe_monad = MaybeMonad.init(.{ .none = {} });

    const cont_fn = &struct {
        fn k(self: *MaybeMonadImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = self;
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.k;

    var maybe_a: ?f64 = null;
    var maybe_b = try maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = try maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = try maybe_monad.bind(f64, u32, maybe_a, cont_fn);
    try testing.expectEqual(32, maybe_b);
}

test "runDo Maybe" {
    const input1: i32 = 42;

    const MaybeMonad = Monad(MaybeMonadImpl);
    const maybe_m = MaybeMonad.init(.{ .none = {} });
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: MaybeMonadImpl,
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const is_pure = false;

        // the do context struct must has startDo function
        pub fn startDo(impl: *MaybeMonadImpl) MaybeMonadImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *MaybeMonadImpl, a: i32) MaybeMonadImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *MaybeMonadImpl, b: u32) MaybeMonadImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;
            return @as(f64, @floatFromInt(b)) + 3.14;
        }
    }{ .monad_impl = maybe_m, .param1 = input1 };
    const out = runDo(&do_ctx);
    try testing.expectEqual(47.14, out);
}

// unit tests for pure Maybe monad
test "pure Maybe Functor fmap" {
    const MaybeFunctor = PureFunctor(PureMaybeMonadImpl);

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
    const MaybeApplicative = PureApplicative(PureMaybeMonadImpl);

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
    const MaybeMonad = PureMonad(PureMaybeMonadImpl);

    const cont1_f64 = &struct {
        fn k(x: f64) MaybeMonad.MbType(u32) {
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.k;

    const cont_ctx = struct {
        a: u32 = 7,
    }{};

    const cont2_f64 = &struct {
        fn k(ctx: @TypeOf(cont_ctx), x: f64) MaybeMonad.MbType(u32) {
            if (x == 3.14) {
                return null;
            } else {
                return @as(u32, @intFromFloat(@floor(x * 4.0))) + ctx.a;
            }
        }
    }.k;

    var maybe_a: ?f64 = null;
    var maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = MaybeMonad.bind(f64, u32, maybe_a, cont1_f64);
    try testing.expectEqual(32, maybe_b);

    maybe_a = null;
    maybe_b = MaybeMonad.bindWithCtx(f64, u32, cont_ctx, maybe_a, cont2_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = MaybeMonad.bindWithCtx(f64, u32, cont_ctx, maybe_a, cont2_f64);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = MaybeMonad.bindWithCtx(f64, u32, cont_ctx, maybe_a, cont2_f64);
    try testing.expectEqual(39, maybe_b);
}

test "runDo pure Maybe" {
    const input1: i32 = 42;

    const MaybeMonad = PureMonad(PureMaybeMonadImpl);
    _ = MaybeMonad;
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: PureMaybeMonadImpl = .{},
        param1: i32,

        // intermediate variable
        a: i32 = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const is_pure = true;

        // the do context struct must has startDo function
        pub fn startDo(impl: *PureMaybeMonadImpl) PureMaybeMonadImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *PureMaybeMonadImpl, a: i32) PureMaybeMonadImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.a = a;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *PureMaybeMonadImpl, b: u32) PureMaybeMonadImpl.MbType(f64) {
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

    const MaybeMonad = PureMonad(PureMaybeMonadImpl);
    _ = MaybeMonad;
    comptime var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: PureMaybeMonadImpl = .{},
        param1: i32,

        const Ctx = @This();
        pub const is_pure = true;

        // the do context struct must has startDo function
        pub fn startDo(impl: *PureMaybeMonadImpl) PureMaybeMonadImpl.MbType(i32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            return ctx.param1;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *PureMaybeMonadImpl, a: i32) PureMaybeMonadImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = ctx;
            return @abs(a) + 2;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *PureMaybeMonadImpl, b: u32) PureMaybeMonadImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = ctx;
            return @as(f64, @floatFromInt(b)) + 3.14;
        }
    }{ .param1 = input1 };
    const out = comptime runDo(&do_ctx);
    try testing.expectEqual(47.14, out);
}
