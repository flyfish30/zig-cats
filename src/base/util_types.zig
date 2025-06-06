const std = @import("std");
const base = @import("../base.zig");
const semi_grp = @import("../semigroup.zig");
const monoid = @import("../monoid.zig");
const functor = @import("../functor.zig");
const applicative = @import("../applicative.zig");
const monad = @import("../monad.zig");
const testu = @import("../test_utils.zig");
const arraym = @import("../array_monad.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const ApplyFnInType = base.ApplyFnInType;
const ApplyFnRetType = base.ApplyFnRetType;
const ApplyLamInType = base.ApplyLamInType;
const ApplyLamRetType = base.ApplyLamRetType;

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

const Array = base.Array;
const ArrayList = std.ArrayList;

pub fn Identity(comptime A: type) type {
    return struct {
        a: A,

        const Self = @This();
        const BaseType = A;

        pub const SemiGroupImpl = IdentityMonoidImpl(Self);
        pub const MonoidImpl = IdentityMonoidImpl(Self);
        pub const FunctorImpl = IdentityMonadImpl;
        pub const ApplicativeImpl = IdentityMonadImpl;
        pub const MonadImpl = IdentityMonadImpl;

        pub fn deinit(self: Self) void {
            base.deinitOrUnref(self.a);
        }

        pub fn fromA(a: A) Self {
            return .{ .a = a };
        }

        pub fn toA(self: Self) A {
            return self.a;
        }
    };
}

fn IdentityMonoidImpl(comptime IdA: type) type {
    return struct {
        base_impl: BaseImpl,

        const Self = @This();
        const A = IdA.BaseType;
        const BaseImpl = Monoid(A).InstanceImpl;

        pub const Error: ?type = BaseImpl.Error;
        pub const M = IdA;
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = if (Error) |Err| Err!M else M;

        const fromA = IdA.fromA;
        const toA = IdA.toA;

        pub fn mempty(self: *const Self) EM {
            if (Error == null) {
                return IdA.fromA(self.base_impl.mempty());
            } else {
                return IdA.fromA(try self.base_impl.mempty());
            }
        }

        pub fn mappend(self: *const Self, a: M, b: M) EM {
            if (Error == null) {
                return IdA.fromA(self.base_impl.mappend(a.toA(), b.toA()));
            } else {
                return IdA.fromA(try self.base_impl.mappend(a.toA(), b.toA()));
            }
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            var acc = if (Error == null) self.base_impl.mempty() else try self.base_impl.mempty();
            for (xs) |x| {
                const new_acc = if (Error == null)
                    self.base_impl.mappend(acc, x.toA())
                else
                    try self.base_impl.mappend(acc, x.toA());
                base.deinitOrUnref(acc);
                acc = new_acc;
            }
            return fromA(acc);
        }
    };
}

test "Monoid Identity(A) mempty, mappend and mconcat" {
    const U32Monoid = Monoid(u32);
    const u32_impl = U32Monoid.InstanceImpl{};
    const IdentityMonoid = Monoid(Identity(u32));
    const identity_monoid = IdentityMonoid.InstanceImpl{
        .base_impl = u32_impl,
    };

    const id_0 = identity_monoid.mempty();
    try testing.expectEqual(0, id_0.toA());

    const id_1 = Identity(u32).fromA(13);
    const id_2 = Identity(u32).fromA(42);
    const id_3 = Identity(u32).fromA(37);

    const id_01 = identity_monoid.mappend(id_0, id_1);
    try testing.expectEqual(13, id_01.toA());
    const id_23 = identity_monoid.mappend(id_2, id_3);
    try testing.expectEqual(79, id_23.toA());

    const ids = &[_]Identity(u32){ id_1, id_2, id_3 };
    const concated = identity_monoid.mconcat(ids);
    try testing.expectEqual(92, concated.toA());
}

const IdentityMonadImpl = struct {
    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = Identity;

    /// Get base type of Constant(T)(A), it is must just is A.
    pub fn BaseType(comptime IdA: type) type {
        return IdA.BaseType;
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
        fa: anytype, // Identity(A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
    ) void {
        free_fn(fa.toA());
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
        const b = if (comptime isMapRef(K))
            map_fn(&(fa.*.toA()))
        else
            map_fn(fa.toA());
        return if (has_err) try F(B).fromA(b) else F(B).fromA(b);
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
        const b = if (comptime isMapRef(K))
            map_lam.call(&(fa.*.toA()))
        else
            map_lam.call(fa.toA());
        return if (has_err) try F(B).fromA(b) else F(B).fromA(b);
    }

    pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
        _ = self;
        const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
        return if (has_err) try F(_A).fromA(a) else F(_A).fromA(a);
    }

    pub fn fapply(
        self: *const Self,
        // applicative function: F (a -> b), fa: F a
        // ff: F(*const fn (A) B),
        ff: anytype,
        fa: F(ApplyFnInType(Self, @TypeOf(ff))),
    ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
        _ = self;
        const B = ApplyFnRetType(Self, @TypeOf(ff));
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        const f = ff.toA();
        const a = fa.toA();
        const b = f(a);
        return if (has_err) try F(_B).fromA(b) else F(_B).fromA(b);
    }

    pub fn fapplyLam(
        self: *const Self,
        // applicative function: F (a -> b), fa: F a
        flam: anytype, // a F(lambda) that present F(*const fn (A) B),
        fa: F(ApplyLamInType(Self, @TypeOf(flam))),
    ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
        _ = self;
        const B = ApplyLamRetType(Self, @TypeOf(flam));
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        const lam = flam.toA();
        const a = fa.toA();
        const b = lam.call(a);
        return if (has_err) try F(_B).fromA(b) else F(_B).fromA(b);
    }

    pub fn bind(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        k: *const fn (*const Self, A) MbType(B),
    ) MbType(B) {
        const a = ma.toA();
        return k(self, a);
    }

    pub fn bindLam(
        self: *const Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        klam: anytype,
    ) MbType(B) {
        const a = ma.toA();
        return klam.call(self, a);
    }

    pub fn join(
        self: *const Self,
        comptime A: type,
        mma: F(F(A)),
    ) MbType(A) {
        _ = self;
        return mma.toA();
    }
};

const Ident_mul_f64_Klam = struct {
    _x: f64,
    const Self = @This();
    pub fn call(self: *const Self, impl: *const IdentityMonadImpl, a: u32) Identity(f64) {
        _ = impl;
        return Identity(f64).fromA(@as(f64, @floatFromInt(a)) * self._x);
    }
};

test "Monad Identity pure, fmap, fapply and bind" {
    const IdentityMonad = Monad(Identity);
    const identity_monad = IdentityMonad.InstanceImpl{};

    const id_1: Identity(u32) = .fromA(42);
    const id_2 = identity_monad.fmap(.InplaceMap, add10, id_1);
    try testing.expectEqual(52, id_2.toA());

    const id_f = identity_monad.pure(&mul_pi_f64);
    const id_3 = identity_monad.fapply(id_f, id_2);
    try testing.expectEqual(163.28, id_3.toA());

    const sum_mul_2_4_klam = Ident_mul_f64_Klam{ ._x = 2.4 };
    const id_4 = identity_monad.bindLam(u32, f64, id_2, sum_mul_2_4_klam);
    try testing.expectEqual(124.8, id_4.toA());
    const id_5 = identity_monad.join(f64, identity_monad.pure(id_3));
    try testing.expectEqual(163.28, id_5.toA());
}

pub fn Constant(comptime T: type) TCtor {
    return struct {
        fn ConstantT(comptime A: type) type {
            return struct {
                t: T,

                const Self = @This();
                const ConstType = T;
                pub const BaseType = A;
                pub const SemiGroupImpl = ConstantMonoidImpl(Self);
                pub const MonoidImpl = ConstantMonoidImpl(Self);
                pub const FunctorImpl = ConstantApplicativeImpl(T);
                pub const ApplicativeImpl = ConstantApplicativeImpl(T);

                pub fn deinit(self: Self) void {
                    base.deinitOrUnref(self.t);
                }
            };
        }
    }.ConstantT;
}

fn ConstantMonoidImpl(comptime ConstTA: type) type {
    return struct {
        monoid_impl: MonoidImpl,

        const Self = @This();
        const T = ConstTA.ConstType;
        const A = ConstTA.BaseType;
        const MonoidImpl = Monoid(T).InstanceImpl;

        pub const Error: ?type = MonoidImpl.Error;
        pub const M = ConstTA;
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = if (Error) |Err| Err!M else M;

        pub fn mempty(self: *const Self) EM {
            if (Error == null) {
                return .{ .t = self.monoid_impl.mempty() };
            } else {
                return .{ .t = try self.monoid_impl.mempty() };
            }
        }

        pub fn mappend(self: *const Self, a: M, b: M) EM {
            if (Error == null) {
                return .{ .t = self.monoid_impl.mappend(a.t, b.t) };
            } else {
                return .{ .t = try self.monoid_impl.mappend(a.t, b.t) };
            }
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            var acc = if (Error == null) self.monoid_impl.mempty() else try self.monoid_impl.mempty();
            for (xs) |x| {
                const new_acc = if (Error == null)
                    self.monoid_impl.mappend(acc, x.t)
                else
                    try self.monoid_impl.mappend(acc, x.t);
                base.deinitOrUnref(acc);
                acc = new_acc;
            }
            return .{ .t = acc };
        }
    };
}

test "Monoid Constant(T)(A) mempty and mappend, mconcat" {
    const allocator = testing.allocator;
    const ArrayMonoid = Monoid(ArrayList(u32));
    const array_monoid = ArrayMonoid.InstanceImpl{
        .allocator = allocator,
    };
    const ConstMonoid = Monoid(Constant(ArrayList(u32))(u32));
    const const_monoid = ConstMonoid.InstanceImpl{
        .monoid_impl = array_monoid,
    };

    var array_m1: ArrayList(u32) = .init(allocator);
    var array_m2: ArrayList(u32) = .init(allocator);
    var array_m3: ArrayList(u32) = .init(allocator);

    const array1: [2]u32 = @splat(42);
    const array2: [2]u32 = @splat(37);
    const array3: [3]u32 = @splat(13);
    try array_m1.appendSlice(&array1);
    const const_array1 = Constant(ArrayList(u32))(u32){ .t = array_m1 };
    defer const_array1.deinit();
    try array_m2.appendSlice(&array2);
    const const_array2 = Constant(ArrayList(u32))(u32){ .t = array_m2 };
    defer const_array2.deinit();
    try array_m3.appendSlice(&array3);
    const const_array3 = Constant(ArrayList(u32))(u32){ .t = array_m3 };
    defer const_array3.deinit();
    const consts = &[_]@TypeOf(const_array1){ const_array1, const_array2, const_array3 };

    const const_array_12 = try const_monoid.mappend(const_array1, const_array2);
    defer const_array_12.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37 }, const_array_12.t.items);

    const concated = try const_monoid.mconcat(consts);
    defer concated.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42, 37, 37, 13, 13, 13 }, concated.t.items);
}

fn ConstantApplicativeImpl(comptime T: type) type {
    return struct {
        monoid_impl: MonoidImpl,

        const Self = @This();
        const MonoidImpl = Monoid(T).InstanceImpl;

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = Constant(T);

        /// Get base type of Constant(T)(A), it is must just is A.
        pub fn BaseType(comptime ConstTA: type) type {
            return ConstTA.BaseType;
        }

        pub const Error: ?type = MonoidImpl.Error;

        pub const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub fn deinitFa(
            fa: anytype, // Maybe(A)
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
        ) void {
            _ = free_fn;
            fa.deinit();
        }

        pub fn fmap(
            self: *const Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            _ = self;
            if (!comptime isInplaceMap(K)) {
                @compileError("The Constant Functor only support inplace mode fmap!" ++ @tagName(K));
            }
            return .{ .t = fa.t };
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            if (!comptime isInplaceMap(K)) {
                @compileError("The Constant Functor only support inplace mode fmapLam!");
            }
            return .{ .t = fa.t };
        }

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            if (Error == null) {
                return .{ .t = self.monoid_impl.mempty() };
            } else {
                return .{ .t = try self.monoid_impl.mempty() };
            }
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // ff: F(*const fn (A) B),
            ff: anytype,
            fa: F(ApplyFnInType(Self, @TypeOf(ff))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
            if (Error == null) {
                return .{ .t = self.monoid_impl.mappend(ff.t, fa.t) };
            } else {
                return .{ .t = try self.monoid_impl.mappend(ff.t, fa.t) };
            }
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(ApplyLamInType(Self, @TypeOf(flam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
            if (Error == null) {
                return .{ .t = self.monoid_impl.mappend(flam.t, fa.t) };
            } else {
                return .{ .t = try self.monoid_impl.mappend(flam.t, fa.t) };
            }
        }
    };
}

test "Applicative Constant(T)(A) fmap and pure, fapply" {
    const allocator = testing.allocator;
    const ArrayMonoid = Monoid(ArrayList(u32));
    const array_monoid = ArrayMonoid.InstanceImpl{
        .allocator = allocator,
    };
    const ConstApplicative = Applicative(Constant(ArrayList(u32)));
    const const_applicative = ConstApplicative.InstanceImpl{
        .monoid_impl = array_monoid,
    };

    var array_m1: ArrayList(u32) = .init(allocator);
    var array_m2: ArrayList(u32) = .init(allocator);
    var array_m3: ArrayList(u32) = .init(allocator);

    const array1: [2]u32 = @splat(42);
    const array2: [2]u32 = @splat(37);
    const array3: [2]u32 = @splat(13);
    try array_m1.appendSlice(&array1);
    const const_array1 = Constant(ArrayList(u32))(u32){ .t = array_m1 };
    defer const_array1.deinit();
    try array_m2.appendSlice(&array2);
    const const_array2 = Constant(ArrayList(u32))(*Add_x_u32_Lam){ .t = array_m2 };
    defer const_array2.deinit();
    try array_m3.appendSlice(&array3);
    const const_array3 = Constant(ArrayList(u32))(u32){ .t = array_m3 };
    defer const_array3.deinit();

    const const_fmapped = try const_applicative.fmap(.InplaceMap, mul_pi_f64, const_array1);
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42 }, const_fmapped.t.items);
    const const_array_pure = try const_applicative.pure(18);
    defer const_array_pure.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{}, const_array_pure.t.items);
    const const_array_ff = try const_applicative.pure(&mul_pi_f64);
    const const_array_01 = try const_applicative.fapply(const_array_ff, const_array1);
    defer const_array_01.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 42, 42 }, const_array_01.t.items);
    const const_array_23 = try const_applicative.fapplyLam(const_array2, const_array3);
    defer const_array_23.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 37, 37, 13, 13 }, const_array_23.t.items);
}

/// A newtype wrapper for bool, just is
/// `newtype All = All { getAll :: Bool }`
/// in Haskell.
pub const AllBool = packed struct {
    b: bool,

    const Self = @This();
    pub const SemiGroupImpl = BoolMonoidImpl(Self, .And);
    pub const MonoidImpl = BoolMonoidImpl(Self, .And);

    pub fn fromBool(b: bool) Self {
        return @bitCast(b);
    }

    pub fn toBool(self: Self) bool {
        return @bitCast(self);
    }
};

/// A newtype wrapper for bool, just is
/// `newtype Any = Any { getAny :: Bool }`
/// in Haskell.
pub const AnyBool = packed struct {
    b: bool,

    const Self = @This();
    pub const SemiGroupImpl = BoolMonoidImpl(Self, .Or);
    pub const MonoidImpl = BoolMonoidImpl(Self, .Or);

    pub fn fromBool(b: bool) Self {
        return @bitCast(b);
    }

    pub fn toBool(self: Self) bool {
        return @bitCast(self);
    }
};

const BoolOp = enum {
    And,
    Or,
};

fn BoolMonoidImpl(comptime BoolM: type, boolop: BoolOp) type {
    return struct {
        const Self = @This();
        pub const Error: ?type = null;
        pub const M = BoolM;
        pub const EM = BoolM;

        const bool_unit = switch (boolop) {
            .And => true,
            .Or => false,
        };
        const fromBool = BoolM.fromBool;
        const toBool = BoolM.toBool;

        pub fn mempty(self: *const Self) EM {
            _ = self;
            return BoolM.fromBool(bool_unit);
        }

        pub fn mappend(self: *const Self, a: M, b: M) EM {
            _ = self;
            return switch (boolop) {
                .And => fromBool(toBool(a) and toBool(b)),
                .Or => fromBool(toBool(a) or toBool(b)),
            };
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            _ = self;
            var acc: bool = bool_unit;
            for (xs) |x| {
                switch (boolop) {
                    .And => acc = acc and toBool(x),
                    .Or => acc = acc or toBool(x),
                }
            }
            return fromBool(acc);
        }
    };
}

test "Monoid Any and All mempty and mappend" {
    const AllMonoid = Monoid(AllBool);
    const all_monoid = AllMonoid.InstanceImpl{};
    const all_0 = all_monoid.mempty();
    try testing.expectEqual(true, all_0.toBool());

    const all_1 = AllBool.fromBool(false);
    const all_2 = AllBool.fromBool(true);
    try testing.expectEqual(false, all_monoid.mappend(all_0, all_1).toBool());
    try testing.expectEqual(false, all_monoid.mappend(all_1, all_2).toBool());

    const AnyMonoid = Monoid(AnyBool);
    const any_monoid = AnyMonoid.InstanceImpl{};
    const any_0 = any_monoid.mempty();
    try testing.expectEqual(false, any_0.toBool());

    const any_1 = AnyBool.fromBool(false);
    const any_2 = AnyBool.fromBool(true);
    try testing.expectEqual(false, any_monoid.mappend(any_0, any_1).toBool());
    try testing.expectEqual(true, any_monoid.mappend(any_1, any_2).toBool());
}

test "Monoid Any and All mconcat" {
    const AllMonoid = Monoid(AllBool);
    const all_monoid = AllMonoid.InstanceImpl{};
    const AnyMonoid = Monoid(AnyBool);
    const any_monoid = AnyMonoid.InstanceImpl{};

    const Array4Functor = Functor(Array(4));
    const array4_functor = Array4Functor.InstanceImpl{};

    const bools = [_]bool{ false, true, true, false };
    const all_bools = array4_functor.fmap(.NewValMap, AllBool.fromBool, bools);
    const all_concated = all_monoid.mconcat(&all_bools);
    try testing.expectEqual(false, all_concated.toBool());

    const any_bools = array4_functor.fmap(.NewValMap, AnyBool.fromBool, bools);
    const any_concated = any_monoid.mconcat(&any_bools);
    try testing.expectEqual(true, any_concated.toBool());
}

/// A newtype wrapper for number, just is
/// `newtype Sum a = Sum { getSum :: a }`
/// in Haskell.
/// The type Numb should be a number or a function pointer `*const fn (Numb) Numb`.
pub fn SumNumb(comptime Numb: type) type {
    return SumOrProductNumb(Numb, .Add);
}

/// A newtype wrapper for number, just is
/// `newtype Product a = Product { getProduct :: a }`
/// in Haskell.
/// The value a should be a number or a function pointer `*const fn (Numb) Numb`.
pub fn ProductNumb(comptime Numb: type) type {
    return SumOrProductNumb(Numb, .Mul);
}

const NumbOp = enum {
    Add,
    Mul,
};

fn isNumberType(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float, .comptime_int, .comptime_float => true,
        .vector => |vec_info| switch (@typeInfo(vec_info.child)) {
            .int, .float, .comptime_int, .comptime_float => true,
            else => false,
        },
        else => false,
    };
}

fn SumOrProductNumb(comptime Numb: type, comptime numbop: NumbOp) type {
    const info = @typeInfo(Numb);

    // Check if the type Numb is a valid number type.
    switch (info) {
        .void, .int, .float, .comptime_int, .comptime_float => {},
        .vector => |vec_info| {
            // If the element is a number then vector is a number.
            switch (@typeInfo(vec_info.child)) {
                .int, .float, .comptime_int, .comptime_float => {},
                else => @compileError("It is must be a number vector in SumNumb/ProductNumb"),
            }
        },
        .pointer => {
            // If the ponter is point to a function or a lambda that parameter and return
            // value is a number, then it is a number.
            const ChildType = info.pointer.child;
            switch (@typeInfo(ChildType)) {
                .@"fn" => if (!(isNumberType(MapFnInType(ChildType)) and
                    isNumberType(MapFnRetType(ChildType))))
                {
                    @compileError("Expected a function `fn (Numb a) Numb b`, found type `" ++ @typeName(ChildType) ++ "`");
                } else {},
                .@"struct" => if (!(isNumberType(MapLamInType(ChildType)) and
                    isNumberType(MapLamRetType(ChildType))))
                {
                    @compileError("Expected a lambda with function `fn (Numb a) Numb b`, found type `" ++ @typeName(ChildType) ++ "`");
                } else {},
                else => @compileError("SumNumb/ProductNumb only support pointer of function and lambda"),
            }
        },
        else => @compileError("SumNumb/ProductNumb is not accept non-number type: " ++ @typeName(Numb)),
    }

    return packed struct {
        /// The numb should be a number or a function pointer `*const fn (Numb) Numb`.
        numb: Numb,

        const Self = @This();
        const NumbF = switch (numbop) {
            .Add => SumNumb,
            .Mul => ProductNumb,
        };
        pub const NumbType = Numb;

        pub const SemiGroupImpl = NumbMonoidImpl(Self, numbop);
        pub const MonoidImpl = NumbMonoidImpl(Self, numbop);
        pub const FunctorImpl = NumbMonadImpl(NumbF);
        pub const ApplicativeImpl = NumbMonadImpl(NumbF);
        pub const MonadImpl = NumbMonadImpl(NumbF);

        pub fn fromNumb(numb: Numb) Self {
            if (@typeInfo(Numb) == .pointer) return @bitCast(@intFromPtr(numb));
            return @bitCast(numb);
        }

        pub fn toNumb(self: Self) Numb {
            if (@typeInfo(Numb) == .pointer) return @ptrFromInt(@as(usize, @bitCast(self)));
            return @bitCast(self);
        }
    };
}

fn NumbMonoidImpl(comptime NumbM: type, numbop: NumbOp) type {
    return struct {
        const Self = @This();
        pub const Error: ?type = null;
        pub const M = NumbM;
        pub const EM = NumbM;

        const NumbType = NumbM.NumbType;
        const numb_0: NumbType = switch (@typeInfo(NumbType)) {
            .int, .float, .comptime_int, .comptime_float => 0,
            .vector => @splat(0),
            else => @compileError("Can not set 0 to type `" ++ @typeName(NumbType) ++ "`"),
        };

        const numb_1: NumbType = switch (@typeInfo(NumbType)) {
            .int, .float, .comptime_int, .comptime_float => 1,
            .vector => @splat(1),
            else => @compileError("Can not set 1 to type `" ++ @typeName(NumbType) ++ "`"),
        };

        const numb_unit = switch (numbop) {
            .Add => numb_0,
            .Mul => numb_1,
        };
        const fromNumb = NumbM.fromNumb;
        const toNumb = NumbM.toNumb;
        pub fn mempty(self: *const Self) EM {
            _ = self;
            return NumbM.fromNumb(numb_unit);
        }

        pub fn mappend(self: *const Self, a: M, b: M) EM {
            _ = self;
            return switch (numbop) {
                .Add => fromNumb(toNumb(a) + toNumb(b)),
                .Mul => fromNumb(toNumb(a) * toNumb(b)),
            };
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            _ = self;
            var acc: NumbType = numb_unit;
            for (xs) |x| {
                switch (numbop) {
                    .Add => acc += toNumb(x),
                    .Mul => acc *= toNumb(x),
                }
            }
            return fromNumb(acc);
        }
    };
}

test "Monoid SumNumb and ProductNumb mempty and mappend" {
    // test sum number
    const SumMonoid = Monoid(SumNumb(u16));
    const sum_monoid = SumMonoid.InstanceImpl{};
    const sum_0 = sum_monoid.mempty();
    try testing.expectEqual(0, sum_0.toNumb());
    const sum_1 = SumNumb(u16).fromNumb(42);
    const sum_2 = SumNumb(u16).fromNumb(37);
    try testing.expectEqual(42, sum_monoid.mappend(sum_0, sum_1).toNumb());
    try testing.expectEqual(79, sum_monoid.mappend(sum_1, sum_2).toNumb());

    // test sum vector number
    const Vec4xU16 = @Vector(4, u16);
    const SumVecMonoid = Monoid(SumNumb(Vec4xU16));
    const sum_vec_monoid = SumVecMonoid.InstanceImpl{};
    const sum_vec_0 = sum_vec_monoid.mempty();
    try testing.expectEqual(Vec4xU16{ 0, 0, 0, 0 }, sum_vec_0.toNumb());
    const sum_vec_1 = SumNumb(Vec4xU16).fromNumb(Vec4xU16{ 9, 7, 3, 5 });
    const sum_vec_2 = SumNumb(Vec4xU16).fromNumb(Vec4xU16{ 2, 8, 5, 4 });
    try testing.expectEqual(
        Vec4xU16{ 9, 7, 3, 5 },
        sum_vec_monoid.mappend(sum_vec_0, sum_vec_1).toNumb(),
    );
    try testing.expectEqual(
        Vec4xU16{ 11, 15, 8, 9 },
        sum_vec_monoid.mappend(sum_vec_1, sum_vec_2).toNumb(),
    );

    // test product number
    const ProductMonoid = Monoid(ProductNumb(u16));
    const product_monoid = ProductMonoid.InstanceImpl{};
    const product_0 = product_monoid.mempty();
    try testing.expectEqual(1, product_0.toNumb());
    const product_1 = ProductNumb(u16).fromNumb(12);
    const product_2 = ProductNumb(u16).fromNumb(25);
    try testing.expectEqual(12, product_monoid.mappend(product_0, product_1).toNumb());
    try testing.expectEqual(300, product_monoid.mappend(product_1, product_2).toNumb());

    // test product vector number
    const ProductVecMonoid = Monoid(ProductNumb(Vec4xU16));
    const product_vec_monoid = ProductVecMonoid.InstanceImpl{};
    const product_vec_0 = product_vec_monoid.mempty();
    try testing.expectEqual(Vec4xU16{ 1, 1, 1, 1 }, product_vec_0.toNumb());
    const product_vec_1 = ProductNumb(Vec4xU16).fromNumb(Vec4xU16{ 9, 7, 3, 5 });
    const product_vec_2 = ProductNumb(Vec4xU16).fromNumb(Vec4xU16{ 2, 8, 5, 4 });
    try testing.expectEqual(
        Vec4xU16{ 9, 7, 3, 5 },
        product_vec_monoid.mappend(product_vec_0, product_vec_1).toNumb(),
    );
    try testing.expectEqual(
        Vec4xU16{ 18, 56, 15, 20 },
        product_vec_monoid.mappend(product_vec_1, product_vec_2).toNumb(),
    );
}

test "Monoid SumNumb and ProductNumb mconcat" {
    // test sum/product number
    const SumMonoid = Monoid(SumNumb(u16));
    const sum_monoid = SumMonoid.InstanceImpl{};
    const ProductMonoid = Monoid(ProductNumb(u16));
    const product_monoid = ProductMonoid.InstanceImpl{};

    const Array4Functor = Functor(Array(4));
    const array4_functor = Array4Functor.InstanceImpl{};

    const numbs = [_]u16{ 7, 13, 17, 23 };
    const sum_numbs = array4_functor.fmap(.NewValMap, SumNumb(u16).fromNumb, numbs);
    const sum_concated = sum_monoid.mconcat(&sum_numbs);
    try testing.expectEqual(60, sum_concated.toNumb());

    const product_numbs = array4_functor.fmap(.NewValMap, ProductNumb(u16).fromNumb, numbs);
    const product_concated = product_monoid.mconcat(&product_numbs);
    try testing.expectEqual(35581, product_concated.toNumb());

    // test sum/product vector number
    const Vec4xU16 = @Vector(4, u16);
    const SumVecMonoid = Monoid(SumNumb(Vec4xU16));
    const sum_vec_monoid = SumVecMonoid.InstanceImpl{};
    const ProductVecMonoid = Monoid(ProductNumb(Vec4xU16));
    const product_vec_monoid = ProductVecMonoid.InstanceImpl{};

    const numb_vecs = [_]Vec4xU16{
        Vec4xU16{ 2, 3, 4, 5 },
        Vec4xU16{ 5, 4, 3, 2 },
        Vec4xU16{ 3, 5, 7, 9 },
        Vec4xU16{ 9, 7, 5, 3 },
    };
    const sum_vec_numbs = array4_functor.fmap(.NewValMap, SumNumb(Vec4xU16).fromNumb, numb_vecs);
    const sum_vec_concated = sum_vec_monoid.mconcat(&sum_vec_numbs);
    try testing.expectEqual(Vec4xU16{ 19, 19, 19, 19 }, sum_vec_concated.toNumb());

    const product_vec_numbs = array4_functor.fmap(.NewValMap, ProductNumb(Vec4xU16).fromNumb, numb_vecs);
    const product_vec_concated = product_vec_monoid.mconcat(&product_vec_numbs);
    try testing.expectEqual(Vec4xU16{ 270, 420, 420, 270 }, product_vec_concated.toNumb());
}

fn NumbMonadImpl(comptime NumbF: TCtor) type {
    return struct {
        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = NumbF;

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime NumbM: type) type {
            return NumbM.NumbType;
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
            _ = free_fn;
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
            const b = if (comptime isMapRef(K))
                map_fn(&(fa.*.toNumb()))
            else
                map_fn(fa.toNumb());
            return if (has_err) try F(B).fromNumb(b) else F(B).fromNumb(b);
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
            const b = if (comptime isMapRef(K))
                map_lam.call(&(fa.*.toNumb()))
            else
                map_lam.call(fa.toNumb());
            return if (has_err) try F(B).fromNumb(b) else F(B).fromNumb(b);
        }

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            _ = self;
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            return if (has_err) try F(_A).fromNumb(a) else F(_A).fromNumb(a);
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // ff: F(*const fn (A) B),
            ff: anytype,
            fa: F(ApplyFnInType(Self, @TypeOf(ff))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
            _ = self;
            const B = ApplyFnRetType(Self, @TypeOf(ff));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const f = ff.toNumb();
            const a = fa.toNumb();
            const b = f(a);
            return if (has_err) try F(_B).fromNumb(b) else F(_B).fromNumb(b);
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(ApplyLamInType(Self, @TypeOf(flam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
            _ = self;
            const B = ApplyLamRetType(Self, @TypeOf(flam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const lam = flam.toNumb();
            const a = fa.toNumb();
            const b = lam.call(a);
            return if (has_err) try F(_B).fromNumb(b) else F(_B).fromNumb(b);
        }

        pub fn bind(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*const Self, A) MbType(B),
        ) MbType(B) {
            const a = ma.toNumb();
            return k(self, a);
        }

        pub fn bindLam(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            klam: anytype,
        ) MbType(B) {
            const a = ma.toNumb();
            return klam.call(self, a);
        }
    };
}

// These functions are used for unit test
const add10 = testu.add10;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const Add_x_u32_Lam = testu.Add_x_u32_Lam;
const Add_x_f64_Lam = testu.Add_x_f64_Lam;
const Mul_x_f64_Lam = testu.Mul_x_f64_Lam;

const ARRAY_LEN = 4;
const ArrayF = Array(ARRAY_LEN);

test "SumNumb and ProductNumb Functor fmap/fmapLam" {
    const SumFunctor = Functor(SumNumb);
    const sum_functor = SumFunctor.InstanceImpl{};
    const ProductFunctor = Functor(ProductNumb);
    const product_functor = ProductFunctor.InstanceImpl{};

    const sum_u32 = SumNumb(u32).fromNumb(42);
    var sum_f64 = sum_functor.fmap(.NewValMap, add_pi_f64, sum_u32);
    try testing.expectEqual(45.14, sum_f64.toNumb());

    const add_pi_lam = Add_x_f64_Lam{ ._x = 3.14 };
    sum_f64 = sum_functor.fmapLam(.NewValMap, add_pi_lam, sum_u32);
    try testing.expectEqual(45.14, sum_f64.toNumb());

    const product_u32 = ProductNumb(u32).fromNumb(42);
    var product_f64 = product_functor.fmap(.NewValMap, mul_pi_f64, product_u32);
    try testing.expectEqual(131.88, product_f64.toNumb());

    const mul_pi_lam = Mul_x_f64_Lam{ ._x = 3.14 };
    product_f64 = product_functor.fmapLam(.NewValMap, mul_pi_lam, product_u32);
    try testing.expectEqual(131.88, product_f64.toNumb());

    // The test case for vector number is not necessary, because fmap f = fapply (pure f)
}

const Vec4xU32 = @Vector(4, u32);
const Vec4xF64 = @Vector(4, f64);

fn vec_add10(v: Vec4xU32) Vec4xU32 {
    return v + @as(Vec4xU32, @splat(10));
}

fn vec_add_pi_f64(v: Vec4xU32) Vec4xF64 {
    return @as(Vec4xF64, @floatFromInt(v)) + @as(Vec4xF64, @splat(3.14));
}

fn vec_mul_pi_f64(v: Vec4xU32) Vec4xF64 {
    return @as(Vec4xF64, @floatFromInt(v)) * @as(Vec4xF64, @splat(3.14));
}

test "SumNumb and ProductNumb Applicative pure and fapply/fapplyLam" {
    // test sum/product number
    const SumApplicative = Applicative(SumNumb);
    const sum_applicative = SumApplicative.InstanceImpl{};
    const ProductApplicative = Applicative(ProductNumb);
    const product_applicative = ProductApplicative.InstanceImpl{};

    const sum_u32 = sum_applicative.pure(@as(u32, 42));
    const sum_add10 = sum_applicative.pure(&add10);
    var sum_added = sum_applicative.fapply(sum_add10, sum_u32);
    try testing.expectEqual(52, sum_added.toNumb());
    const sum_add_pi = sum_applicative.pure(&add_pi_f64);
    var sum_f64 = sum_applicative.fapply(sum_add_pi, sum_u32);
    try testing.expectEqual(45.14, sum_f64.toNumb());

    const add10_lam = Add_x_u32_Lam{ ._x = 10 };
    const sum_add10_lam = sum_applicative.pure(&add10_lam);
    sum_added = sum_applicative.fapplyLam(sum_add10_lam, sum_u32);
    try testing.expectEqual(52, sum_added.toNumb());
    const add_pi_lam = Add_x_f64_Lam{ ._x = 3.14 };
    const sum_add_pi_lam = sum_applicative.pure(&add_pi_lam);
    sum_f64 = sum_applicative.fapplyLam(sum_add_pi_lam, sum_u32);
    try testing.expectEqual(45.14, sum_f64.toNumb());

    const product_u32 = product_applicative.pure(@as(u32, 42));
    const product_mul_pi = product_applicative.pure(&mul_pi_f64);
    var product_f64 = product_applicative.fapply(product_mul_pi, product_u32);
    try testing.expectEqual(131.88, product_f64.toNumb());

    const mul_pi_lam = Mul_x_f64_Lam{ ._x = 3.14 };
    const product_mul_pi_lam = product_applicative.pure(&mul_pi_lam);
    product_f64 = product_applicative.fapplyLam(product_mul_pi_lam, product_u32);
    try testing.expectEqual(131.88, product_f64.toNumb());

    // test sum/product vector number
    const SumVecApplicative = Applicative(SumNumb);
    const sum_vec_applicative = SumVecApplicative.InstanceImpl{};
    const ProductVecApplicative = Applicative(ProductNumb);
    const product_vec_applicative = ProductVecApplicative.InstanceImpl{};

    const sum_vec_u32 = sum_vec_applicative.pure(@as(Vec4xU32, @splat(42)));
    const sum_vec_add10 = sum_vec_applicative.pure(&vec_add10);
    var sum_vec_added = sum_vec_applicative.fapply(sum_vec_add10, sum_vec_u32);
    try testing.expectEqual(@as(Vec4xU32, @splat(52)), sum_vec_added.toNumb());
    const sum_vec_add_pi = sum_vec_applicative.pure(&vec_add_pi_f64);
    var sum_vec_f64 = sum_vec_applicative.fapply(sum_vec_add_pi, sum_vec_u32);
    try testing.expectEqual(@as(Vec4xF64, @splat(45.14)), sum_vec_f64.toNumb());

    const product_vec_u32 = product_vec_applicative.pure(@as(Vec4xU32, @splat(42)));
    const product_vec_mul_pi = product_vec_applicative.pure(&vec_mul_pi_f64);
    var product_vec_f64 = product_vec_applicative.fapply(product_vec_mul_pi, product_vec_u32);
    try testing.expectEqual(@as(Vec4xF64, @splat(131.88)), product_vec_f64.toNumb());
}

const SumImpl = NumbMonadImpl(SumNumb);
fn sum_add10_k(impl: *const SumImpl, a: u32) SumNumb(u32) {
    _ = impl;
    return SumNumb(u32).fromNumb(a + 10);
}

fn sum_vec_add10_k(impl: *const SumImpl, a: Vec4xU32) SumNumb(Vec4xU32) {
    _ = impl;
    return SumNumb(Vec4xU32).fromNumb(a + @as(Vec4xU32, @splat(10)));
}

const Sum_mul_f64_Klam = struct {
    _x: f64,
    const Self = @This();
    pub fn call(self: *const Self, impl: *const SumImpl, a: u32) SumNumb(f64) {
        _ = impl;
        return SumNumb(f64).fromNumb(@as(f64, @floatFromInt(a)) * self._x);
    }
};

const ProductImpl = NumbMonadImpl(ProductNumb);
fn product_add10_k(impl: *const ProductImpl, a: u32) ProductNumb(u32) {
    _ = impl;
    return ProductNumb(u32).fromNumb(a + 10);
}

fn product_vec_add10_k(impl: *const ProductImpl, a: Vec4xU32) ProductNumb(Vec4xU32) {
    _ = impl;
    return ProductNumb(Vec4xU32).fromNumb(a + @as(Vec4xU32, @splat(10)));
}

const Product_mul_f64_Klam = struct {
    _x: f64,
    const Self = @This();
    pub fn call(self: *const Self, impl: *const ProductImpl, a: u32) ProductNumb(f64) {
        _ = impl;
        return ProductNumb(f64).fromNumb(@as(f64, @floatFromInt(a)) * self._x);
    }
};

test "SumNumb and ProductNumb Monad bind/bindLam" {
    // test sum/product number
    const SumMonad = Monad(SumNumb);
    const sum_monad = SumMonad.InstanceImpl{};
    const ProductMonad = Monad(ProductNumb);
    const product_monad = ProductMonad.InstanceImpl{};

    const sum_u32 = sum_monad.pure(@as(u32, 42));
    var sum_added = sum_monad.bind(u32, u32, sum_u32, sum_add10_k);
    try testing.expectEqual(52, sum_added.toNumb());
    const sum_mul_pi_klam = Sum_mul_f64_Klam{ ._x = 3.14 };
    var sum_f64 = sum_monad.bindLam(u32, f64, sum_u32, sum_mul_pi_klam);
    try testing.expectEqual(131.88, sum_f64.toNumb());

    const product_u32 = product_monad.pure(@as(u32, 42));
    var product_added = product_monad.bind(u32, u32, product_u32, product_add10_k);
    try testing.expectEqual(52, product_added.toNumb());
    const product_mul_pi_klam = Product_mul_f64_Klam{ ._x = 3.14 };
    var product_f64 = product_monad.bindLam(u32, f64, product_u32, product_mul_pi_klam);
    try testing.expectEqual(131.88, product_f64.toNumb());

    // test sum/product vector number
    const SumVecMonad = Monad(SumNumb);
    const sum_vec_monad = SumVecMonad.InstanceImpl{};
    const ProductVecMonad = Monad(ProductNumb);
    const product_vec_monad = ProductVecMonad.InstanceImpl{};

    const sum_vec_u32 = sum_vec_monad.pure(@as(Vec4xU32, @splat(42)));
    var sum_vec_added = sum_vec_monad.bind(Vec4xU32, Vec4xU32, sum_vec_u32, sum_vec_add10_k);
    try testing.expectEqual(@as(Vec4xU32, @splat(52)), sum_vec_added.toNumb());

    const product_vec_u32 = product_vec_monad.pure(@as(Vec4xU32, @splat(42)));
    var product_vec_added = product_vec_monad.bind(Vec4xU32, Vec4xU32, product_vec_u32, product_vec_add10_k);
    try testing.expectEqual(@as(Vec4xU32, @splat(52)), product_vec_added.toNumb());
}
