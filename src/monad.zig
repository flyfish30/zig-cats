const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

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
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;

pub fn MonadFxTypes(comptime F: TCtor, comptime E: type) type {
    return struct {
        /// return type of bind
        pub fn MbType(comptime B: type) type {
            return E!F(B);
        }
    };
}

/// Monad typeclass like in Haskell, it inherit from Applicative Functor.
/// M is instance of Monad typeclass, such as Maybe, List
pub fn Monad(comptime MonadImpl: type) type {
    const M = MonadImpl.F;
    const has_sup_impl = @hasField(MonadImpl, "applicative_sup");

    return struct {
        const Self = @This();
        pub const InstanceImpl = MonadImpl;
        const ApplicativeSup = if (has_sup_impl)
            Applicative(InstanceImpl.SupImpl)
        else
            Applicative(InstanceImpl);

        pub const Error = InstanceImpl.Error;
        pub const MbType = InstanceImpl.MbType;

        const BindType = @TypeOf(struct {
            fn bindFn(
                instance: *InstanceImpl,
                comptime A: type,
                comptime B: type,
                // monad function: (a -> M b), ma: M a
                ma: M(A),
                f: *const fn (*InstanceImpl, A) MbType(B),
            ) MbType(B) {
                _ = instance;
                _ = ma;
                _ = f;
            }
        }.bindFn);

        pub fn init(instance: InstanceImpl) InstanceImpl {
            var inst: InstanceImpl = undefined;

            if (has_sup_impl) {
                const sup = ApplicativeSup.init(instance.applicative_sup);
                inst = instance;
                inst.applicative_sup = sup;
            } else {
                inst = ApplicativeSup.init(instance);
            }

            if (@TypeOf(InstanceImpl.bind) != BindType) {
                @compileError("Incorrect type of bind for Monad instance " ++ @typeName(InstanceImpl));
            }
            return inst;
        }
    };
}

const Maybe = base.Maybe;

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
        comptime free_fn: fn (BaseType(@TypeOf(fa))) void,
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
        const has_err, const B = isErrorUnionOrVal(MapFnRetType(MapFn));
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
        self: *Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        _ = self;
        const MapLam = @TypeOf(map_lam);
        const has_err, const B = isErrorUnionOrVal(MapLamRetType(MapLam));
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
        return a;
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
        const has_err, const _B = isErrorUnionOrVal(B);
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
        const has_err, const _B = isErrorUnionOrVal(B);
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
        f: *const fn (*Self, A) MbType(B),
    ) MbType(B) {
        if (ma) |a| {
            return f(self, a);
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

const add_pi_f32 = struct {
    fn f(a: u32) f32 {
        return @as(f32, @floatFromInt(a)) + 3.14;
    }
}.f;

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

    const bind_fn = &struct {
        fn f(self: *MaybeMonadImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = self;
            if (x == 3.14) {
                return null;
            } else {
                return @intFromFloat(@floor(x * 4.0));
            }
        }
    }.f;

    var maybe_a: ?f64 = null;
    var maybe_b = try maybe_monad.bind(f64, u32, maybe_a, bind_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 3.14;
    maybe_b = try maybe_monad.bind(f64, u32, maybe_a, bind_fn);
    try testing.expectEqual(null, maybe_b);

    maybe_a = 8.0;
    maybe_b = try maybe_monad.bind(f64, u32, maybe_a, bind_fn);
    try testing.expectEqual(32, maybe_b);
}

pub const ArrayListMonadImpl = struct {
    allocator: Allocator,

    const Self = @This();

    const ARRAY_DEFAULT_LEN = 4;

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = ArrayList;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime ArrayA: type) type {
        return std.meta.Child(ArrayA.Slice);
    }

    pub const Error = Allocator.Error;

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
        comptime free_fn: fn (BaseType(@TypeOf(fa))) void,
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
        self: *Self,
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
        self: *Self,
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
        self: *Self,
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

        const array = if (@typeInfo(@TypeOf(fa)) == .Pointer)
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
        self: *Self,
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

    pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
        var array = try ArrayList(@TypeOf(a)).initCapacity(self.allocator, ARRAY_DEFAULT_LEN);

        array.appendAssumeCapacity(a);
        return array;
    }

    pub fn fapply(
        self: *Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        ff: F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        return fapplyGeneric(self, .NormalMap, A, B, ff, fa);
    }

    pub fn fapplyLam(
        self: *Self,
        comptime A: type,
        comptime B: type,
        // applicative function: F (a -> b), fa: F a
        flam: anytype, // a F(lambda) that present F(*const fn (A) B),
        fa: F(A),
    ) AFbType(B) {
        return fapplyGeneric(self, .LambdaMap, A, B, flam, fa);
    }

    fn fapplyGeneric(
        self: *Self,
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
        self: *Self,
        comptime A: type,
        comptime B: type,
        // monad function: (a -> M b), ma: M a
        ma: F(A),
        f: *const fn (*Self, A) MbType(B),
    ) MbType(B) {
        var mb = ArrayList(B).init(self.allocator);
        for (ma.items) |a| {
            const tmp_mb = try f(self, a);
            defer tmp_mb.deinit();
            for (tmp_mb.items) |b| {
                try mb.append(b);
            }
        }
        return mb;
    }
};

test "ArrayList Functor fmap" {
    const allocator = testing.allocator;
    const ArrayListFunctor = Functor(ArrayListMonadImpl);
    var array_functor = ArrayListFunctor.init(.{ .allocator = allocator });

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
    const ArrayListApplicative = Applicative(ArrayListMonadImpl);
    var array_applicative = ArrayListApplicative.init(.{ .allocator = allocator });

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
    const ArrayListMonad = Monad(ArrayListMonadImpl);
    var array_monad = ArrayListMonad.init(.{ .allocator = allocator });

    var array_a = ArrayList(f64).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]f64{ 10, 20, 30, 40 });
    const array_binded = try array_monad.bind(f64, u32, array_a, struct {
        fn f(inst: *@TypeOf(array_monad), a: f64) ArrayListMonad.MbType(u32) {
            var arr_b = try ArrayList(u32).initCapacity(inst.allocator, 2);
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 4.0)));
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 9.0)));
            return arr_b;
        }
    }.f);
    defer array_binded.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 40, 90, 80, 180, 120, 270, 160, 360 }, array_binded.items);
}
