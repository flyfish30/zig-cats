const std = @import("std");
const base = @import("base.zig");
const semi_grp = @import("semigroup.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const testu = @import("test_utils.zig");
const arraym = @import("array_monad.zig");

const testing = std.testing;
const Allocator = std.mem.Allocator;
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

const FunctorFxTypes = functor.FunctorFxTypes;

/// A fixed point type constructor, just is
/// `newtype Fix f = Fix { unFix :: f (Fix f)) }`
/// in Haskell.
pub fn Fix(comptime in_cfg: anytype, comptime F: TCtor) type {
    return struct {
        fixed: *F(Fix(in_cfg, F)),

        const Self = @This();
        pub const cfg = in_cfg;
        pub const FunF = F;
    };
}

/// A alg function type, just is
/// `type Alg f a = f a -> a`
/// in Haskell
pub fn Alg(comptime F: TCtor, comptime A: type) type {
    return *const fn (F(A)) A;
}

fn CataAlgLam(comptime cfg: anytype, comptime F: TCtor, comptime A: type) type {
    return struct {
        functor_impl: *const Functor(F).InstanceImpl,
        fix_alg: Alg(F, A),

        const Self = @This();
        pub fn call(self: *const Self, fix: Fix(cfg, F)) A {
            return self.fix_alg(self.functor_impl.fmapLam(.NewValMap, self, fix.fixed.*));
        }
    };
}

/// A cata function, just is
/// ```
/// cata :: Functor f => Alg f a -> Fix f -> a
/// cata alg = alg . fmap (cata alg) . unFix
/// ```
/// in Haskell
/// The type of fix parameter is Fix(cfg, F)
pub fn cata(
    comptime F: TCtor,
    comptime A: type,
    f_impl: *const Functor(F).InstanceImpl,
    alg: Alg(F, A),
    fix: anytype,
) A {
    const FixType = @TypeOf(fix);
    std.debug.assert(Fix(FixType.cfg, F) == FixType);
    const cata_alg = CataAlgLam(FixType.cfg, F, A){ .functor_impl = f_impl, .fix_alg = alg };
    return alg(f_impl.fmapLam(.NewValMap, cata_alg, fix.fixed.*));
}

fn SimpleExprF(comptime X: type) type {
    return union(enum) {
        liti: i32,
        add: struct { X, X },

        pub const FunctorImpl = SimpleExprFFunctorImpl;
        pub const BaseType = X;
    };
}

fn ExprCtx(comptime cfg: anytype) type {
    return struct {
        const SimpleExpr = Fix(cfg, SimpleExprF);

        fn liftLiti(int: i32) Allocator.Error!SimpleExpr {
            const exprf_liti = try cfg.allocator.create(SimpleExprF(SimpleExpr));
            exprf_liti.* = .{ .liti = int };
            return .{ .fixed = exprf_liti };
        }

        fn liftAdd(a: SimpleExpr, b: SimpleExpr) Allocator.Error!SimpleExpr {
            const exprf_add = try cfg.allocator.create(SimpleExprF(SimpleExpr));
            exprf_add.* = .{ .add = .{ a, b } };
            return .{ .fixed = exprf_add };
        }
    };
}

const SimpleExprFFunctorImpl = struct {
    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = SimpleExprF;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime ExprFA: type) type {
        return ExprFA.BaseType;
    }

    pub const Error: ?type = null;

    pub const FxTypes = FunctorFxTypes(F, Error);
    pub const FaType = FxTypes.FaType;
    pub const FbType = FxTypes.FbType;
    pub const FaLamType = FxTypes.FaLamType;
    pub const FbLamType = FxTypes.FbLamType;

    pub fn deinitFa(
        fa: anytype, // SimpleExprF(X)
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
        _ = B;
        if (comptime isMapRef(K)) {
            switch (fa.*) {
                .liti => |i| return .{ .liti = i },
                .add => |tuple| {
                    const a = map_fn(&tuple[0]);
                    const b = map_fn(&tuple[1]);
                    return .{ .add = .{
                        if (has_err) try a else a,
                        if (has_err) try b else b,
                    } };
                },
            }
        } else {
            switch (fa) {
                .liti => |i| return .{ .liti = i },
                .add => |tuple| {
                    const a = map_fn(tuple[0]);
                    const b = map_fn(tuple[1]);
                    return .{ .add = .{
                        if (has_err) try a else a,
                        if (has_err) try b else b,
                    } };
                },
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
        _ = B;
        if (comptime isMapRef(K)) {
            switch (fa.*) {
                .liti => |i| return .{ .liti = i },
                .add => |tuple| {
                    const a = map_lam.call(&tuple[0]);
                    const b = map_lam.call(&tuple[1]);
                    return .{ .add = .{
                        if (has_err) try a else a,
                        if (has_err) try b else b,
                    } };
                },
            }
        } else {
            switch (fa) {
                .liti => |i| return .{ .liti = i },
                .add => |tuple| {
                    const a = map_lam.call(tuple[0]);
                    const b = map_lam.call(tuple[1]);
                    return .{ .add = .{
                        if (has_err) try a else a,
                        if (has_err) try b else b,
                    } };
                },
            }
        }

        return null;
    }
};

fn deinitSimpleExpr(comptime cfg: anytype, fix: ExprCtx(cfg).SimpleExpr) void {
    return switch (fix.fixed.*) {
        .liti => cfg.allocator.destroy(fix.fixed),
        .add => |tuple| {
            deinitSimpleExpr(cfg, tuple[0]);
            deinitSimpleExpr(cfg, tuple[1]);
            cfg.allocator.destroy(fix.fixed);
        },
    };
}

fn evalSimpleExprF(exprf: SimpleExprF(i32)) i32 {
    return switch (exprf) {
        .liti => |int| int,
        .add => |tuple| tuple[0] + tuple[1],
    };
}

test "Fix(SimpleExprF) cata function" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);

    const ExprFFunctor = Functor(SimpleExprF);
    const exprf_functor = ExprFFunctor.InstanceImpl{};
    const liftLiti = ExprCtx(cfg).liftLiti;
    const liftAdd = ExprCtx(cfg).liftAdd;

    const expr = try liftAdd(
        try liftAdd(try liftLiti(42), try liftLiti(37)),
        try liftLiti(13),
    );
    defer deinitSimpleExpr(cfg, expr);
    const result = cata(SimpleExprF, i32, &exprf_functor, &evalSimpleExprF, expr);
    try testing.expectEqual(92, result);
}
