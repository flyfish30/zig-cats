const std = @import("std");
const base = @import("base.zig");
const semi_grp = @import("semigroup.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const testu = @import("test_utils.zig");
const maybe = @import("maybe.zig");
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
const mapFnToLam = base.mapFnToLam;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const isErrorUnionOrVal = base.isErrorUnionOrVal;
const maybe_error = maybe.maybe_error;

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
        pub const Error = Functor(F).InstanceImpl.Error;
    };
}

/// A alg function type, just is
/// `type Alg f a = f a -> a`
/// in Haskell
pub fn Alg(comptime F: TCtor, comptime A: type, comptime E: ?type) type {
    const EA = if (E == null) A else E.?!A;
    return *const fn (F(A)) EA;
}

fn CataAlgLam(
    comptime cfg: anytype,
    comptime AlgType: type,
    comptime F: TCtor,
    comptime A: type,
    comptime E: ?type,
) type {
    return struct {
        functor_impl: *const FImpl,
        // alg lambda with function: Alg(F, A, E),
        alg: AlgType,

        const Self = @This();
        const FImpl = Functor(F).InstanceImpl;
        const Error = maybe_error.mappend(E, FImpl.Error);
        const EA = if (Error == null) A else Error.?!A;
        pub fn call(self: *const Self, fix: Fix(cfg, F)) EA {
            if (Error == null) {
                return self.alg.call(self.functor_impl.fmapLam(.NewValMap, self, fix.fixed.*));
            } else {
                return self.alg.call(try self.functor_impl.fmapLam(.NewValMap, self, fix.fixed.*));
            }
        }
    };
}

fn CataRetType(comptime FImplPtr: type, comptime AlgType: type, comptime FixType: type) type {
    const AlgInType = MapLamInType(AlgType);
    const AlgRetType = MapLamRetType(AlgType);
    const has_err, const A = isErrorUnionOrVal(AlgRetType);
    const E: ?type = if (has_err) @typeInfo(AlgRetType).error_union.error_set else null;

    if (@typeInfo(FImplPtr) != .pointer) {
        @compileError("Expect FImplPtr is *const Functor(F).InstanceImpl, found `" ++ @typeName(FImplPtr) ++ "`");
    }
    const F = std.meta.Child(FImplPtr).F;
    std.debug.assert(F(A) == AlgInType);
    std.debug.assert(Fix(FixType.cfg, F) == FixType);

    const Error = maybe_error.mappend(E, FixType.Error);
    const EA = if (Error == null) A else Error.?!A;
    return EA;
}

/// A cata function, just is
/// ```
/// cata :: Functor f => Alg f a -> Fix f -> a
/// cata alg = alg . fmap (cata alg) . unFix
/// ```
/// in Haskell
/// type of parameter f_impl is: *const Functor(F).InstanceImpl,
/// type of parameter alg is lambda with function: Alg(F, A, E),
/// type of parameter fix is: Fix(cfg, F)
pub fn cata(
    f_impl: anytype, // type is *const Functor(F).InstanceImpl,
    alg: anytype, // type is lambda with function: Alg(F, A, E),
    fix: anytype, // type is Fix(cfg, F)
) CataRetType(@TypeOf(f_impl), @TypeOf(alg), @TypeOf(fix)) {
    const FImplPtr = @TypeOf(f_impl);
    const AlgType = @TypeOf(alg);
    const FixType = @TypeOf(fix);
    const RetType = CataRetType(FImplPtr, AlgType, FixType);
    const has_err, const A = isErrorUnionOrVal(RetType);
    const F = FixType.FunF;
    const E: ?type = if (has_err) @typeInfo(RetType).error_union.error_set else null;
    const cata_alg = CataAlgLam(FixType.cfg, AlgType, F, A, E){ .functor_impl = f_impl, .alg = alg };

    if (E == null) {
        return alg.call(f_impl.fmapLam(.NewValMap, cata_alg, fix.fixed.*));
    } else {
        return alg.call(try f_impl.fmapLam(.NewValMap, cata_alg, fix.fixed.*));
    }
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

const ArrayList = std.ArrayList;

const ShowSimpleExprFLam = struct {
    show_str_ptr: *ArrayList(u8),

    const Self = @This();
    pub fn call(self: *const Self, exprf: SimpleExprF(ArrayList(u8))) !ArrayList(u8) {
        var show_str_ptr = self.show_str_ptr;
        switch (exprf) {
            .liti => |int| {
                const fmt_str = " {d} ";
                const count: usize = @intCast(std.fmt.count(fmt_str, .{int}));
                const buf = try show_str_ptr.addManyAsSlice(count);
                _ = std.fmt.bufPrint(buf, fmt_str, .{int}) catch unreachable;
                return show_str_ptr.*;
            },
            .add => |tuple| {
                const rhs_start = tuple[0].items.len;
                const rhs_end = tuple[1].items.len;
                const rhs_len = rhs_end - rhs_start;
                const fmt_str = " + ";
                const count: usize = @intCast(std.fmt.count(fmt_str, .{}));
                _ = try show_str_ptr.addManyAsSlice(count);
                // copy right hand operand to rightest of new str
                const new_len = show_str_ptr.items.len;
                std.mem.copyBackwards(
                    u8,
                    show_str_ptr.items[new_len - rhs_len .. new_len],
                    show_str_ptr.items[rhs_start..rhs_end],
                );
                const buf = show_str_ptr.items[rhs_start..][0..count];
                _ = std.fmt.bufPrint(buf, fmt_str, .{}) catch unreachable;
                return show_str_ptr.*;
            },
        }
    }
};

fn printSimpleExprF(exprf: SimpleExprF(void)) !void {
    return switch (exprf) {
        .liti => |int| std.debug.print(" {d} ", .{int}),
        .add => std.debug.print(" + ", .{}),
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
    const result = cata(&exprf_functor, mapFnToLam(evalSimpleExprF), expr);
    try testing.expectEqual(92, result);

    var show_array = ArrayList(u8).init(allocator);
    const show_exprf_lam = ShowSimpleExprFLam{ .show_str_ptr = &show_array };
    defer show_exprf_lam.show_str_ptr.*.deinit();
    const show_str = try cata(&exprf_functor, show_exprf_lam, expr);
    _ = show_str;
    try testing.expectEqualSlices(u8, " 42  +  37  +  13 ", show_array.items);

    try cata(&exprf_functor, mapFnToLam(printSimpleExprF), expr);
}
