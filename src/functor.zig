const std = @import("std");
const base = @import("base.zig");
const applicative = @import("applicative.zig");

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;

const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

pub const MaybeFunctorImpl = applicative.MaybeApplicativeImpl;
pub const ArrayListFunctorImpl = applicative.ArrayListApplicativeImpl;

pub fn FunctorFxTypes(comptime F: TCtor, comptime E: ?type) type {
    return struct {
        pub fn FaType(comptime K: MapFnKind, comptime MapFn: type) type {
            if (comptime isMapRef(K)) {
                // The fa paramerter of fmap function is also a reference.
                return *F(std.meta.Child(MapFnInType(MapFn)));
            } else {
                return F(MapFnInType(MapFn));
            }
        }

        pub fn FbType(comptime MapFn: type) type {
            const info = @typeInfo(MapFnRetType(MapFn));
            if (E == null) {
                return F(MapFnRetType(MapFn));
            }

            const _E = E.?;
            if (info != .error_union) {
                return _E!F(MapFnRetType(MapFn));
            }

            return (_E || info.error_union.error_set)!F(info.error_union.payload);
        }

        pub fn FaLamType(comptime K: MapFnKind, comptime MapLam: type) type {
            if (comptime isMapRef(K)) {
                // The fa paramerter of fmapLam function is also a reference.
                return *F(std.meta.Child(MapLamInType(MapLam)));
            } else {
                return F(MapLamInType(MapLam));
            }
        }

        pub fn FbLamType(comptime MapLam: type) type {
            const info = @typeInfo((MapLamRetType(MapLam)));
            if (E == null) {
                return F(MapLamRetType(MapLam));
            }

            const _E = E.?;
            if (info != .error_union) {
                return _E!F(MapLamRetType(MapLam));
            }

            return (_E || info.error_union.error_set)!F(info.error_union.payload);
        }
    };
}

/// Functor typeclass like in Haskell.
/// F is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn Functor(comptime FunctorImpl: type) type {
    if (!@hasDecl(FunctorImpl, "F")) {
        @compileError("The Functor instance must has F type!");
    }

    if (!@hasDecl(FunctorImpl, "BaseType")) {
        @compileError("The Functor instance must has type function: BaseType!");
    }

    if (!@hasDecl(FunctorImpl, "Error")) {
        @compileError("The Functor instance must has Error type!");
    }

    if (!@hasDecl(FunctorImpl, "deinitFa")) {
        @compileError("The Functor instance must has deinitFa function!");
    }

    // const F = FunctorImpl.F;
    return struct {
        const Self = @This();
        pub const InstanceImpl = FunctorImpl;

        pub const Error = InstanceImpl.Error;

        pub const FaType = InstanceImpl.FaType;
        pub const FbType = InstanceImpl.FbType;
        pub const FaLamType = InstanceImpl.FaLamType;
        pub const FbLamType = InstanceImpl.FbLamType;

        /// Typeclass function for map with function
        const FMapType = @TypeOf(struct {
            fn fmapFn(
                instance: *InstanceImpl,
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                f: anytype,
                fa: FaType(K, @TypeOf(f)),
            ) FbType(@TypeOf(f)) {
                _ = instance;
                _ = fa;
            }
        }.fmapFn);

        /// Typeclass function for map with lambda
        const FMapLamType = @TypeOf(struct {
            fn fmapLam(
                instance: *const InstanceImpl,
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                lam: anytype, // a lambda with funtion *const fn(Self, A) B
                fa: FaLamType(K, @TypeOf(lam)),
            ) FbLamType(@TypeOf(lam)) {
                _ = instance;
                _ = fa;
            }
        }.fmapLam);

        pub fn init(instance: InstanceImpl) InstanceImpl {
            if (@TypeOf(InstanceImpl.fmap) != FMapType) {
                @compileError("Incorrect type of fmap for Functor instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fmapLam) != FMapLamType) {
                @compileError("Incorrect type of fmapLam for Functor instance " ++ @typeName(InstanceImpl));
            }
            return instance;
        }
    };
}

pub fn NatTransType(comptime F: TCtor, comptime G: TCtor) type {
    return @TypeOf(struct {
        fn transFn(comptime A: type, fa: F(A)) G(A) {
            _ = fa;
        }
    }.transFn);
}

/// Natural Transformation typeclass like in Haskell.
/// F and G is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn NatTrans(
    comptime NatTransImpl: type,
) type {
    if (!(@hasDecl(NatTransImpl, "F") and @hasDecl(NatTransImpl, "G"))) {
        @compileError("The NatTrans instance must has F and G type!");
    }

    if (!(@hasDecl(NatTransImpl, "Error"))) {
        @compileError("The NatTrans instance must has Error type!");
    }

    const F = NatTransImpl.F;
    const G = NatTransImpl.G;
    const Error = NatTransImpl.Error;

    return struct {
        const Self = @This();
        pub const InstanceImpl = NatTransImpl;

        const FTransType = @TypeOf(struct {
            fn transFn(
                instance: InstanceImpl,
                comptime A: type,
                fa: F(A),
            ) Error!G(A) {
                _ = instance;
                _ = fa;
            }
        }.transFn);

        pub fn init(instance: InstanceImpl) InstanceImpl {
            if (@TypeOf(InstanceImpl.trans) != FTransType) {
                @compileLog("Impl trans type: " ++ @typeName(@TypeOf(InstanceImpl.trans)));
                @compileLog("FTransType: " ++ @typeName(FTransType));
                @compileError("Incorrect type of trans for NatTrans instance: " ++ @typeName(InstanceImpl));
            }
            return instance;
        }
    };
}

pub const MaybeToArrayListNatImpl = struct {
    instanceArray: ArrayListFunctorImpl,

    const Self = @This();

    pub const F = Maybe;
    pub const G = ArrayList;
    pub const Error = Functor(ArrayListFunctorImpl).Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
        if (fa) |a| {
            var array = try ArrayList(A).initCapacity(self.instanceArray.allocator, 1);
            array.appendAssumeCapacity(a);
            return array;
        } else {
            // return empty ArrayList
            return ArrayList(A).init(self.instanceArray.allocator);
        }
    }
};

pub const ArrayListToMaybeNatImpl = struct {
    const Self = @This();

    pub const F = ArrayList;
    pub const G = Maybe;
    pub const Error = Functor(MaybeFunctorImpl).Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
        _ = self;
        if (fa.items.len > 0) {
            return fa.items[0];
        }

        return null;
    }
};
