const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

const assert = std.debug.assert;
const TCtor = base.TCtor;

const MapFnKind = base.MapFnKind;

const Functor = functor.Functor;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;

/// Get a Coproduct Type constructor from two Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn CoproductFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Coproducted(comptime A: type) type {
            return union(enum) {
                inl: F(A),
                inr: G(A),
            };
        }
    }.Coproducted;
}

/// Get tuple of left and right type of coproduct
pub fn getCoproductTypeTuple(comptime U: type) struct { type, type } {
    const info = @typeInfo(U);
    comptime assert(info == .Union);
    comptime assert(info.Union.fields.len == 2);

    const l_type = info.Union.fields[0].type;
    const r_type = info.Union.fields[1].type;
    return .{ l_type, r_type };
}

pub fn CoproductFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        instanceF: ImplF,
        instanceG: ImplG,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = CoproductFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            const l_type, const r_type = getCoproductTypeTuple(FGA);
            comptime assert(ImplF.BaseType(l_type) == ImplG.BaseType(r_type));
            return ImplF.BaseType(l_type);
        }

        /// Error set of CoproductFunctorImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error = ImplF.Error || ImplG.Error;

        const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            ImplF.deinitFa(fga[0], free_fn);
            ImplG.deinitFa(fga[1], free_fn);
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return switch (fga) {
                .inl => |fa| .{ .inl = try self.instanceF.fmap(K, map_fn, fa) },
                .inr => |ga| .{ .inr = try self.instanceG.fmap(K, map_fn, ga) },
            };
        }

        pub fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return switch (fga) {
                .inl => |fa| .{ .inl = try self.instanceF.fmapLam(K, map_lam, fa) },
                .inr => |ga| .{ .inr = try self.instanceG.fmapLam(K, map_lam, ga) },
            };
        }
    };
}

pub fn CoproductApplicativeImpl(
    comptime ImplF: type,
    comptime ImplG: type,
    comptime ImplNat: type,
) type {
    return struct {
        functor_sup: SupImpl,
        /// The ImplNat type must is void for instance of Coproduct Functor
        natural_gf: ImplNat,

        const Self = @This();
        pub const SupImpl = CoproductFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        const BaseType = SupImpl.BaseType;

        /// Error set of CoproductApplicativeImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error = SupImpl.Error;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            SupImpl.deinitFa(fga, free_fn);
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return self.functor_sup.fmap(K, map_fn, fga);
        }

        pub fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return self.functor_sup.fmapLam(K, map_lam, fga);
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            return .{ .inr = try self.functor_sup.instanceG.pure(a) };
        }

        pub fn fapply(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) AFbType(B) {
            const FnType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) },
                    .inr => |ga| {
                        // fa is ArrayList(A), so we should be free it.
                        const fa = try self.natural_gf.trans(A, ga);
                        defer fa.deinit();
                        return .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        // ff is ArrayList(FnType), so we should be free it.
                        const ff = try self.natural_gf.trans(FnType, gf);
                        defer ff.deinit();
                        return .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) };
                    },
                    .inr => |ga| .{ .inr = try self.functor_sup.instanceG.fapply(A, B, gf, ga) },
                },
            };
        }

        pub fn fapplyLam(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            const LamType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) },
                    .inr => |ga| {
                        // fa is ArrayList(A), so we should be free it.
                        const fa = try self.natural_gf.trans(A, ga);
                        defer fa.deinit();
                        return .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        // ff is ArrayList(FnType), so we should be free it.
                        const ff = try self.natural_gf.trans(LamType, gf);
                        defer ff.deinit();
                        return .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) };
                    },
                    .inr => |ga| .{ .inr = try self.functor_sup.instanceG.fapplyLam(A, B, gf, ga) },
                },
            };
        }
    };
}

/// Get a Coproduct Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn CoproductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const FGImpl = CoproductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(FGImpl);
}

/// Get a Coproduct Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn CoproductApplicative(
    comptime ApplicativeF: type,
    comptime ApplicativeG: type,
    comptime NaturalGF: type,
) type {
    const FGImpl = CoproductApplicativeImpl(
        ApplicativeF.InstanceImpl,
        ApplicativeG.InstanceImpl,
        NaturalGF.InstanceImpl,
    );
    return Applicative(FGImpl);
}
