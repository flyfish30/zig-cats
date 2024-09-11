const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const MapFnKind = base.MapFnKind;
const FMapMode = base.FMapMode;

const Functor = functor.Functor;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;

/// Compose two Type constructor to one Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn ComposeFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Composed(comptime A: type) type {
            return F(G(A));
        }
    }.Composed;
}

pub fn ComposeFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        instanceF: ImplF,
        instanceG: ImplG,

        const Self = @This();
        const FunctorF = Functor(ImplF);
        const FunctorG = Functor(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = ComposeFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            return ImplG.BaseType(ImplF.BaseType(FGA));
        }

        /// Error set of ComposeFunctorImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error = ImplF.Error || ImplG.Error;

        const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // F(G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            const free_ga_fn = struct {
                fn freeGa(ga: ImplF.BaseType(@TypeOf(fga))) void {
                    ImplG.deinitFa(ga, free_fn);
                }
            }.freeGa;
            ImplF.deinitFa(fga, free_ga_fn);
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            const MapFn = @TypeOf(map_fn);
            const map_lam = struct {
                map_fn: *const fn (a: MapFnInType(MapFn)) MapFnRetType(MapFn),

                const MapSelf = @This();
                pub fn call(map_self: *const MapSelf, a: MapFnInType(MapFn)) MapFnRetType(MapFn) {
                    return map_self.map_fn(a);
                }
            }{ .map_fn = &map_fn };

            return fmapLam(self, K, map_lam, fga);
        }

        pub fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const MapLam = @TypeOf(map_lam);
            const map_inner = struct {
                inner_g: *ImplG,
                map_lam: MapLam,

                const InnerSelf = @This();
                pub fn call(
                    inner_self: *const InnerSelf,
                    ga: FunctorG.FaLamType(K, MapLam),
                ) FunctorG.FbLamType(MapLam) {
                    return inner_self.inner_g.fmapLam(K, inner_self.map_lam, ga);
                }
            }{
                .inner_g = &self.instanceG,
                .map_lam = map_lam,
            };

            return self.instanceF.fmapLam(K, map_inner, fga);
        }
    };
}

pub fn ComposeApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        functor_sup: SupImpl,

        const Self = @This();
        pub const SupImpl = ComposeFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is composed FG(A) by ImplF and
        /// ImplG.
        const BaseType = SupImpl.BaseType;

        /// Error set of ComposeApplicativeImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error = SupImpl.Error;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub inline fn deinitFa(
            fga: anytype, // F(G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            return SupImpl.deinitFa(fga, free_fn);
        }

        pub inline fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return self.functor_sup.fmap(K, map_fn, fga);
        }

        pub inline fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return self.functor_sup.fmapLam(K, map_lam, fga);
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            return self.functor_sup.instanceF.pure(self.functor_sup.instanceG.pure(a));
        }

        pub fn fapply(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) AFbType(B) {
            return fapplyGeneric(self, .NormalMap, A, B, fgf, fga);
        }

        pub fn fapplyLam(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            return fapplyGeneric(self, .LambdaMap, A, B, fgf, fga);
        }

        fn fapplyGeneric(
            self: *Self,
            comptime M: FMapMode,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            // inner_fapply: G (a -> b) -> G a -> G b
            // outer_fapply: F (G a -> G b) -> F (G a) -> F (G b)
            // fmap inner_fapply: F (G (a -> b)) -> F (G a -> G b)
            // outer_fapply (fmap inner_fapply): F (G (a -> b)) -> F (G a) -> F (G b)
            // fapply = outer_fapply (fmap inner_fapply)

            // A function with type *const fn (A) B
            // or a lambda that has function *const fn (LamSelf, A) B
            const FnOrLambdaType = BaseType(@TypeOf(fgf));

            const inner_fapply = struct {
                inner_instance: *ImplG,

                const InnerSelf = @This();
                const ApplyLam = struct {
                    apply_instanceG: *ImplG,
                    apply_gf_p: *ImplG.F(FnOrLambdaType),

                    const ApplySelf = @This();
                    // applyFn: G a -> G b
                    pub fn call(applySelf: *const ApplySelf, ga: ImplG.F(A)) ImplG.AFbType(B) {
                        if (M == .NormalMap) {
                            return applySelf.apply_instanceG.fapply(A, B, applySelf.apply_gf_p.*, ga);
                        } else {
                            return applySelf.apply_instanceG.fapplyLam(A, B, applySelf.apply_gf_p.*, ga);
                        }
                    }
                };

                // mapFn \gf_p -> apply_lam : G (a -> b) -> G a -> G b
                pub fn call(
                    inner_self: *const InnerSelf,
                    gf_p: *ImplG.F(FnOrLambdaType),
                ) ApplyLam {
                    const apply_lam = .{
                        .apply_instanceG = inner_self.inner_instance,
                        .apply_gf_p = gf_p,
                    };
                    // apply lambda \ga -> fapply instanceG gf ga : G a -> G b
                    return apply_lam;
                }
            }{ .inner_instance = &self.functor_sup.instanceG };

            const free_fn = struct {
                fn free_fn(lam: @TypeOf(inner_fapply).ApplyLam) void {
                    _ = lam;
                }
            }.free_fn;

            const flam = try self.functor_sup.instanceF.fmapLam(.NewValMapRef, inner_fapply, @constCast(&fgf));
            defer ImplF.deinitFa(flam, free_fn);
            return self.functor_sup.instanceF.fapplyLam(
                ImplG.F(A),
                ImplG.AFbType(B),
                flam,
                fga,
            );
        }
    };
}

/// Compose two Functor to one Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ComposeFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const FGImpl = ComposeFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(FGImpl);
}

/// Compose two Applicative Functor to one Applicative Functor, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ComposeApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const FGImpl = ComposeApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
    return Applicative(FGImpl);
}
