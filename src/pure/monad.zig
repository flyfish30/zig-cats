const std = @import("std");
const base = @import("../base.zig");
const applicative = @import("applicative.zig");

const TCtor = base.TCtor;
const Applicative = applicative.Applicative;

/// Monad typeclass like in Haskell, it inherit from Applicative Functor.
/// M is instance of Monad typeclass, such as Maybe, List
pub fn Monad(comptime MonadImpl: type) type {
    const M = MonadImpl.F;
    const has_sup_impl = @hasField(MonadImpl, "SupImpl");

    const InstanceType = struct {
        pub const InstanceImpl = MonadImpl;
        const ApplicativeSup = if (has_sup_impl)
            Applicative(InstanceImpl.SupImpl)
        else
            Applicative(InstanceImpl);

        pub const MbType = M;
        const BindType = @TypeOf(struct {
            fn bindFn(
                comptime A: type,
                comptime B: type,
                // monad function: (a -> M b), ma: M a
                ma: M(A),
                k: *const fn (A) M(B),
            ) M(B) {
                _ = ma;
                _ = k;
            }
        }.bindFn);

        const BindLamType = @TypeOf(struct {
            fn bindLam(
                comptime A: type,
                comptime B: type,
                // monad function: (a -> M b), ma: M a
                ma: M(A),
                klam: anytype, // a lambda with function *const fn(Self, A) M(B)
            ) M(B) {
                _ = ma;
                _ = klam;
            }
        }.bindLam);

        pub fn init() void {
            if (@TypeOf(InstanceImpl.bind) != BindType) {
                @compileError("Incorrect type of bind for Monad instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.bindLam) != BindLamType) {
                @compileError("Incorrect type of bindLam for Monad instance " ++ @typeName(InstanceImpl));
            }
        }

        pub const fmap = ApplicativeSup.fmap;
        pub const fmapLam = ApplicativeSup.fmapLam;
        pub const pure = ApplicativeSup.pure;
        pub const fapply = ApplicativeSup.fapply;
        pub const fapplyLam = ApplicativeSup.fapplyLam;
        pub const bind = InstanceImpl.bind;
        pub const bindLam = InstanceImpl.bindLam;
    };

    InstanceType.init();
    return InstanceType;
}
