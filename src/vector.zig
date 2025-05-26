const std = @import("std");
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const assert = std.debug.assert;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const FMapMode = base.FMapMode;
const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const castInplaceValue = base.castInplaceValue;

const Monoid = monoid.Monoid;
const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

const Vector = base.Vector;

/// The instance of Monoid Vector(N, T).
/// Like `instance Monoid Vector(N, T)` in haskell.
pub fn VectorMonoidImpl(comptime N: usize, comptime T: type) type {
    return struct {
        child_impl: ChildImpl,

        const Self = @This();
        const ChildImpl = Monoid(T).InstanceImpl;
        /// The Vector is pure value, so it is Error is null.
        pub const Error: ?type = null;

        /// The type M is a monoid, so the Monoid(M) is a Constrait.
        pub const M = @Vector(N, T);
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = M;

        pub fn mempty(self: *const Self) EM {
            return @splat(self.child_impl.mempty());
        }

        pub fn mappend(self: *const Self, ma: M, mb: M) EM {
            _ = self;
            return ma + mb;
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            var acc: M = self.mempty();
            for (xs) |x| {
                acc += x;
            }
            return acc;
        }
    };
}

test "Monoid Vector(N, A) mempty and mappend" {
    const U32Monoid = Monoid(u32);
    const monoid_u32 = U32Monoid.InstanceImpl{};
    const Vector4U32Monoid = Monoid(@Vector(4, u32));
    const vector4_u32_m = Vector4U32Monoid.InstanceImpl{ .child_impl = monoid_u32 };
    try testing.expect(base.isPureTypeClass(@TypeOf(vector4_u32_m)));

    const vector4_u32_unit = vector4_u32_m.mempty();
    try testing.expectEqual(@as(@Vector(4, u32), @splat(0)), vector4_u32_unit);

    const v1: [4]u32 = @Vector(4, u32){ 42, 34, 75, 13 };
    const v2: [4]u32 = @Vector(4, u32){ 37, 57, 13, 42 };
    try testing.expectEqual(@Vector(4, u32){ 42, 34, 75, 13 }, vector4_u32_m.mappend(vector4_u32_unit, v1));
    try testing.expectEqual(@Vector(4, u32){ 79, 91, 88, 55 }, vector4_u32_m.mappend(v1, v2));
}
