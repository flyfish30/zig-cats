const std = @import("std");
const base = @import("base.zig");
const semi_grp = @import("semigroup.zig");
const maybe = @import("maybe.zig");
const vector = @import("vector.zig");
const arraym = @import("array_monad.zig");
const arraylm = @import("array_list_monad.zig");

/// Monoid typeclass like in Haskell.
/// A is just a type of Monoid typeclass, such as u32, List.
/// The return type is a Constrait, just like a constrait `Monoid a` in haskell.
pub fn Monoid(comptime A: type) type {
    _ = semi_grp.SemiGroup(A);
    const MonoidImpl = MonoidImplFromType(A);
    if (A != MonoidImpl.M) {
        @compileError("Monoid A(" ++ @typeName(A) ++ ") not match MonoidImpl.M(" ++ @typeName(MonoidImpl.M) ++ ")");
    }
    return MonoidFromImpl(MonoidImpl);
}

pub fn MonoidFromImpl(comptime MonoidImpl: type) type {
    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        pub const InstanceImpl = MonoidImpl;
        pub const Error: ?type = InstanceImpl.Error;

        /// The type M is a monoid, so the Monoid(M) is a Constrait.
        pub const M = InstanceImpl.M;
        /// The result type of operator function in Monoid
        /// This is just the type M that maybe with Error
        pub const EM = InstanceImpl.EM;

        /// Typeclass function for mempty
        const MemptyType = @TypeOf(struct {
            fn memptyFn(
                instance: *const InstanceImpl,
            ) EM {
                _ = instance;
            }
        }.memptyFn);

        /// Typeclass function for mappend
        const MappendType = @TypeOf(struct {
            fn mappendFn(
                instance: *const InstanceImpl,
                a: M,
                b: M,
            ) EM {
                _ = instance;
                _ = a;
                _ = b;
            }
        }.mappendFn);

        /// Typeclass function for mconcat
        const MconcatType = @TypeOf(struct {
            fn mconcatFn(
                instance: *const InstanceImpl,
                xs: []const M,
            ) EM {
                _ = instance;
                _ = xs;
            }
        }.mconcatFn);
    };

    if (@TypeOf(MonoidImpl.mempty) != T.MemptyType) {
        @compileError("Incorrect type of mempty for Monoid instance " ++ @typeName(MonoidImpl));
    }
    if (@TypeOf(MonoidImpl.mappend) != T.MappendType) {
        @compileError("Incorrect type of mappend for Monoid instance " ++ @typeName(MonoidImpl));
    }
    return base.ConstraitType(T);
}

// instance Monoid void
const VoidMonoidImpl = struct {
    const Self = @This();
    pub const Error: ?type = null;
    const M = void;
    const EM = void;

    pub fn mempty(self: *const Self) EM {
        _ = self;
        return {};
    }

    pub fn mappend(self: *const Self, a: M, b: M) EM {
        _ = self;
        _ = a;
        _ = b;
        return {};
    }

    pub fn mconcat(self: *const Self, xs: []const M) EM {
        _ = self;
        _ = xs;
        return {};
    }

    pub const default: Self = .{};
};

// instance Monoid number, type of number is int, float, vector, etc.
fn NumberMonoidImpl(comptime Num: type) type {
    return struct {
        const Self = @This();
        pub const Error: ?type = null;
        pub const M = Num;
        pub const EM = Num;

        pub fn mempty(self: *const Self) EM {
            _ = self;
            return 0;
        }

        pub fn mappend(self: *const Self, a: M, b: M) EM {
            _ = self;
            return a + b;
        }

        pub fn mconcat(self: *const Self, xs: []const M) EM {
            _ = self;
            var acc: M = 0;
            for (xs) |x| {
                acc += x;
            }
            return acc;
        }
    };
}

const monoidImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(void), VoidMonoidImpl },
    // Add more MonoidImply and associated type
});

const monoidImplFnMap = std.StaticStringMap(*const fn (type) type).initComptime(.{
    .{ @typeName(std.ArrayList(void)), arraylm.ArrayListMonoidImpl },
});

pub fn MonoidImplFromType(comptime T: type) type {
    comptime {
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "MonoidImpl")) {
                    return T.MonoidImpl;
                }
                for (monoidImplFnMap.values()) |ImplFn| {
                    const F = ImplFn(void).F;
                    const A = ImplFn(void).BaseType(T);
                    if (F(A) == T) return ImplFn(A);
                }
            },
            .int, .float => return NumberMonoidImpl(T),
            .vector => |info| return vector.VectorMonoidImpl(info.len, info.child),
            .array => |info| return arraym.ArrayMonoidImpl(info.len, info.child),
            .optional => return maybe.MaybeMonoidImpl(std.meta.Child(T)),
            else => {},
        }

        const impl = monoidImplMap.get(@typeName(T));
        if (impl == null) {
            @compileError("The customered Monoid(" ++ @typeName(T) ++ ") must has MonoidImpl!");
        }
        return impl.?;
    }
}

pub fn commonMconcat(
    comptime M: type,
    comptime EM: type,
    monoid_impl: anytype,
    xs: []const M,
) EM {
    // The monoid_impl is must be a pointer
    const MonoidImpl = std.meta.Child(@TypeOf(monoid_impl));
    const Error = MonoidImpl.Error;
    var acc = if (Error == null) monoid_impl.mempty() else try monoid_impl.mempty();
    for (xs) |x| {
        if (Error == null) {
            acc = monoid_impl.mappend(acc, x);
        } else {
            acc = try monoid_impl.mappend(acc, x);
        }
    }

    return acc;
}

const testing = std.testing;
test "mconcat u32 mumbers" {
    const MonoidImpl = Monoid(u32);
    var monoid_impl = MonoidImpl.InstanceImpl{};
    const numbs = &[_]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 };
    const sum = monoid_impl.mconcat(numbs);
    try testing.expectEqual(55, sum);
}
