const std = @import("std");
const base = @import("base.zig");
const maybe = @import("maybe.zig");
const array = @import("array_list_monad.zig");

/// SemiGroup typeclass like in Haskell.
/// A is just a type of SemiGroup typeclass, such as u32, List.
/// The return type is a Constrait, just like a constrait `SemiGroup a` in haskell.
pub fn SemiGroup(comptime A: type) type {
    const SemiGroupImpl = SemiGroupImplFromType(A);
    std.debug.assert(A == SemiGroupImpl.M);
    return SemiGroupFromImpl(SemiGroupImpl);
}

pub fn SemiGroupFromImpl(comptime SemiGroupImpl: type) type {
    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        pub const InstanceImpl = SemiGroupImpl;
        pub const Error: ?type = InstanceImpl.Error;

        /// The type M is a semi-group, so the SemiGroup(M) is a Constrait.
        pub const M = InstanceImpl.M;
        /// The result type of operator function in SemiGroup
        /// This is just the type M that maybe with Error
        pub const EM = InstanceImpl.EM;

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
    };

    if (@TypeOf(SemiGroupImpl.mappend) != T.MappendType) {
        @compileError("Incorrect type of mappend for SemiGroup instance " ++ @typeName(SemiGroupImpl));
    }
    return base.ConstraitType(T);
}

// instance SemiGroup void
const VoidSemiGroupImpl = struct {
    const Self = @This();
    pub const Error: ?type = null;
    const M = void;
    const EM = void;

    pub fn mappend(self: *const Self, a: void, b: void) void {
        _ = self;
        _ = a;
        _ = b;
        return {};
    }

    pub const default: Self = .{};
};

// instance SemiGroup number, type of number is int, float, etc.
fn NumberSemiGroupImpl(comptime Num: type) type {
    return struct {
        const Self = @This();
        pub const Error: ?type = null;
        pub const M = Num;
        pub const EM = Num;

        pub fn mappend(self: *const Self, a: Num, b: Num) Num {
            _ = self;
            return a + b;
        }
    };
}

const semi_group_impl_map = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(void), VoidSemiGroupImpl },
    // Add more SemiGroupImply and associated type
});

const monoid_impl_fn_map = std.StaticStringMap(*const fn (type) type).initComptime(.{
    .{ @typeName(std.ArrayList(void)), array.ArrayListMonoidImpl },
});

pub fn SemiGroupImplFromType(comptime T: type) type {
    comptime {
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "SemiGroupImpl")) {
                    return T.SemiGroupImpl;
                }
                for (monoid_impl_fn_map.values()) |ImplFn| {
                    const F = ImplFn(void).F;
                    const A = ImplFn(void).BaseType(T);
                    if (F(A) == T) return ImplFn(A);
                }
            },
            .int, .float => return NumberSemiGroupImpl(T),
            .optional => return maybe.MaybeMonoidImpl(std.meta.Child(T)),
            else => {},
        }

        const impl_fn = semi_group_impl_map.get(@typeName(T));
        if (impl_fn == null) {
            @compileError("The customered SemiGroup(" ++ @typeName(T) ++ ") must has SemiGroupImpl!");
        }
        return impl_fn.?;
    }
}
