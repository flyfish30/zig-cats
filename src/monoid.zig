const std = @import("std");
const base = @import("base.zig");
const maybe = @import("maybe.zig");
const array = @import("array_list_monad.zig");

/// Monoid typeclass like in Haskell.
/// A is just a type of Monoid typeclass, such as u32, List.
/// The return type is a Constrait, just like a constrait `Monoid a` in haskell.
pub fn Monoid(comptime A: type) type {
    const MonoidImpl = MonoidImplFromType(A);
    std.debug.assert(A == MonoidImpl.M);
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
                instance: *InstanceImpl,
            ) EM {
                _ = instance;
            }
        }.memptyFn);

        /// Typeclass function for mappend
        const MappendType = @TypeOf(struct {
            fn mappendFn(
                instance: *InstanceImpl,
                a: M,
                b: M,
            ) EM {
                _ = instance;
                _ = a;
                _ = b;
            }
        }.mappendFn);
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

    pub fn mempty(self: Self) void {
        _ = self;
        return {};
    }

    pub fn mappend(self: Self, a: void, b: void) void {
        _ = self;
        _ = a;
        _ = b;
        return {};
    }

    pub const default: Self = .{};
};

// instance Monoid number, type of number is int, float, etc.
fn NumberMonoidImpl(comptime Num: type) type {
    return struct {
        const Self = @This();
        pub const Error: ?type = null;
        pub const M = Num;
        pub const EM = Num;

        pub fn mempty(self: Self) u32 {
            _ = self;
            return 0;
        }

        pub fn mappend(self: Self, a: Num, b: Num) Num {
            _ = self;
            return a + b;
        }
    };
}

const monoidImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(void), VoidMonoidImpl },
    // Add more MonoidImply and associated type
});

const monoidImplFnMap = std.StaticStringMap(*const fn (type) type).initComptime(.{
    .{ @typeName(std.ArrayList(void)), array.ArrayListMonoidImpl },
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
            .optional => return maybe.MaybeMonoidImpl(std.meta.Child(T)),
            else => {},
        }

        const impl_fn = monoidImplMap.get(@typeName(T));
        if (impl_fn == null) {
            @compileError("The customered Monoid(" ++ @typeName(T) ++ ") must has MonoidImpl!");
        }
        return impl_fn.?;
    }
}

// pub fn sumAll(xs: std.ArrayList[u32])
//    TypeWithContraits(u32, .{Monoid(u32)}) {
// }
