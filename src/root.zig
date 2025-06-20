const std = @import("std");
const testing = std.testing;

// pub const pure = @import("pure.zig");

pub usingnamespace @import("base.zig");
pub usingnamespace @import("monoid.zig");
pub usingnamespace @import("functor.zig");
pub usingnamespace @import("applicative.zig");
pub usingnamespace @import("monad.zig");
pub usingnamespace @import("compose.zig");
pub usingnamespace @import("product.zig");
pub usingnamespace @import("coproduct.zig");
pub usingnamespace @import("free_types.zig");

pub usingnamespace @import("fixed_point.zig");

pub usingnamespace @import("maybe.zig");
pub usingnamespace @import("vector.zig");
pub usingnamespace @import("array_monad.zig");
pub usingnamespace @import("array_list_monad.zig");
pub usingnamespace @import("state.zig");

test {
    std.testing.refAllDecls(@This());
}
