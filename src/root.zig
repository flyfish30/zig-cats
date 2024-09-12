const std = @import("std");
const testing = std.testing;

pub const pure = @import("pure.zig");

pub usingnamespace @import("base.zig");
pub usingnamespace @import("functor.zig");
pub usingnamespace @import("applicative.zig");
pub usingnamespace @import("monad.zig");
pub usingnamespace @import("compose.zig");
pub usingnamespace @import("product.zig");
pub usingnamespace @import("coproduct.zig");

test {
    std.testing.refAllDecls(@This());
}
