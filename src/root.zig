const std = @import("std");
const testing = std.testing;

pub const pure = @import("pure.zig");

pub usingnamespace @import("base.zig");
pub usingnamespace @import("functor.zig");
pub usingnamespace @import("applicative.zig");
pub usingnamespace @import("monad.zig");
