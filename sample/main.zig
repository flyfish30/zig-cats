const std = @import("std");
const zcats = @import("zcats");
const sample = @import("zcats_sample.zig");
const pure_sample = @import("pure_zcats_sample.zig");
const freem = @import("free_monad_sample.zig");

pub fn main() !void {
    std.debug.print("Run pure samples of zig-cats...\n", .{});
    pure_sample.runZCatsSamples();

    std.debug.print("\nRun impure samples of zig-cats...\n", .{});
    try sample.runZCatsSamples();

    std.debug.print("\nRun free monad samples...\n", .{});
    try freem.freeMonadSmaple();
}
