const std = @import("std");
const zcats = @import("zcats");
const sample = @import("zcats_sample.zig");
const pure_sample = @import("pure_zcats_sample.zig");

pub fn main() !void {
    std.debug.print("Run pure samples of zig-cats...\n", .{});
    pure_sample.runZCatsSamples();

    std.debug.print("\nRun impure samples of zig-cats...\n", .{});
    try sample.runZCatsSamples();
}
