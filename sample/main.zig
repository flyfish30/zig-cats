const std = @import("std");
const zcats = @import("zcats");
const sample = @import("zcats_sample.zig");
const pure_sample = @import("pure_zcats_sample.zig");

pub fn main() !void {
    std.debug.print("Run Samples of zig-cats...\n", .{});

    pure_sample.runZCatsSamples();
    try sample.runZCatsSamples();
}
