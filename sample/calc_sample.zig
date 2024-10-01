const std = @import("std");
const zcats = @import("zcats");

const Allocator = std.mem.Allocator;
const Functor = zcats.Functor;
const Applicative = zcats.Applicative;
const Monad = zcats.Monad;
const NatTrans = zcats.NatTrans;

const ArrayListMonadImpl = zcats.ArrayListMonadImpl;
const StateMonadImpl = zcats.StateMonadImpl;

pub fn calcSample() !void {
    std.debug.print("calcSample entry!\n", .{});
}
