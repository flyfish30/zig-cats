//! Definition State struct, these is a instance of Functor|Applicative|Monad typeclass.

const std = @import("std");
const base = @import("base.zig");

const FreeTFn = base.FreeTFn;

pub fn State(comptime S: type, comptime free_s: FreeTFn(S)) type {
    return struct {
        fn StateFn(comptime A: type) type {
            return struct {
                s: StateS,

                const Self = @This();
                pub const StateS = S;
                pub const StateA = A;
                pub fn get(self: Self) struct { void, S } {
                    return .{ {}, self.s };
                }

                pub fn put(self: Self, s: S) struct { S, S } {
                    free_s(self.s);
                    self.s = s;
                    return .{ s, s };
                }
            };
        }
    }.StateFn;
}

pub fn StateMonadImpl(comptime S: type, comptime free_s: FreeTFn(S)) type {
    return struct {
        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = State(S, free_s);

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime StateT: type) type {
            return StateT.StateA;
        }
    };
}
