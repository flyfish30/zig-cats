// These functions are defined for unit test
pub const add10 = struct {
    fn f(a: u32) u32 {
        return a + 10;
    }
}.f;

pub const add_pi_f32 = struct {
    fn f(a: u32) f32 {
        return @as(f32, @floatFromInt(a)) + 3.14;
    }
}.f;

pub const add_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 3.14;
    }
}.f;

pub const mul_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 3.14;
    }
}.f;

pub const add_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 2.71828;
    }
}.f;

pub const mul_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 2.71828;
    }
}.f;
