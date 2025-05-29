// These functions are defined for unit test
pub fn add4(a: u32) u32 {
    return a + 4;
}

pub fn add10(a: u32) u32 {
    return a + 10;
}

pub fn mul2(a: u32) u32 {
    return a * 2;
}

pub fn mul3(a: u32) u32 {
    return a * 3;
}

pub fn add_pi_f32(a: u32) f32 {
    return @as(f32, @floatFromInt(a)) + 3.14;
}

pub fn add_pi_f64(a: u32) f64 {
    return @as(f64, @floatFromInt(a)) + 3.14;
}

pub fn mul_pi_f64(a: u32) f64 {
    return @as(f64, @floatFromInt(a)) * 3.14;
}

pub fn add_e_f64(a: u32) f64 {
    return @as(f64, @floatFromInt(a)) + 2.71828;
}

pub fn mul_e_f64(a: u32) f64 {
    return @as(f64, @floatFromInt(a)) * 2.71828;
}

pub const Add_x_u32_Lam = struct {
    _x: u32,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) u32 {
        return a + self._x;
    }
};

pub const Add_x_f32_Lam = struct {
    _x: f32,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) f32 {
        return @as(f32, @floatFromInt(a)) + self._x;
    }
};

pub const Add_x_f64_Lam = struct {
    _x: f64,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + self._x;
    }
};

pub const Mul_x_u32_Lam = struct {
    _x: u32,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) u32 {
        return a * self._x;
    }
};

pub const Mul_x_f32_Lam = struct {
    _x: f32,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) f32 {
        return @as(f32, @floatFromInt(a)) * self._x;
    }
};

pub const Mul_x_f64_Lam = struct {
    _x: f64,
    const Self = @This();
    pub fn call(self: *const Self, a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * self._x;
    }
};

pub const Div_x_u32_Lam = struct {
    _x: u32,
    const Self = @This();
    pub fn call(self: *const Self, a: f64) u32 {
        const a_u32: u32 = @intFromFloat(a);
        return @divFloor(a_u32, self._x);
    }
};

pub const Point3_offset_u32_Lam = struct {
    _point: Point3D,
    const Self = @This();
    const Point3D = struct { f64, f64, f64 };
    pub fn call(self: *const Self, offset: u32) Point3D {
        const offset_float: f64 = @floatFromInt(offset);
        return .{
            self._point[0] + offset_float,
            self._point[1] + offset_float,
            self._point[2] + offset_float,
        };
    }
};
