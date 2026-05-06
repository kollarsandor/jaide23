const std = @import("std");
const Allocator = std.mem.Allocator;
const Tensor = @import("../core/tensor.zig").Tensor;

pub const OFTB = struct {
    fractal_scale: f32,
    dim: usize,

    pub fn init(d: usize) OFTB {
        return OFTB{
            .fractal_scale = 0.70710678,
            .dim = d,
        };
    }

    pub fn forwardInPlace(self: *const OFTB, x: *Tensor) void {
        if (x.data.len < self.dim * 2) return;
        const half = self.dim;
        const x1 = x.data[0..half];
        const x2 = x.data[half .. half * 2];

        var i: usize = 0;
        while (i < half) : (i += 1) {
            const a = x1[i];
            const b = x2[i];
            x1[i] = (a - b) * self.fractal_scale;
            x2[i] = (a + b) * self.fractal_scale;
        }
    }

    pub fn backwardInPlace(self: *const OFTB, grad: []f32) void {
        if (grad.len < self.dim * 2) return;
        const half = self.dim;
        const g1 = grad[0..half];
        const g2 = grad[half .. half * 2];

        var i: usize = 0;
        while (i < half) : (i += 1) {
            const a = g1[i];
            const b = g2[i];
            g1[i] = (a + b) * self.fractal_scale;
            g2[i] = (-a + b) * self.fractal_scale;
        }
    }
};
