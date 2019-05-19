#[inline]
pub fn div_ceil(a: usize, b: usize) -> usize {
    (a + b - 1) / b
}

#[inline]
pub fn div_floor(a: usize, b: usize) -> usize {
    a / b
}

#[inline]
pub fn round_up(a: usize, b: usize) -> usize {
    div_ceil(a, b) * b
}

#[inline]
pub fn round_down(a: usize, b: usize) -> usize {
    div_floor(a, b) * b
}
