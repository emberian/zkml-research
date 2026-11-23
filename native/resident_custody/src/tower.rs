// Equality dependency of the vendored qsag BeltLatch kernel.
#[inline]
const fn diff_bytes8(a: &[u8; 32], b: &[u8; 32], base: usize) -> u8 {
    ((a[base] ^ b[base]) | (a[base + 1] ^ b[base + 1]))
        | ((a[base + 2] ^ b[base + 2]) | (a[base + 3] ^ b[base + 3]))
        | ((a[base + 4] ^ b[base + 4]) | (a[base + 5] ^ b[base + 5]))
        | ((a[base + 6] ^ b[base + 6]) | (a[base + 7] ^ b[base + 7]))
}

/// Branchless constant-time 32-byte equality check (`0` data-dependent branches).
#[inline]
pub const fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let d = (diff_bytes8(a, b, 0) | diff_bytes8(a, b, 8))
        | (diff_bytes8(a, b, 16) | diff_bytes8(a, b, 24));
    d == 0
}
