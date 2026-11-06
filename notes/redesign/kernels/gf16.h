/* GF(2^16) = Fan-Paar tower T_4 (the low 16 bits of minidregg's Tower256 coordinates),
 * reference multiply ported from minidregg prover/src/binary_tower_256.rs mul_small,
 * plus the fast forms used by the encoder. */
#pragma once
#include <stdint.h>

static uint32_t t_mulgen(int level, uint32_t v);
static uint32_t t_mul(int level, uint32_t a, uint32_t b) {
    if (level == 0) return a & b & 1;
    int child = level - 1, w = 1 << child;
    uint32_t mask = (w == 32) ? 0xffffffffu : ((1u << w) - 1);
    uint32_t a0 = a & mask, a1 = (a >> w) & mask, b0 = b & mask, b1 = (b >> w) & mask;
    uint32_t p0 = t_mul(child, a0, b0), p1 = t_mul(child, a1, b1);
    uint32_t mixed = t_mul(child, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1;
    uint32_t pc = child == 0 ? p1 : t_mulgen(child, p1);
    return (p0 ^ p1) | ((mixed ^ pc) << w);
}
static uint32_t t_mulgen(int level, uint32_t v) {
    int child = level - 1, w = 1 << child;
    uint32_t mask = (1u << w) - 1;
    uint32_t lo = v & mask, hi = (v >> w) & mask;
    uint32_t rh = child == 0 ? (lo ^ hi) : (lo ^ t_mulgen(child, hi));
    return hi | (rh << w);
}
static inline uint16_t gf_mul_ref(uint16_t a, uint16_t b) { return (uint16_t)t_mul(4, a, b); }

/* log/exp tables over a generator found by search with the reference multiply */
static uint16_t GF_EXP[2 * 65535 + 2];
static int32_t GF_LOG[65536];
static void gf_init(void) {
    for (uint32_t g = 2; g < 65536; g++) {
        uint16_t x = 1; uint32_t i;
        for (i = 0; i < 65535; i++) { GF_EXP[i] = x; GF_LOG[x] = (int32_t)i; x = gf_mul_ref(x, (uint16_t)g); if (x == 1) break; }
        if (i == 65534) { for (i = 0; i < 65535; i++) GF_EXP[i + 65535] = GF_EXP[i]; GF_LOG[0] = -1; return; }
    }
}
static inline uint16_t gf_mul(uint16_t a, uint16_t b) {
    if (!a || !b) return 0; return GF_EXP[GF_LOG[a] + GF_LOG[b]];
}
static inline uint16_t gf_inv(uint16_t a) { return GF_EXP[65535 - GF_LOG[a]]; }

/* multiply-by-constant as 4 nibble tables (the pshufb / GFNI shape: c*x is GF(2)-linear in x) */
typedef struct { uint16_t t[4][16]; } cmul_t;
static void cmul_make(cmul_t *m, uint16_t c) {
    for (int k = 0; k < 4; k++) for (int v = 0; v < 16; v++) m->t[k][v] = gf_mul(c, (uint16_t)(v << (4 * k)));
}
static inline uint16_t cmul(const cmul_t *m, uint16_t x) {
    return m->t[0][x & 15] ^ m->t[1][(x >> 4) & 15] ^ m->t[2][(x >> 8) & 15] ^ m->t[3][x >> 12];
}
