/* GF(2^256) in the polynomial basis mod f = x^256 + x^10 + x^5 + x^2 + 1 (irreducible: Rabin test in
 * piop_ref.py). Field-isomorphic to Tower256; minidregg's fast prover runs its arithmetic the same way and
 * converts coordinates at the boundary (TOWER256.md section 1). Carry-less multiply by PMULL / PCLMULQDQ. */
#pragma once
#include <stdint.h>
#include <string.h>
typedef struct { uint64_t w[4]; } g256;
static __thread long g256_mults;  /* per-thread multiply counter for the cost report */
#if defined(__aarch64__)
#include <arm_neon.h>
static inline void clmul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi) {
    poly128_t p = vmull_p64((poly64_t)a, (poly64_t)b);
    uint64x2_t v = vreinterpretq_u64_p128(p); *lo = vgetq_lane_u64(v, 0); *hi = vgetq_lane_u64(v, 1);
}
#elif defined(__PCLMUL__)
#include <wmmintrin.h>
#include <smmintrin.h>
static inline void clmul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi) {
    __m128i p = _mm_clmulepi64_si128(_mm_cvtsi64_si128((long long)a), _mm_cvtsi64_si128((long long)b), 0);
    *lo = (uint64_t)_mm_cvtsi128_si64(p); *hi = (uint64_t)_mm_extract_epi64(p, 1);
}
#else
static inline void clmul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi) {
    uint64_t l = 0, h = 0;
    for (int i = 0; i < 64; i++) if (b >> i & 1) { l ^= a << i; if (i) h ^= a >> (64 - i); }
    *lo = l; *hi = h;
}
#endif
static inline g256 g_add(g256 a, g256 b) { for (int i = 0; i < 4; i++) a.w[i] ^= b.w[i]; return a; }
static inline int g_is0(g256 a) { return !(a.w[0] | a.w[1] | a.w[2] | a.w[3]); }
#if defined(__PCLMUL__)
/* x86: 128-bit lanes, Karatsuba on the 128-bit halves (3 x 4 PCLMULQDQ = 12 instead of 16) */
static inline void mul128(__m128i a, __m128i b, __m128i *lo, __m128i *hi) {
    __m128i l = _mm_clmulepi64_si128(a, b, 0x00), h = _mm_clmulepi64_si128(a, b, 0x11);
    __m128i m = _mm_xor_si128(_mm_clmulepi64_si128(a, b, 0x01), _mm_clmulepi64_si128(a, b, 0x10));
    *lo = _mm_xor_si128(l, _mm_slli_si128(m, 8)); *hi = _mm_xor_si128(h, _mm_srli_si128(m, 8));
}
static inline void mul256_raw(const g256 *a, const g256 *b, uint64_t p[8]) {
    __m128i a0 = _mm_loadu_si128((const __m128i *)a->w), a1 = _mm_loadu_si128((const __m128i *)(a->w + 2));
    __m128i b0 = _mm_loadu_si128((const __m128i *)b->w), b1 = _mm_loadu_si128((const __m128i *)(b->w + 2));
    __m128i l0, l1, h0, h1, m0, m1;
    mul128(a0, b0, &l0, &l1); mul128(a1, b1, &h0, &h1);
    mul128(_mm_xor_si128(a0, a1), _mm_xor_si128(b0, b1), &m0, &m1);
    m0 = _mm_xor_si128(m0, _mm_xor_si128(l0, h0)); m1 = _mm_xor_si128(m1, _mm_xor_si128(l1, h1));
    _mm_storeu_si128((__m128i *)p, l0); _mm_storeu_si128((__m128i *)(p + 2), _mm_xor_si128(l1, m0));
    _mm_storeu_si128((__m128i *)(p + 4), _mm_xor_si128(h0, m1)); _mm_storeu_si128((__m128i *)(p + 6), h1);
}
#endif
static inline g256 g_mul(g256 a, g256 b) {
    uint64_t p[8] = {0}, lo, hi;
#if defined(__PCLMUL__)
    (void)lo; (void)hi; mul256_raw(&a, &b, p);
#else
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { clmul64(a.w[i], b.w[j], &lo, &hi); p[i + j] ^= lo; p[i + j + 1] ^= hi; }
#endif
    /* reduce: x^256 = x^10 + x^5 + x^2 + 1 */
    uint64_t *h = p + 4, o[5];
    for (int i = 0; i < 4; i++) o[i] = h[i] ^ (h[i] << 2) ^ (h[i] << 5) ^ (h[i] << 10);
    o[4] = 0;
    for (int i = 1; i < 4; i++) o[i] ^= (h[i - 1] >> 62) ^ (h[i - 1] >> 59) ^ (h[i - 1] >> 54);
    o[4] = (h[3] >> 62) ^ (h[3] >> 59) ^ (h[3] >> 54);        /* bits 256..265 of h*g */
    uint64_t t = o[4];
    o[0] ^= t ^ (t << 2) ^ (t << 5) ^ (t << 10);               /* t < 2^10: t*g < 2^20, no further carry */
    g256 r; for (int i = 0; i < 4; i++) r.w[i] = p[i] ^ o[i];
    g256_mults++;
    return r;
}
static const g256 G_ONE = {{1, 0, 0, 0}};
static inline g256 g_eq(g256 t, g256 x) { /* (1+t)(1+x) + t x = 1 + t + x */
    g256 r = g_add(t, x); r.w[0] ^= 1; return r;
}
