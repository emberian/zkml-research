/* Packed-binary commitment kernel (notes/redesign): systematic rate-1/4 additive RS over GF(2^16)
 * (Lin-Chung-Han novel basis), interleaved over R rows, then a cSHAKE-shaped Keccak Merkle tree with one
 * WIDE leaf per codeword column. A Tower256 element is 16 GF(2^16) coordinates and a T_4 twiddle acts on
 * them coordinate-wise, so R = 16 * (Tower256 rows) is the packed-Tower256 encode with T_4 twiddles.
 *   ./encode check  ELL R            -> prints message and codeword (check_encode.py compares with Lagrange)
 *   ./encode bench  ELL R REPS       -> timings and a SHAKE digest of the codeword
 *   ./encode keccak N                -> Keccak-f/s on this core
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "gf16.h"
#include "keccak.h"
#if defined(__aarch64__)
#include <arm_neon.h>
#elif defined(__SSSE3__)
#include <tmmintrin.h>
#endif

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t sm = 0x243f6a8885a308d3ULL;
static uint64_t splitmix(void) { uint64_t z = (sm += 0x9e3779b97f4a7c15ULL); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }

/* basis v_i = bit i; What_i(x) = W_i(x)/W_i(v_i), W_0(x)=x, W_{i+1}(x)=W_i(x)(W_i(x)+W_i(v_i)) */
static uint16_t W(int i, uint16_t x) { if (i == 0) return x; uint16_t w = W(i - 1, x); return gf_mul(w, w ^ W(i - 1, (uint16_t)(1u << (i - 1)))); }
static uint16_t What_slow(int i, uint16_t x) { return gf_mul(W(i, x), gf_inv(W(i, (uint16_t)(1u << i)))); }
/* What_i is GF(2)-linear: tabulate it on the basis once, then XOR (fixed per shape, like a twiddle table) */
static uint16_t WT[16][16]; static int wt_ready;
static uint16_t What(int i, uint16_t x) {
    if (!wt_ready) { for (int a = 0; a < 16; a++) for (int j = 0; j < 16; j++) WT[a][j] = What_slow(a, (uint16_t)(1u << j)); wt_ready = 1; }
    uint16_t r = 0; for (int j = 0; j < 16; j++) if (x >> j & 1) r ^= WT[i][j]; return r;
}

/* data: lo/hi byte planes, element (index p, row r) at [p*R + r] */
typedef struct { int R; uint8_t *lo, *hi; } vec_t;

/* a[p] ^= c * a[q] over all R rows (the hot loop) */
static void axpy(const vec_t *a, size_t p, size_t q, uint16_t c) {
    cmul_t m; cmul_make(&m, c);
    uint8_t *dl = a->lo + p * a->R, *dh = a->hi + p * a->R;
    const uint8_t *sl = a->lo + q * a->R, *sh = a->hi + q * a->R;
    int r = 0;
#if defined(__aarch64__) || defined(__SSSE3__)
    /* split tables: for nibble k, lo and hi output bytes */
    uint8_t TL[4][16], TH[4][16];
    for (int k = 0; k < 4; k++) for (int v = 0; v < 16; v++) { TL[k][v] = m.t[k][v] & 255; TH[k][v] = m.t[k][v] >> 8; }
#endif
#if defined(__aarch64__)
    uint8x16_t tl0 = vld1q_u8(TL[0]), tl1 = vld1q_u8(TL[1]), tl2 = vld1q_u8(TL[2]), tl3 = vld1q_u8(TL[3]);
    uint8x16_t th0 = vld1q_u8(TH[0]), th1 = vld1q_u8(TH[1]), th2 = vld1q_u8(TH[2]), th3 = vld1q_u8(TH[3]);
    uint8x16_t m15 = vdupq_n_u8(15);
    for (; r + 16 <= a->R; r += 16) {
        uint8x16_t xl = vld1q_u8(sl + r), xh = vld1q_u8(sh + r);
        uint8x16_t n0 = vandq_u8(xl, m15), n1 = vshrq_n_u8(xl, 4), n2 = vandq_u8(xh, m15), n3 = vshrq_n_u8(xh, 4);
        uint8x16_t ol = veorq_u8(veorq_u8(vqtbl1q_u8(tl0, n0), vqtbl1q_u8(tl1, n1)), veorq_u8(vqtbl1q_u8(tl2, n2), vqtbl1q_u8(tl3, n3)));
        uint8x16_t oh = veorq_u8(veorq_u8(vqtbl1q_u8(th0, n0), vqtbl1q_u8(th1, n1)), veorq_u8(vqtbl1q_u8(th2, n2), vqtbl1q_u8(th3, n3)));
        vst1q_u8(dl + r, veorq_u8(vld1q_u8(dl + r), ol)); vst1q_u8(dh + r, veorq_u8(vld1q_u8(dh + r), oh));
    }
#elif defined(__SSSE3__)
    __m128i tl0 = _mm_loadu_si128((void *)TL[0]), tl1 = _mm_loadu_si128((void *)TL[1]), tl2 = _mm_loadu_si128((void *)TL[2]), tl3 = _mm_loadu_si128((void *)TL[3]);
    __m128i th0 = _mm_loadu_si128((void *)TH[0]), th1 = _mm_loadu_si128((void *)TH[1]), th2 = _mm_loadu_si128((void *)TH[2]), th3 = _mm_loadu_si128((void *)TH[3]);
    __m128i m15 = _mm_set1_epi8(15);
    for (; r + 16 <= a->R; r += 16) {
        __m128i xl = _mm_loadu_si128((void *)(sl + r)), xh = _mm_loadu_si128((void *)(sh + r));
        __m128i n0 = _mm_and_si128(xl, m15), n1 = _mm_and_si128(_mm_srli_epi16(xl, 4), m15);
        __m128i n2 = _mm_and_si128(xh, m15), n3 = _mm_and_si128(_mm_srli_epi16(xh, 4), m15);
        __m128i ol = _mm_xor_si128(_mm_xor_si128(_mm_shuffle_epi8(tl0, n0), _mm_shuffle_epi8(tl1, n1)), _mm_xor_si128(_mm_shuffle_epi8(tl2, n2), _mm_shuffle_epi8(tl3, n3)));
        __m128i oh = _mm_xor_si128(_mm_xor_si128(_mm_shuffle_epi8(th0, n0), _mm_shuffle_epi8(th1, n1)), _mm_xor_si128(_mm_shuffle_epi8(th2, n2), _mm_shuffle_epi8(th3, n3)));
        _mm_storeu_si128((void *)(dl + r), _mm_xor_si128(_mm_loadu_si128((void *)(dl + r)), ol));
        _mm_storeu_si128((void *)(dh + r), _mm_xor_si128(_mm_loadu_si128((void *)(dh + r)), oh));
    }
#endif
    for (; r < a->R; r++) { uint16_t y = cmul(&m, (uint16_t)(sl[r] | sh[r] << 8)); dl[r] ^= y & 255; dh[r] ^= y >> 8; }
}
static void addv(const vec_t *a, size_t p, size_t q) { /* a[p] ^= a[q] */
    uint8_t *dl = a->lo + p * a->R, *dh = a->hi + p * a->R; const uint8_t *sl = a->lo + q * a->R, *sh = a->hi + q * a->R;
    for (int r = 0; r < a->R; r++) { dl[r] ^= sl[r]; dh[r] ^= sh[r]; }
}
/* forward LCH on a[base .. base+2^ell): novel coefficients -> values at shift + span(v_0..v_{ell-1}) */
static void fft(const vec_t *a, size_t base, int ell, uint16_t shift) {
    for (int i = ell - 1; i >= 0; i--) {
        uint16_t ws = What(i, shift);
        for (size_t b = 0; b < ((size_t)1 << ell); b += (size_t)2 << i) {
            uint16_t t = ws ^ What(i, (uint16_t)b);
            for (size_t k = 0; k < ((size_t)1 << i); k++) {
                size_t u = base + b + k, v = u + ((size_t)1 << i);
                if (t) axpy(a, u, v, t);
                addv(a, v, u);
            }
        }
    }
}
static void ifft(const vec_t *a, size_t base, int ell, uint16_t shift) {
    for (int i = 0; i < ell; i++) {
        uint16_t ws = What(i, shift);
        for (size_t b = 0; b < ((size_t)1 << ell); b += (size_t)2 << i) {
            uint16_t t = ws ^ What(i, (uint16_t)b);
            for (size_t k = 0; k < ((size_t)1 << i); k++) {
                size_t u = base + b + k, v = u + ((size_t)1 << i);
                addv(a, v, u);
                if (t) axpy(a, u, v, t);
            }
        }
    }
}
/* systematic encode: cw[0..k) = message (values on span(v_0..v_{ell-1})); cw[c*k..) = values on coset c */
static void encode(const vec_t *cw, int ell) {
    size_t k = (size_t)1 << ell, row = (size_t)cw->R;
    /* block 3 keeps a copy of the message; block 0 becomes the novel coefficients */
    memcpy(cw->lo + 3 * k * row, cw->lo, k * row); memcpy(cw->hi + 3 * k * row, cw->hi, k * row);
    ifft(cw, 0, ell, 0);
    for (int c = 1; c < 3; c++) {
        memcpy(cw->lo + c * k * row, cw->lo, k * row); memcpy(cw->hi + c * k * row, cw->hi, k * row);
        fft(cw, c * k, ell, (uint16_t)(c << ell));
    }
    /* swap: block 0 <- message copy, block 3 <- coefficients, then evaluate coset 3 */
    for (size_t i = 0; i < k * row; i++) {
        uint8_t t = cw->lo[i]; cw->lo[i] = cw->lo[3 * k * row + i]; cw->lo[3 * k * row + i] = t;
        t = cw->hi[i]; cw->hi[i] = cw->hi[3 * k * row + i]; cw->hi[3 * k * row + i] = t;
    }
    fft(cw, 3 * k, ell, (uint16_t)(3 << ell));
}
/* Merkle over 4k wide leaves, cSHAKE-shaped (midstate of a customization block, ds 0x04) */
static long merkle(const vec_t *cw, size_t n, uint8_t root[32], const uint64_t *mid) {
    long perms = 0; size_t lb = 2 * (size_t)cw->R + 1;
    uint8_t *leaf = malloc(lb), *lvl = malloc(n * 32), buf[65];
    for (size_t j = 0; j < n; j++) {
        leaf[0] = 0; memcpy(leaf + 1, cw->lo + j * cw->R, cw->R); memcpy(leaf + 1 + cw->R, cw->hi + j * cw->R, cw->R);
        perms += sponge256(mid, 0x04, leaf, lb, lvl + 32 * j, 32);
    }
    for (size_t m = n; m > 1; m /= 2)
        for (size_t j = 0; j < m / 2; j++) { buf[0] = 1; memcpy(buf + 1, lvl + 64 * j, 64); perms += sponge256(mid, 0x04, buf, 65, lvl + 32 * j, 32); }
    memcpy(root, lvl, 32); free(leaf); free(lvl); return perms;
}

int main(int argc, char **argv) {
    gf_init();
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "keccak")) {
        long n = atol(argv[2]); uint64_t s[25] = {0}; double t = now();
        for (long i = 0; i < n; i++) keccakf(s);
        t = now() - t; printf("{\"keccak_f_per_s\": %.4e, \"ns_per_f\": %.1f, \"chk\": \"%016llx\"}\n", n / t, 1e9 * t / n, (unsigned long long)s[0]);
        uint8_t o[32]; sponge256(NULL, 0x1f, (const uint8_t *)"abc", 3, o, 32);
        printf("shake256(abc)="); for (int i = 0; i < 32; i++) printf("%02x", o[i]); printf("\n");
        return 0;
    }
    int ell = atoi(argv[2]), R = atoi(argv[3]); size_t k = (size_t)1 << ell, n = 4 * k;
    vec_t cw = {R, calloc(n * R, 1), calloc(n * R, 1)};
    for (size_t i = 0; i < k * R; i++) { uint64_t z = splitmix(); cw.lo[i] = z & 255; cw.hi[i] = (z >> 8) & 255; }
    uint64_t mid[25] = {0}; { uint8_t blk[136] = {1, 136, 1, 64, 'r','e','d','e','s','i','g','n'}; for (int i = 0; i < 136; i++) ((uint8_t *)mid)[i] ^= blk[i]; keccakf(mid); }
    if (!strcmp(argv[1], "check")) {
        uint16_t *msg = malloc(k * R * 2);
        for (size_t i = 0; i < k * R; i++) msg[i] = cw.lo[i] | cw.hi[i] << 8;
        encode(&cw, ell);
        printf("{\"ell\": %d, \"R\": %d, \"gen_exp1\": %u, \"msg\": [", ell, R, GF_EXP[1]);
        for (size_t i = 0; i < k * R; i++) printf("%s%u", i ? "," : "", msg[i]);
        printf("], \"cw\": [");
        for (size_t i = 0; i < n * R; i++) printf("%s%u", i ? "," : "", cw.lo[i] | cw.hi[i] << 8);
        printf("]}\n"); return 0;
    }
    int reps = argc > 4 ? atoi(argv[4]) : 3;
    vec_t src = {R, malloc(k * R), malloc(k * R)}; memcpy(src.lo, cw.lo, k * R); memcpy(src.hi, cw.hi, k * R);
    double te = 1e9, th = 1e9; long perms = 0; uint8_t root[32];
    for (int it = 0; it < reps; it++) {
        memcpy(cw.lo, src.lo, k * R); memcpy(cw.hi, src.hi, k * R);
        double t0 = now(); encode(&cw, ell); double t1 = now(); perms = merkle(&cw, n, root, mid); double t2 = now();
        if (t1 - t0 < te) te = t1 - t0; if (t2 - t1 < th) th = t2 - t1;
    }
    uint8_t dg[16]; sponge256(NULL, 0x1f, cw.lo, n * R, dg, 16);
    double mbytes = (double)k * R * 2, cbytes = (double)n * R * 2;
    printf("{\"ell\": %d, \"R\": %d, \"message_bytes\": %.0f, \"codeword_bytes\": %.0f, \"encode_ms\": %.4f, \"merkle_ms\": %.4f, "
           "\"keccak_f\": %ld, \"encode_ns_per_codeword_byte\": %.3f, \"merkle_ns_per_codeword_byte\": %.3f, \"root\": \"",
           ell, R, mbytes, cbytes, te * 1e3, th * 1e3, perms, te * 1e9 / cbytes, th * 1e9 / cbytes);
    for (int i = 0; i < 8; i++) printf("%02x", root[i]);
    printf("\", \"cw_lo_digest\": \""); for (int i = 0; i < 16; i++) printf("%02x", dg[i]); printf("\"}\n");
    return 0;
}
