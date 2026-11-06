// GPU form of encode.c's systematic rate-1/4 additive RS over GF(2^16), interleaved over R rows.
// Same message (SplitMix64 stream), same LCH butterflies, same layout; the codeword's SHAKE digest must
// equal encode.c's "cw_lo_digest" for the same (ELL, R). Twiddle t * x uses four 16-entry nibble tables
// per twiddle in shared memory (the GPU analogue of encode.c's NEON/SSSE3 table lookups).
//   ./encode_gpu ELL R REPS [fused]
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <cuda_runtime.h>
extern "C" {
#include "gf16.h"
#include "keccak.h"
}
#define CK(x) do { cudaError_t e = (x); if (e != cudaSuccess) { printf("{\"error\": \"%s line %d\"}\n", cudaGetErrorString(e), __LINE__); exit(1); } } while (0)
static uint64_t sm = 0x243f6a8885a308d3ULL;
static uint64_t splitmix(void) { uint64_t z = (sm += 0x9e3779b97f4a7c15ULL); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static uint16_t W(int i, uint16_t x) { if (i == 0) return x; uint16_t w = W(i - 1, x); return gf_mul(w, w ^ W(i - 1, (uint16_t)(1u << (i - 1)))); }
static uint16_t WT[16][16];
static uint16_t What(int i, uint16_t x) { uint16_t r = 0; for (int j = 0; j < 16; j++) if (x >> j & 1) r ^= WT[i][j]; return r; }

__device__ __forceinline__ uint32_t cmul4(const uint16_t *T, uint32_t lo, uint32_t hi, uint32_t &ohi) {
    // 4 elements: byte e of lo/hi words is element e. T[k*16+v] = t * (v << 4k).
    uint32_t ol = 0, oh = 0;
#pragma unroll
    for (int e = 0; e < 4; e++) {
        uint32_t l = (lo >> (8 * e)) & 255, h = (hi >> (8 * e)) & 255;
        uint32_t y = T[l & 15] ^ T[16 + (l >> 4)] ^ T[32 + (h & 15)] ^ T[48 + (h >> 4)];
        ol |= (y & 255) << (8 * e); oh |= (y >> 8) << (8 * e);
    }
    ohi = oh; return ol;
}
// one LCH layer over block base..base+2^ell of the codeword; tw[g] = twiddle of group g; inv selects order
__global__ void layer(uint32_t *lo, uint32_t *hi, size_t base, int i, int ell, int Rw, const uint16_t *tw,
                      const uint16_t *exp_t, const int32_t *log_t, int inv, int chunks) {
    __shared__ uint16_t T[64];
    int g = blockIdx.x / chunks, ch = blockIdx.x % chunks;
    uint16_t t = tw[g];
    if (threadIdx.x < 64) {
        int k = threadIdx.x >> 4, v = threadIdx.x & 15; uint32_t x = (uint32_t)v << (4 * k);
        T[threadIdx.x] = (t && x) ? exp_t[log_t[t] + log_t[x]] : 0;
    }
    __syncthreads();
    size_t half = (size_t)1 << i, items = half * Rw;
    size_t it = (size_t)ch * blockDim.x + threadIdx.x;
    if (it >= items) return;
    size_t kk = it / Rw, r = it % Rw;
    size_t u = (base + ((size_t)g << (i + 1)) + kk) * Rw + r, v = u + half * Rw;
    uint32_t ul = lo[u], uh = hi[u], vl = lo[v], vh = hi[v], ph;
    if (!inv) {
        if (t) { uint32_t pl = cmul4(T, vl, vh, ph); ul ^= pl; uh ^= ph; }
        vl ^= ul; vh ^= uh;
    } else {
        vl ^= ul; vh ^= uh;
        if (t) { uint32_t pl = cmul4(T, vl, vh, ph); ul ^= pl; uh ^= ph; }
    }
    lo[u] = ul; hi[u] = uh; lo[v] = vl; hi[v] = vh;
}

// FUSED: up to S_MAX consecutive layers [lo, lo+s) of one block in shared memory per pass (the per-layer kernel
// above makes one HBM round trip per layer; T4 run redesign-encode-t4-01 measured that HBM-bound).
#ifndef S_MAX
#define S_MAX 6
#endif
#ifndef RWT
#define RWT 32
#endif
__global__ void fused(uint32_t *lo_, uint32_t *hi_, size_t base, int lo, int s, int ell, int Rw,
                      const uint16_t *const *twl, const uint16_t *exp_t, const int32_t *log_t, int inv) {
    __shared__ uint32_t DL[(1 << S_MAX) * RWT], DH[(1 << S_MAX) * RWT];
    __shared__ uint16_t TB[(1 << S_MAX) * 64];      // table j*64.. for twiddle slot j
    __shared__ uint16_t TW[1 << S_MAX];
    int chunks = Rw / RWT;
    size_t tile = blockIdx.x / chunks; int ch = blockIdx.x % chunks;
    size_t off = tile & (((size_t)1 << lo) - 1), hip = tile >> lo;
    size_t p0 = base + hip * ((size_t)1 << (lo + s)) + off;          // position of m = 0
    int M = 1 << s;
    // slots: layer i = lo + j uses 2^(s-1-j) twiddles; slot index = (2^(s-1-j) - 1) + local group
    for (int j = 0; j < s; j++) {
        int i = lo + j, nt = 1 << (s - 1 - j);
        size_t g0 = (p0 - base) >> (i + 1);
        for (int q = threadIdx.x; q < nt; q += blockDim.x) TW[nt - 1 + q] = twl[i][g0 + q];
    }
    __syncthreads();
#ifdef TABLE_GATHER
    for (int e = threadIdx.x; e < (M - 1) * 64; e += blockDim.x) {
        int slot = e >> 6, k = (e >> 4) & 3, v = e & 15; uint16_t t = TW[slot]; uint32_t x = (uint32_t)v << (4 * k);
        TB[e] = (t && x) ? exp_t[log_t[t] + log_t[x]] : 0;
    }
#else
    // t*x is GF(2)-linear in x: gather only t * 2^m (16 per twiddle), then each entry is an XOR of <= 4 of them
    __shared__ uint16_t BAS[(1 << S_MAX) * 16];
    for (int e = threadIdx.x; e < (M - 1) * 16; e += blockDim.x) {
        int slot = e >> 4, m = e & 15; uint16_t t = TW[slot];
        BAS[e] = t ? exp_t[log_t[t] + log_t[1u << m]] : 0;  // t times the basis element with bit m set
    }
    __syncthreads();
    for (int e = threadIdx.x; e < (M - 1) * 64; e += blockDim.x) {
        int slot = e >> 6, k = (e >> 4) & 3, v = e & 15; const uint16_t *bs = BAS + slot * 16 + 4 * k;
        TB[e] = (v & 1 ? bs[0] : 0) ^ (v & 2 ? bs[1] : 0) ^ (v & 4 ? bs[2] : 0) ^ (v & 8 ? bs[3] : 0);
    }
#endif
    for (int e = threadIdx.x; e < M * RWT; e += blockDim.x) {
        int m = e / RWT, r = e % RWT; size_t gi = (p0 + ((size_t)m << lo)) * Rw + ch * RWT + r;
        DL[e] = lo_[gi]; DH[e] = hi_[gi];
    }
    __syncthreads();
    for (int jj = 0; jj < s; jj++) {
        int j = inv ? jj : s - 1 - jj, h = 1 << j, nt = 1 << (s - 1 - j);
        for (int e = threadIdx.x; e < (M / 2) * RWT; e += blockDim.x) {
            int b = e / RWT, r = e % RWT;
            int grp = b >> j, kk = b & (h - 1);
            int mu = (grp << (j + 1)) + kk, mv = mu + h;
            const uint16_t *T = TB + (size_t)(nt - 1 + grp) * 64; uint16_t t = TW[nt - 1 + grp];
            uint32_t ul = DL[mu * RWT + r], uh = DH[mu * RWT + r], vl = DL[mv * RWT + r], vh = DH[mv * RWT + r], ph;
            if (!inv) { if (t) { uint32_t pl = cmul4(T, vl, vh, ph); ul ^= pl; uh ^= ph; } vl ^= ul; vh ^= uh; }
            else { vl ^= ul; vh ^= uh; if (t) { uint32_t pl = cmul4(T, vl, vh, ph); ul ^= pl; uh ^= ph; } }
            DL[mu * RWT + r] = ul; DH[mu * RWT + r] = uh; DL[mv * RWT + r] = vl; DH[mv * RWT + r] = vh;
        }
        __syncthreads();
    }
    for (int e = threadIdx.x; e < M * RWT; e += blockDim.x) {
        int m = e / RWT, r = e % RWT; size_t gi = (p0 + ((size_t)m << lo)) * Rw + ch * RWT + r;
        lo_[gi] = DL[e]; hi_[gi] = DH[e];
    }
}
static void run_fft_fused(uint32_t *lo, uint32_t *hi, size_t base, int ell, int Rw, uint16_t *const *dtwl, int inv,
                          const uint16_t *exp_t, const int32_t *log_t) {
    // passes of up to S_MAX layers; forward runs high layers first
    int npass = (ell + S_MAX - 1) / S_MAX;
    for (int q = 0; q < npass; q++) {
        int pidx = inv ? q : npass - 1 - q;
        int lo_l = pidx * S_MAX, s = (ell - lo_l) < S_MAX ? (ell - lo_l) : S_MAX;
        size_t tiles = (size_t)1 << (ell - s);
        fused<<<(unsigned)(tiles * (Rw / RWT)), 256>>>(lo, hi, base, lo_l, s, ell, Rw, (const uint16_t *const *)dtwl, exp_t, log_t, inv);
    }
}
struct Plan { int ell, Rw; std::vector<uint16_t *> tw[4]; };
static void run_fft(uint32_t *lo, uint32_t *hi, size_t base, int ell, int Rw, uint16_t **twl, int inv,
                    const uint16_t *exp_t, const int32_t *log_t) {
    for (int s = 0; s < ell; s++) {
        int i = inv ? s : ell - 1 - s;
        size_t groups = (size_t)1 << (ell - 1 - i), items = ((size_t)1 << i) * Rw;
        int chunks = (int)((items + 255) / 256);
        layer<<<(unsigned)(groups * chunks), 256>>>(lo, hi, base, i, ell, Rw, twl[i], exp_t, log_t, inv, chunks);
    }
}
int main(int argc, char **argv) {
    gf_init();
    for (int a = 0; a < 16; a++) for (int j = 0; j < 16; j++) WT[a][j] = gf_mul(W(a, (uint16_t)(1u << j)), gf_inv(W(a, (uint16_t)(1u << a))));
    int ell = atoi(argv[1]), R = atoi(argv[2]), reps = argc > 3 ? atoi(argv[3]) : 5;
    if (R % 4) { printf("{\"error\": \"R must be a multiple of 4\"}\n"); return 1; }
    int Rw = R / 4; size_t k = (size_t)1 << ell, n = 4 * k;
    std::vector<uint8_t> lo(n * R), hi(n * R);
    for (size_t i = 0; i < k * R; i++) { uint64_t z = splitmix(); lo[i] = z & 255; hi[i] = (z >> 8) & 255; }
    // twiddles per coset c (shift c<<ell), layer i, group g
    uint16_t *twd[4][16];
    for (int c = 0; c < 4; c++) for (int i = 0; i < ell; i++) {
        size_t groups = (size_t)1 << (ell - 1 - i); std::vector<uint16_t> h(groups);
        uint16_t ws = What(i, (uint16_t)(c << ell));
        for (size_t g = 0; g < groups; g++) h[g] = ws ^ What(i, (uint16_t)(g << (i + 1)));
        CK(cudaMalloc(&twd[c][i], groups * 2)); CK(cudaMemcpy(twd[c][i], h.data(), groups * 2, cudaMemcpyHostToDevice));
    }
    uint16_t **dtwl[4];
    for (int c = 0; c < 4; c++) { CK(cudaMalloc(&dtwl[c], 16 * sizeof(uint16_t *))); CK(cudaMemcpy(dtwl[c], twd[c], ell * sizeof(uint16_t *), cudaMemcpyHostToDevice)); }
    int use_fused = argc > 4 && !strcmp(argv[4], "fused");
    if (use_fused && Rw % RWT) { printf("{\"error\": \"fused needs R multiple of 128\"}\n"); return 1; }
#define FFT(base_, c_, inv_) do { if (use_fused) run_fft_fused(dlo, dhi, base_, ell, Rw, dtwl[c_], inv_, dexp, dlog); else run_fft(dlo, dhi, base_, ell, Rw, twd[c_], inv_, dexp, dlog); } while (0)
    uint16_t *dexp; int32_t *dlog;
    CK(cudaMalloc(&dexp, sizeof GF_EXP)); CK(cudaMemcpy(dexp, GF_EXP, sizeof GF_EXP, cudaMemcpyHostToDevice));
    CK(cudaMalloc(&dlog, sizeof GF_LOG)); CK(cudaMemcpy(dlog, GF_LOG, sizeof GF_LOG, cudaMemcpyHostToDevice));
    uint32_t *dlo, *dhi, *slo, *shi; size_t bytes = n * R, kb = k * R;
    CK(cudaMalloc(&dlo, bytes)); CK(cudaMalloc(&dhi, bytes)); CK(cudaMalloc(&slo, kb)); CK(cudaMalloc(&shi, kb));
    CK(cudaMemcpy(slo, lo.data(), kb, cudaMemcpyHostToDevice)); CK(cudaMemcpy(shi, hi.data(), kb, cudaMemcpyHostToDevice));
    cudaEvent_t e0, e1; cudaEventCreate(&e0); cudaEventCreate(&e1);
    float best = 1e30f;
    for (int it = 0; it < reps + 1; it++) {
        CK(cudaMemcpy(dlo, slo, kb, cudaMemcpyDeviceToDevice)); CK(cudaMemcpy(dhi, shi, kb, cudaMemcpyDeviceToDevice));
        cudaEventRecord(e0);
        size_t w = k * Rw;  // words per block
        CK(cudaMemcpyAsync(dlo + 3 * w, dlo, kb, cudaMemcpyDeviceToDevice)); CK(cudaMemcpyAsync(dhi + 3 * w, dhi, kb, cudaMemcpyDeviceToDevice));
        FFT(0, 0, 1);
        for (int c = 1; c < 3; c++) {
            CK(cudaMemcpyAsync(dlo + c * w, dlo, kb, cudaMemcpyDeviceToDevice)); CK(cudaMemcpyAsync(dhi + c * w, dhi, kb, cudaMemcpyDeviceToDevice));
            FFT(c * k, c, 0);
        }
        CK(cudaMemcpyAsync(dlo + 3 * w, dlo, kb, cudaMemcpyDeviceToDevice)); CK(cudaMemcpyAsync(dhi + 3 * w, dhi, kb, cudaMemcpyDeviceToDevice));
        CK(cudaMemcpyAsync(dlo, slo, kb, cudaMemcpyDeviceToDevice)); CK(cudaMemcpyAsync(dhi, shi, kb, cudaMemcpyDeviceToDevice));
        FFT(3 * k, 3, 0);
        cudaEventRecord(e1); CK(cudaEventSynchronize(e1)); CK(cudaGetLastError());
        float ms; cudaEventElapsedTime(&ms, e0, e1); if (it && ms < best) best = ms;
    }
    CK(cudaMemcpy(lo.data(), dlo, bytes, cudaMemcpyDeviceToHost));
    uint8_t dg[16]; sponge256(NULL, 0x1f, lo.data(), n * R, dg, 16);
    printf("{\"mode\": \"%s\", \"ell\": %d, \"R\": %d, \"codeword_bytes\": %zu, \"gpu_encode_ms\": %.4f, \"gpu_encode_ns_per_codeword_byte\": %.4f, \"launches\": %d, \"cw_lo_digest\": \"",
           use_fused ? "fused" : "per-layer", ell, R, 2 * bytes, best, best * 1e6 / (2.0 * bytes), use_fused ? 5 * ((ell + S_MAX - 1) / S_MAX) : 5 * ell);
    for (int i = 0; i < 16; i++) printf("%02x", dg[i]);
    printf("\"}\n");
    return 0;
}
