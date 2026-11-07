// Keccak section of minidregg lane/accel-tower256-gpu:prover/cuda/tower256_fri.cu (commit 367f9370), lines
// 537..(Tower256 rate probe), copied verbatim, plus the file's device macros and a host main for GPGPU-Sim.
// Lane hw-opt-sim, 2026-11-06. The rest of tower256_fri.cu is left out so the simulator parses only Keccak PTX.
//   keccak_sim leaves N        merkle_leaves on N random 4-limb words, 256-thread blocks (as tower256_gpu.py)
//   keccak_sim rate N ITERS    keccak_rate (dependent chain, ROTL, rounds not unrolled), N threads
//   keccak_sim rateshf N ITERS keccak_rate_shf
// Every output word is checked against the same Keccak round macro run on the host with ROTL.
#include <stdint.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
typedef unsigned long long u64;
#define DEV __device__ __forceinline__
#define KERNEL extern "C" __global__
#define KBEGIN(n) { u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; if (i < (u64)(n)) {
#define KEND } }
// Keccak-f[1600], 64-bit lanes.

#ifdef HOST_EMU
static const u64 RC[24] = {
#else
__constant__ u64 RC[24] = {
#endif
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808aull, 0x8000000080008000ull,
    0x000000000000808bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000aull,
    0x000000008000808bull, 0x800000000000008bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800aull, 0x800000008000000aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};

#define ROTL(x, s) (((x) << (s)) | ((x) >> (64 - (s))))
// The same rotation as two 32-bit funnel shifts (SHF.L.W on sm_70+).
#ifdef HOST_EMU
#define ROTF(x, s) ROTL(x, s)
#else
DEV u64 rotf(u64 x, int s) {
    uint32_t lo = (uint32_t)x, hi = (uint32_t)(x >> 32);
    if (s >= 32) { uint32_t t = lo; lo = hi; hi = t; s -= 32; }
    uint32_t nh = __funnelshift_l(lo, hi, s), nl = __funnelshift_l(hi, lo, s);
    return ((u64)nh << 32) | nl;
}
#define ROTF(x, s) rotf(x, s)
#endif

// One round on a[25]: theta, then rho + pi into b (b[y][2x+3y] = rot(a[x][y])), chi, iota.
#define KECCAK_ROUND(round, R) do { \
 \
        u64 c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]; \
        u64 c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]; \
        u64 c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]; \
        u64 c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]; \
        u64 c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]; \
        u64 d0 = c4 ^ R(c1, 1), d1 = c0 ^ R(c2, 1), d2 = c1 ^ R(c3, 1); \
        u64 d3 = c2 ^ R(c4, 1), d4 = c3 ^ R(c0, 1); \
        u64 b0 = a[0] ^ d0; \
        u64 b1 = R(a[6] ^ d1, 44); \
        u64 b2 = R(a[12] ^ d2, 43); \
        u64 b3 = R(a[18] ^ d3, 21); \
        u64 b4 = R(a[24] ^ d4, 14); \
        u64 b5 = R(a[3] ^ d3, 28); \
        u64 b6 = R(a[9] ^ d4, 20); \
        u64 b7 = R(a[10] ^ d0, 3); \
        u64 b8 = R(a[16] ^ d1, 45); \
        u64 b9 = R(a[22] ^ d2, 61); \
        u64 b10 = R(a[1] ^ d1, 1); \
        u64 b11 = R(a[7] ^ d2, 6); \
        u64 b12 = R(a[13] ^ d3, 25); \
        u64 b13 = R(a[19] ^ d4, 8); \
        u64 b14 = R(a[20] ^ d0, 18); \
        u64 b15 = R(a[4] ^ d4, 27); \
        u64 b16 = R(a[5] ^ d0, 36); \
        u64 b17 = R(a[11] ^ d1, 10); \
        u64 b18 = R(a[17] ^ d2, 15); \
        u64 b19 = R(a[23] ^ d3, 56); \
        u64 b20 = R(a[2] ^ d2, 62); \
        u64 b21 = R(a[8] ^ d3, 55); \
        u64 b22 = R(a[14] ^ d4, 39); \
        u64 b23 = R(a[15] ^ d0, 41); \
        u64 b24 = R(a[21] ^ d1, 2); \
        a[0] = b0 ^ (~b1 & b2) ^ RC[round]; \
        a[1] = b1 ^ (~b2 & b3); \
        a[2] = b2 ^ (~b3 & b4); \
        a[3] = b3 ^ (~b4 & b0); \
        a[4] = b4 ^ (~b0 & b1); \
        a[5] = b5 ^ (~b6 & b7); \
        a[6] = b6 ^ (~b7 & b8); \
        a[7] = b7 ^ (~b8 & b9); \
        a[8] = b8 ^ (~b9 & b5); \
        a[9] = b9 ^ (~b5 & b6); \
        a[10] = b10 ^ (~b11 & b12); \
        a[11] = b11 ^ (~b12 & b13); \
        a[12] = b12 ^ (~b13 & b14); \
        a[13] = b13 ^ (~b14 & b10); \
        a[14] = b14 ^ (~b10 & b11); \
        a[15] = b15 ^ (~b16 & b17); \
        a[16] = b16 ^ (~b17 & b18); \
        a[17] = b17 ^ (~b18 & b19); \
        a[18] = b18 ^ (~b19 & b15); \
        a[19] = b19 ^ (~b15 & b16); \
        a[20] = b20 ^ (~b21 & b22); \
        a[21] = b21 ^ (~b22 & b23); \
        a[22] = b22 ^ (~b23 & b24); \
        a[23] = b23 ^ (~b24 & b20); \
        a[24] = b24 ^ (~b20 & b21); \
} while (0)

// Rounds loop not unrolled (the dry-run kernel), unrolled by 2, and fully unrolled.
DEV void keccak_f(u64* a) {
#ifndef HOST_EMU
#pragma unroll 1
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTL);
}
DEV void keccak_f_u2(u64* a) {
#ifndef HOST_EMU
#pragma unroll 2
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTL);
}
DEV void keccak_f_shf(u64* a) {
#ifndef HOST_EMU
#pragma unroll 1
#endif
    for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTF);
}

// Leaf: 0 :: (32 zeros, 1) :: v (66 bytes), cSHAKE pad 0x04 at byte 66, 0x80 at byte 135.
KERNEL void merkle_leaves(const u64* vals, const u64* mid, u64* dig, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k];
    const u64* v = vals + 4 * i;
    a[4] ^= 0x100ull | (v[0] << 16);
    a[5] ^= (v[0] >> 48) | (v[1] << 16);
    a[6] ^= (v[1] >> 48) | (v[2] << 16);
    a[7] ^= (v[2] >> 48) | (v[3] << 16);
    a[8] ^= (v[3] >> 48) | (0x04ull << 16);
    a[16] ^= 0x80ull << 56;
    keccak_f_shf(a);
    for (int k = 0; k < 4; ++k) dig[4 * i + k] = a[k];
    KEND
}

// Node: 1 :: (32 zeros, 1) :: l :: (32 zeros, 1) :: r (131 bytes); pad 0x04 at 131, 0x80 at 135.
// A batch of trees side by side, 2h digests each: next[b h + o] = node(cur[2bh + o], cur[2bh + o + h]).
KERNEL void merkle_nodes(const u64* cur, const u64* mid, u64* next, u64 h, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k];
    u64 b = i / h, o = i % h;
    const u64* l = cur + 4 * (2 * b * h + o);
    const u64* r = l + 4 * h;
    a[0] ^= 1ull;
    a[4] ^= 0x100ull | (l[0] << 16);
    a[5] ^= (l[0] >> 48) | (l[1] << 16);
    a[6] ^= (l[1] >> 48) | (l[2] << 16);
    a[7] ^= (l[2] >> 48) | (l[3] << 16);
    a[8] ^= (l[3] >> 48);
    a[12] ^= (1ull << 16) | (r[0] << 24);
    a[13] ^= (r[0] >> 40) | (r[1] << 24);
    a[14] ^= (r[1] >> 40) | (r[2] << 24);
    a[15] ^= (r[2] >> 40) | (r[3] << 24);
    a[16] ^= (r[3] >> 40) | (0x04ull << 24) | (0x80ull << 56);
    keccak_f_shf(a);
    for (int k = 0; k < 4; ++k) next[4 * i + k] = a[k];
    KEND
}

// Throughput probe: `iters` Keccak-f per thread on a private state; out[i] = lane 0.
KERNEL void keccak_rate(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f(a);
    out[i] = a[0];
    KEND
}

KERNEL void keccak_rate_shf(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f_shf(a);
    out[i] = a[0];
    KEND
}
KERNEL void keccak_rate_u2(const u64* mid, u64* out, u64 iters, u64 n) {
    KBEGIN(n)
    u64 a[25];
    for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
    for (u64 it = 0; it < iters; ++it) keccak_f_u2(a);
    out[i] = a[0];
    KEND
}
// ------------------------------------------------------------------ host (lane hw-opt-sim)
static const u64 HRC[24] = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808aull, 0x8000000080008000ull,
    0x000000000000808bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000aull,
    0x000000008000808bull, 0x800000000000008bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800aull, 0x800000008000000aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};
static void host_keccak_f(u64 *a) {
#define RC HRC
  for (int round = 0; round < 24; ++round) KECCAK_ROUND(round, ROTL);
#undef RC
}
static u64 sm64(u64 &s) { u64 z = (s += 0x9e3779b97f4a7c15ull); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull; z = (z ^ (z >> 27)) * 0x94d049bb133111ebull; return z ^ (z >> 31); }
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { fprintf(stderr, "CUDA error %s at %d\n", cudaGetErrorString(e_), __LINE__); exit(2);} } while (0)
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
  u64 n = strtoull(argv[2], 0, 10), seed = 7, iters = argc > 3 ? strtoull(argv[3], 0, 10) : 0;
  std::vector<u64> mid(25); for (auto &m : mid) m = sm64(seed);
  u64 *dmid; CK(cudaMalloc(&dmid, 200)); CK(cudaMemcpy(dmid, mid.data(), 200, cudaMemcpyHostToDevice));
  size_t bad = 0;
  if (!strcmp(argv[1], "leaves")) {
    std::vector<u64> v(4 * n), dig(4 * n); for (auto &x : v) x = sm64(seed);
    u64 *dv, *dd; CK(cudaMalloc(&dv, 32 * n)); CK(cudaMalloc(&dd, 32 * n));
    CK(cudaMemcpy(dv, v.data(), 32 * n, cudaMemcpyHostToDevice));
    merkle_leaves<<<(unsigned)((n + 255) / 256), 256>>>(dv, dmid, dd, n);
    CK(cudaGetLastError()); CK(cudaDeviceSynchronize());
    CK(cudaMemcpy(dig.data(), dd, 32 * n, cudaMemcpyDeviceToHost));
    for (u64 i = 0; i < n; i++) {
      u64 a[25]; for (int k = 0; k < 25; ++k) a[k] = mid[k];
      const u64 *w = &v[4 * i];
      a[4] ^= 0x100ull | (w[0] << 16); a[5] ^= (w[0] >> 48) | (w[1] << 16); a[6] ^= (w[1] >> 48) | (w[2] << 16);
      a[7] ^= (w[2] >> 48) | (w[3] << 16); a[8] ^= (w[3] >> 48) | (0x04ull << 16); a[16] ^= 0x80ull << 56;
      host_keccak_f(a);
      for (int k = 0; k < 4; ++k) bad += dig[4 * i + k] != a[k];
    }
  } else {
    std::vector<u64> out(n); u64 *dout; CK(cudaMalloc(&dout, 8 * n));
    unsigned blocks = (unsigned)((n + 255) / 256);
    if (!strcmp(argv[1], "rate")) keccak_rate<<<blocks, 256>>>(dmid, dout, iters, n);
    else keccak_rate_shf<<<blocks, 256>>>(dmid, dout, iters, n);
    CK(cudaGetLastError()); CK(cudaDeviceSynchronize());
    CK(cudaMemcpy(out.data(), dout, 8 * n, cudaMemcpyDeviceToHost));
    for (u64 i = 0; i < n; i++) {
      u64 a[25]; for (int k = 0; k < 25; ++k) a[k] = mid[k] ^ (i * 0x9e3779b97f4a7c15ull);
      for (u64 it = 0; it < iters; ++it) host_keccak_f(a);
      bad += out[i] != a[0];
    }
  }
  printf("{\"cmd\": \"%s\", \"n\": %llu, \"iters\": %llu, \"keccak_f\": %llu, \"bad\": %zu}\n", argv[1], n, iters,
         n * (iters ? iters : 1), bad);
  return bad != 0;
}
