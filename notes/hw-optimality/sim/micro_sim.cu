// Simulator-sized micro kernels for GPGPU-Sim PTX mode (lane hw-opt-sim, 2026-11-06).
// GPGPU-Sim's PTX front end has no mma.sync and no lop3 (probe_sm75.cu fails to parse; see logs), so this file
// carries what it CAN run: a uint4 copy kernel (proxy for cudaMemcpy D2D), the gemm_probe.cu k_read streaming
// kernel verbatim, a SIMT xor3 rate (C source; ptxas would fuse it to one LOP3, PTX mode sees 2 xor.b32),
// and the only modelled tensor path, wmma m16n16k16 f16 -> f32.
//   micro_sim copy  BYTES        one copy kernel launch + one read launch; prints ns from the simulator's own
//                                cycle count (see gpgpu_simulation_time lines in the log), and checks the copy.
//   micro_sim xor3  BLOCKS ITERS U=8 chains of x = x ^ a ^ y, 128 threads.
//   micro_sim wmma  BLOCKS ITERS U=4 independent accumulators, 128 threads.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <mma.h>
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { fprintf(stderr, "CUDA error %s at %d\n", cudaGetErrorString(e_), __LINE__); exit(2);} } while (0)

__global__ void k_copy(const uint4 *a, uint4 *b, size_t n) {
  for (size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; i < n; i += (size_t)gridDim.x * blockDim.x) b[i] = a[i];
}
__global__ void k_read(const uint4 *p, size_t n, uint32_t *sink) {   // gemm_probe.cu, verbatim
  uint32_t x = 0;
  for (size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; i < n; i += (size_t)gridDim.x * blockDim.x) {
    uint4 v = p[i]; x ^= v.x ^ v.y ^ v.z ^ v.w;
  }
  if (x == 0x9E3779B9u) sink[0] = x;
}
#define U 8
__global__ void k_xor3(long long iters, uint32_t seed, int32_t *sink) {
  uint32_t a = 0x3C003C00u ^ (seed & 1);
  uint32_t x[U];
#pragma unroll
  for (int u = 0; u < U; u++) x[u] = seed + u * 0x9E3779B9u + threadIdx.x;
  for (long long it = 0; it < iters; it++) {
#pragma unroll
    for (int u = 0; u < U; u++) x[u] = x[u] ^ a ^ x[(u + 1) % U];
  }
  int32_t s = 0;
#pragma unroll
  for (int u = 0; u < U; u++) s += (int32_t)x[u];
  if (s == 0x12345678) sink[0] = s;
}
using namespace nvcuda;
#define UW 4
__global__ void k_wmma(long long iters, const half *A, float *out) {
  wmma::fragment<wmma::matrix_a, 16, 16, 16, half, wmma::row_major> fa;
  wmma::fragment<wmma::matrix_b, 16, 16, 16, half, wmma::col_major> fb;
  wmma::fragment<wmma::accumulator, 16, 16, 16, float> acc[UW];
  wmma::load_matrix_sync(fa, A, 16);
  wmma::load_matrix_sync(fb, A, 16);
#pragma unroll
  for (int u = 0; u < UW; u++) wmma::fill_fragment(acc[u], 0.f);
  for (long long it = 0; it < iters; it++) {
#pragma unroll
    for (int u = 0; u < UW; u++) wmma::mma_sync(acc[u], fa, fb, acc[u]);
  }
  int w = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
  for (int u = 0; u < UW; u++) wmma::store_matrix_sync(out + ((size_t)w * UW + u) * 256, acc[u], 16, wmma::mem_row_major);
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
  if (!strcmp(argv[1], "copy")) {
    size_t bytes = strtoull(argv[2], 0, 10), n = bytes / 16;
    std::vector<uint32_t> h(bytes / 4);
    for (size_t i = 0; i < h.size(); i++) h[i] = (uint32_t)(i * 2654435761u);
    uint4 *a, *b; uint32_t *sink;
    CK(cudaMalloc(&a, bytes)); CK(cudaMalloc(&b, bytes)); CK(cudaMalloc(&sink, 4));
    CK(cudaMemcpy(a, h.data(), bytes, cudaMemcpyHostToDevice));
    cudaDeviceProp pr; CK(cudaGetDeviceProperties(&pr, 0));
    int blocks = pr.multiProcessorCount * 16;   // as gemm_probe.cu (T4 runs before 23:40 used a fixed 640 = 40 * 16)
    k_copy<<<blocks, 256>>>(a, b, n); CK(cudaDeviceSynchronize());
    k_read<<<blocks, 256>>>(a, n, sink); CK(cudaDeviceSynchronize());
    std::vector<uint32_t> g(bytes / 4);
    CK(cudaMemcpy(g.data(), b, bytes, cudaMemcpyDeviceToHost));
    printf("{\"cmd\": \"copy\", \"bytes\": %zu, \"copy_ok\": %s}\n", bytes, g == h ? "true" : "false");
  } else if (!strcmp(argv[1], "xor3")) {
    int blocks = atoi(argv[2]); long long iters = atoll(argv[3]);
    int32_t *sink; CK(cudaMalloc(&sink, 4));
    k_xor3<<<blocks, 128>>>(iters, 1, sink); CK(cudaDeviceSynchronize());
    printf("{\"cmd\": \"xor3\", \"blocks\": %d, \"threads\": 128, \"iters\": %lld, \"xor3_ops\": %lld}\n", blocks, iters,
           (long long)blocks * 128 * iters * U);
  } else if (!strcmp(argv[1], "wmma")) {
    int blocks = atoi(argv[2]); long long iters = atoll(argv[3]);
    std::vector<__half> hA(256);
    for (int i = 0; i < 256; i++) hA[i] = __float2half((i % 3) - 1.0f);
    half *A; float *out; CK(cudaMalloc(&A, 512)); CK(cudaMemcpy(A, hA.data(), 512, cudaMemcpyHostToDevice));
    size_t warps = (size_t)blocks * 4; CK(cudaMalloc(&out, warps * UW * 1024));
    k_wmma<<<blocks, 128>>>(iters, A, out); CK(cudaDeviceSynchronize());
    std::vector<float> o(256); CK(cudaMemcpy(o.data(), out, 1024, cudaMemcpyDeviceToHost));
    // check: D = iters * A * A^T (B col-major from the same buffer = A^T)
    int bad = 0;
    for (int r = 0; r < 16; r++) for (int c = 0; c < 16; c++) {
      float s = 0; for (int k = 0; k < 16; k++) s += ((r * 16 + k) % 3 - 1.0f) * ((c * 16 + k) % 3 - 1.0f);
      if (o[r * 16 + c] != s * iters) bad++;
    }
    printf("{\"cmd\": \"wmma\", \"blocks\": %d, \"threads\": 128, \"iters\": %lld, \"macs\": %lld, \"bad\": %d}\n", blocks,
           iters, (long long)warps * UW * iters * 4096, bad);
  }
  return 0;
}
