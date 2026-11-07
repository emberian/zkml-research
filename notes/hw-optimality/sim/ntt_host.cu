// Standalone host for one batched forward NTT from accel_rns_ntt.cu (copied verbatim beside this file):
// fwdBr<MODE=0 Shoup, G=3 radix-8>, one pass (E = N), THREADS threads, grid (1, rows), dynamic smem 8N bytes,
// exactly accel_bench_cuda.Ctx.fwd for logE = logN, G = 3. Lane hw-opt-sim, 2026-11-06.
//   ntt_host DIR N L ROWS THREADS REPS   reads DIR/{tw,twq,mc,in,expect}.bin; runs REPS launches on a fresh
//   REPS > 1 re-transforms in place (only the first output is checked); launches 2..REPS are timed with events.
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#include "accel_rns_ntt.cu"
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { fprintf(stderr, "CUDA error %s at %d\n", cudaGetErrorString(e_), __LINE__); exit(2);} } while (0)
static std::vector<u64> slurp(const std::string &p, size_t n) {
  std::vector<u64> v(n); FILE *f = fopen(p.c_str(), "rb");
  if (!f || fread(v.data(), 8, n, f) != n) { fprintf(stderr, "read %s\n", p.c_str()); exit(2); }
  fclose(f); return v;
}
int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: ntt_host DIR N L ROWS THREADS REPS\n"); return 1; }
  std::string d = argv[1]; int N = atoi(argv[2]), L = atoi(argv[3]), rows = atoi(argv[4]), th = atoi(argv[5]), reps = atoi(argv[6]);
  int logN = 0; while ((1 << logN) < N) logN++;
  auto tw = slurp(d + "/tw.bin", (size_t)L * N), twq = slurp(d + "/twq.bin", (size_t)L * N), mc = slurp(d + "/mc.bin", (size_t)L * 8);
  auto in = slurp(d + "/in.bin", (size_t)rows * N), ex = slurp(d + "/expect.bin", (size_t)rows * N);
  u64 *dtw, *dtwq, *dbuf; ModC *dmc;
  CK(cudaMalloc(&dtw, 8ull * L * N)); CK(cudaMalloc(&dtwq, 8ull * L * N)); CK(cudaMalloc(&dmc, 64ull * L));
  CK(cudaMalloc(&dbuf, 8ull * rows * N));
  CK(cudaMemcpy(dtw, tw.data(), 8ull * L * N, cudaMemcpyHostToDevice));
  CK(cudaMemcpy(dtwq, twq.data(), 8ull * L * N, cudaMemcpyHostToDevice));
  CK(cudaMemcpy(dmc, mc.data(), 64ull * L, cudaMemcpyHostToDevice));
  CK(cudaMemcpy(dbuf, in.data(), 8ull * rows * N, cudaMemcpyHostToDevice));
  size_t smem = 8ull * N;
  CK(cudaFuncSetAttribute(fwdBr<0, 3>, cudaFuncAttributeMaxDynamicSharedMemorySize, (int)smem));
  std::vector<u64> out((size_t)rows * N);
  cudaEvent_t e0, e1; CK(cudaEventCreate(&e0)); CK(cudaEventCreate(&e1));
  float ms = 0;
  for (int r = 0; r < reps; r++) {
    if (r == 1) CK(cudaEventRecord(e0));
    fwdBr<0, 3><<<dim3(1, rows), th, smem>>>(dbuf, dtw, dtwq, dmc, logN, logN, L);
    CK(cudaGetLastError());
    if (r == 0) { CK(cudaDeviceSynchronize()); CK(cudaMemcpy(out.data(), dbuf, 8ull * rows * N, cudaMemcpyDeviceToHost)); }
  }
  if (reps > 1) { CK(cudaEventRecord(e1)); CK(cudaEventSynchronize(e1)); CK(cudaEventElapsedTime(&ms, e0, e1)); ms /= (reps - 1); }
  size_t bad = 0; for (size_t i = 0; i < out.size(); i++) bad += out[i] != ex[i];
  printf("{\"cmd\": \"ntt\", \"N\": %d, \"L\": %d, \"rows\": %d, \"threads\": %d, \"reps\": %d, \"words\": %zu, \"bad_words\": %zu, \"ms_per_launch\": %.5f}\n",
         N, L, rows, th, reps, out.size(), bad, ms);
  return bad != 0;
}
