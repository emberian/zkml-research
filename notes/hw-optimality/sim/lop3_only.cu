// One inline-PTX lop3 kernel, to record whether GPGPU-Sim's PTX parser accepts lop3.b32.
#include <cstdio>
#include <cstdint>
__global__ void k(uint32_t *p) { uint32_t x = p[threadIdx.x]; asm volatile("lop3.b32 %0, %0, %1, %2, 0x96;" : "+r"(x) : "r"(x), "r"(x)); p[threadIdx.x] = x; }
int main() { uint32_t *p; cudaMalloc(&p, 128); k<<<1, 32>>>(p); printf("rc=%d\n", (int)cudaDeviceSynchronize()); }
