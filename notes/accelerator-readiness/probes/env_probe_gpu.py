"""T4 environment probe: what the Kaggle GPU image offers for our kernels (nvcc, arch, cupy, torch, jax),
plus one compiled-and-run CUDA kernel with an exact readback. Writes ACCEL_RESULTS."""
import json, os, pathlib, subprocess, sys, time
R = {}
def sh(c, t=120):
    r = subprocess.run(c, shell=True, capture_output=True, text=True, timeout=t)
    return (r.stdout + r.stderr).strip()
R["nvidia_smi"] = sh("nvidia-smi --query-gpu=index,name,memory.total,clocks.max.sm,clocks.max.mem,compute_cap,driver_version --format=csv")
R["nvcc"] = sh("which nvcc; nvcc --version | tail -3; ls -d /usr/local/cuda*")
R["cpu"] = sh("nproc; grep -m1 'model name' /proc/cpuinfo; free -g | head -2; df -h /tmp /kaggle/working | tail -2")
R["pip"] = sh(sys.executable + " -m pip list 2>/dev/null | grep -i -E '^(cupy|torch |jax|jaxlib|numpy|triton|numba|pycuda|nvidia-cuda)'")
R["cutlass_hashcat"] = sh("ls /usr/local/cuda/include/cutlass 2>&1 | head -2; which hashcat cutlass_profiler")
src = r'''
#include <cstdio>
#include <cstdint>
__global__ void k(uint64_t *o){ unsigned long long a = 0x1FFFFFFFFFFFFFFFull - threadIdx.x, b = 0x1FFFFFFFFFFFFFF0ull;
  o[2*threadIdx.x] = a*b; o[2*threadIdx.x+1] = __umul64hi(a,b); }
int main(){ uint64_t *d,h[64]; cudaMalloc(&d,512); k<<<1,32>>>(d); cudaMemcpy(h,d,512,cudaMemcpyDeviceToHost);
  for(int i=0;i<32;i++) printf("%llu %llu\n",(unsigned long long)h[2*i],(unsigned long long)h[2*i+1]); return 0; }
'''
w = pathlib.Path("/tmp/accel/envprobe"); w.mkdir(parents=True, exist_ok=True)
(w / "k.cu").write_text(src)
t = time.time()
R["nvcc_build"] = sh(f"cd {w} && nvcc -O2 -arch=sm_75 k.cu -o k 2>&1 && echo BUILD_OK", 300)
R["nvcc_build_s"] = round(time.time() - t, 1)
out = sh(f"{w}/k") if "BUILD_OK" in R["nvcc_build"] else ""
ok = True
for i, line in enumerate(out.splitlines()[:32]):
    a = 0x1FFFFFFFFFFFFFFF - i; b = 0x1FFFFFFFFFFFFFF0
    lo, hi = (int(x) for x in line.split())
    ok &= (lo == (a * b) % 2**64 and hi == (a * b) >> 64)
R["umul64hi_exact"] = ok and bool(out)
print(json.dumps(R, indent=1))
pathlib.Path(os.environ["ACCEL_RESULTS"]).write_text(json.dumps(R, indent=1))
