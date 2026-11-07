#!/bin/bash
# GPGPU-Sim (PTX mode) + Accel-Sim (trace mode) on a CPU-only Debian box, as run on bb2 2026-11-06 (lane hw-opt-sim).
# Run from ~/lanes/hw-opt-sim on bb2 as user build. Builds go through swarm-build (SWARM_MEM_MAX=16G).
set -e
L=$HOME/lanes/hw-opt-sim; mkdir -p $L && cd $L
git clone https://github.com/accel-sim/accel-sim-framework.git            # dev @ 7ba54ded (2026-10-27, v2.0.1)
git clone https://github.com/accel-sim/gpgpu-sim_distribution.git accel-sim-framework/gpu-simulator/gpgpu-sim  # dev @ 4195dd4f
curl -sL https://micro.mamba.pm/api/micromamba/linux-64/latest | tar -xj bin/micromamba   # 2.10.0
export MAMBA_ROOT_PREFIX=$L/mamba
# CUDA 12.8: the newest toolkit GPGPU-Sim's setup_environment calls tested (it warns above 12.8).
./bin/micromamba create -y -p $L/cuda128 -c conda-forge --override-channels cuda-nvcc=12.8.93 cuda-cudart-dev=12.8.90 \
  cuda-cuobjdump=12.8 cuda-nvdisasm=12.8 cuda-profiler-api=12.8 bison flex zlib xorg-makedepend numpy python=3.12 \
  libgl-devel libglx-devel libopengl-devel
mkdir -p shim && ln -sf /usr/lib/x86_64-linux-gnu/libGL.so.1 shim/libGL.so      # Makefile links -lGL
cat > env.sh <<'E2'
L=$HOME/lanes/hw-opt-sim
export CUDA_INSTALL_PATH=$L/cuda128 PATH=$L/cuda128/bin:$PATH
export C_INCLUDE_PATH=$L/cuda128/targets/x86_64-linux/include:$L/cuda128/include CPLUS_INCLUDE_PATH=$L/cuda128/targets/x86_64-linux/include:$L/cuda128/include
export LIBRARY_PATH=$L/shim:$L/cuda128/lib:$L/cuda128/targets/x86_64-linux/lib
E2
cat > simenv.sh <<'E2'
. $HOME/lanes/hw-opt-sim/env.sh
cd $HOME/lanes/hw-opt-sim/accel-sim-framework/gpu-simulator/gpgpu-sim && source setup_environment release >/dev/null && cd - >/dev/null
E2
# lane patches (see gpgpusim-lane.patch): wmma f16 operand decode, mul.hi.u64/s64, dynamic smem in occupancy
git -C accel-sim-framework/gpu-simulator/gpgpu-sim apply $L/work/gpgpusim-lane.patch
SWARM_MEM_MAX=16G swarm-build ./build-gpgpusim.sh    # make -j24 in gpgpu-sim -> lib/gcc-14.2.0/cuda-12080/release/libcudart.so
SWARM_MEM_MAX=16G swarm-build ./build-accelsim.sh    # cmake; -> gpu-simulator/build/accel-sim.out
# apps: nvcc -arch=sm_75 -cudart shared -ccbin x86_64-conda-linux-gnu-g++ -Xlinker --enable-new-dtags X.cu -o X
#   (--enable-new-dtags turns conda's RPATH into RUNPATH so LD_LIBRARY_PATH reaches GPGPU-Sim's libcudart)
