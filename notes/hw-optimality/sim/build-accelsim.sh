#!/bin/bash
. $HOME/lanes/hw-opt-sim/env.sh
export PATH=$HOME/lanes/hw-opt-sim/cuda128/bin:$PATH
cd $HOME/lanes/hw-opt-sim/accel-sim-framework/gpu-simulator
source ./setup_environment.sh release
cd ..
t=$(date +%s)
cmake -DCMAKE_PREFIX_PATH=$HOME/lanes/hw-opt-sim/cuda128 -DZLIB_ROOT=$HOME/lanes/hw-opt-sim/cuda128 -S ./gpu-simulator/ -B ./gpu-simulator/build -DCMAKE_BUILD_TYPE=Release -DPython_EXECUTABLE=$HOME/lanes/hw-opt-sim/cuda128/bin/python3 -DPYTHON_EXECUTABLE=$HOME/lanes/hw-opt-sim/cuda128/bin/python3 && cmake --build ./gpu-simulator/build -j16
echo "BUILD rc=$? $(( $(date +%s)-t ))s"
find gpu-simulator/build -maxdepth 3 -type f -name "accel-sim*" | head
