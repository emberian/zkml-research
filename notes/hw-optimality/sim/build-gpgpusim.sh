#!/bin/bash
set -e
. $HOME/lanes/hw-opt-sim/env.sh
cd $HOME/lanes/hw-opt-sim/accel-sim-framework/gpu-simulator/gpgpu-sim
source setup_environment release
t=$(date +%s)
make -j 24 
echo "BUILD rc=$? $(( $(date +%s)-t ))s"
ls -la lib/$GPGPUSIM_CONFIG/
