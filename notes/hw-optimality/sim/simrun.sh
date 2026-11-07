#!/bin/bash
# simrun.sh NAME CFG CMD...   run one app under GPGPU-Sim PTX mode in work/runs/NAME with config dir work/CFG.
# Detached use: nohup setsid ./simrun.sh ... & echo $! > runs/NAME.pid  (the caller writes the PID file)

W=$HOME/lanes/hw-opt-sim/work
name=$1 cfg=$2; shift 2
rm -rf $W/runs/$name && mkdir -p $W/runs/$name && cp $W/$cfg/* $W/runs/$name/ && cd $W/runs/$name
. $HOME/lanes/hw-opt-sim/simenv.sh
t=$(date +%s)
"$@" > out.log 2>&1
echo "SIMRUN rc=$? wall=$(( $(date +%s) - t ))s cmd=$*" >> out.log
