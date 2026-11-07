#!/bin/bash
# tracerun.sh NAME CFG TRACEDIR : Accel-Sim trace-driven run of TRACEDIR/kernelslist.g with config dir work/CFG
W=$HOME/lanes/hw-opt-sim/work
name=$1 cfg=$2 tr=$3
rm -rf $W/runs/$name && mkdir -p $W/runs/$name && cp $W/$cfg/* $W/runs/$name/ && cd $W/runs/$name
. $HOME/lanes/hw-opt-sim/env.sh
t=$(date +%s)
$HOME/lanes/hw-opt-sim/accel-sim-framework/gpu-simulator/build/accel-sim.out -trace $W/$tr/kernelslist.g -config ./gpgpusim.config -config ./trace.config > out.log 2>&1
echo "SIMRUN rc=$? wall=$(( $(date +%s) - t ))s trace=$tr" >> out.log
