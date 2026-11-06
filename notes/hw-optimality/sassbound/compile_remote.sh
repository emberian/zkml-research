#!/bin/bash
# Compile a .cu for several SASS targets on dregg-forge (no GPU needed) and pull back SASS + ptxas stats.
# usage: compile_remote.sh <file.cu> <outdir> "<arch list>" [extra nvcc flags...]
# Toolkit: /srv/lanes/hw-opt/cuda129 (conda-forge cuda-nvcc 12.9.86, cuobjdump 12.9.82, nvdisasm 12.9.88).
set -euo pipefail
SRC=$1; OUT=$2; ARCHS=${3:-"sm_75 sm_80 sm_90a sm_100a sm_103a"}; shift 3 || true
EXTRA="$*"
REM=/srv/lanes/hw-opt/work/$(basename "$OUT")
mkdir -p "$OUT"
ssh dregg-forge "mkdir -p $REM"
scp -q "$SRC" dregg-forge:$REM/
B=$(basename "$SRC")
ssh dregg-forge "cd $REM && export PATH=/srv/lanes/hw-opt/cuda129/bin:\$PATH && for a in $ARCHS; do
  nice -n 15 nvcc -ccbin /srv/lanes/hw-opt/cuda129/bin/x86_64-conda-linux-gnu-g++ -cubin -O3 -std=c++17 -arch=\$a -Xptxas -v $EXTRA -o \${a}.cubin $B > \${a}.ptxas.txt 2>&1 || { echo FAIL \$a; cat \${a}.ptxas.txt | tail -5; continue; }
  cuobjdump -sass \${a}.cubin > \${a}.sass
done; ls"
for a in $ARCHS; do scp -q dregg-forge:$REM/$a.sass dregg-forge:$REM/$a.ptxas.txt "$OUT"/ 2>/dev/null || true; done
ls -la "$OUT"
