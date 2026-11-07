#!/usr/bin/env bash
# From the Mac: start one darkprep command per custodian box (party 0 forge, 1 bb2, 2 hbox), each under its box's
# rules, detached with a PID file; then wait for all three and print their JSON lines.
#   launch3.sh NAME darkprep-subcommand-and-args...    ({ROOT} is replaced by each box's lane root)
# Logs and PID files: <ROOT>/runs/NAME.{log,pid} on each box.
set -u
name=$1; shift
declare -a HOST=(dregg-forge bb2 hbox)
declare -a ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /othersys/lanes/dl-gen6-prep)
declare -a WRAP=("nice -n 15 systemd-run --scope -q -p MemoryMax=12G" "nice -n 15 systemd-run --user --scope -q -p MemoryMax=24G" "env SWARM_MEM_MAX=16G swarm-build")
for i in 0 1 2; do
  r=${ROOT[$i]}
  args=""
  for a in "$@"; do args+=" $(printf '%q' "${a//\{ROOT\}/$r}")"; done
  ssh ${HOST[$i]} "mkdir -p $r/runs; cd $r; nohup ${WRAP[$i]} $r/target/release/darkprep$args --party $i > runs/$name.log 2>&1 < /dev/null & echo \$! > $r/runs/$name.pid"
done
for i in 0 1 2; do
  r=${ROOT[$i]}
  ssh ${HOST[$i]} "while kill -0 \$(cat $r/runs/$name.pid) 2>/dev/null; do sleep 2; done; tail -c 3000 $r/runs/$name.log"
done
