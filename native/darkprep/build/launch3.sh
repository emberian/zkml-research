#!/usr/bin/env bash
# From the Mac: start one darkprep command per custodian box (party 0 forge, 1 bb2, 2 hbox), each under its box's
# rules, detached with a PID file; then wait for all three and print their JSON lines.
#   launch3.sh NAME darkprep-subcommand-and-args...    ({ROOT} is replaced by each box's lane root)
# {MP} is replaced by the party's MP-SPDZ runtime dir. LAYOUT=wired: parties 1 and 2 both on bb2 (each its own
# runtime dir wired<I>/mpspdz with its own key), party 0 on forge; otherwise 0 forge, 1 bb2, 2 hbox.
# Logs and PID files: <ROOT>/runs/NAME[-P<I>].{log,pid} on each box.
set -u
name=$1; shift
declare -a HOST=(dregg-forge bb2 hbox)
declare -a ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /othersys/lanes/dl-gen6-prep)
declare -a WRAP=("nice -n 15 systemd-run --scope -q -p MemoryMax=12G" "nice -n 15 systemd-run --user --scope -q -p MemoryMax=24G" "env SWARM_MEM_MAX=16G swarm-build")
declare -a MP=(mpspdz mpspdz mpspdz)
if [ "${LAYOUT:-}" = wired ]; then
  HOST=(dregg-forge bb2 bb2); ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  WRAP=("${WRAP[0]}" "${WRAP[1]}" "${WRAP[1]}"); MP=(wired0/mpspdz wired1/mpspdz wired2/mpspdz)
fi
for i in 0 1 2; do
  r=${ROOT[$i]}
  args=""
  for a in "$@"; do a=${a//\{MP\}/$r/${MP[$i]}}; a=${a//\{I\}/$i}; args+=" $(printf '%q' "${a//\{ROOT\}/$r}")"; done
  ssh ${HOST[$i]} "mkdir -p $r/runs; cd $r; nohup ${WRAP[$i]} $r/target/release/darkprep$args --party $i > runs/$name-P$i.log 2>&1 < /dev/null & echo \$! > $r/runs/$name-P$i.pid"
done
for i in 0 1 2; do
  r=${ROOT[$i]}
  ssh ${HOST[$i]} "while kill -0 \$(cat $r/runs/$name-P$i.pid) 2>/dev/null; do sleep 2; done; tail -c 3000 $r/runs/$name-P$i.log"
done
