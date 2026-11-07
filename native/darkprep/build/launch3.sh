#!/usr/bin/env bash
# From the Mac: start one darkprep command per custodian box (party 0 forge, 1 bb2, 2 hbox), each under its box's
# rules, detached with a PID file; then wait for all three and print their JSON lines.
#   launch3.sh NAME darkprep-subcommand-and-args...    ({ROOT} is replaced by each box's lane root)
# {MP} is replaced by the party's MP-SPDZ runtime dir. LAYOUT=wired: parties 1 and 2 both on bb2 (each its own
# runtime dir wired<I>/mpspdz with its own key), party 0 on forge; LAYOUT=wired-new / wired-sh: seats.sh's test
# seats; otherwise 0 forge, 1 bb2, 2 hbox.
# Logs and PID files: <ROOT>/runs/NAME[-P<I>].{log,pid} on each box. BIN (default target/release/darkprep, relative to
# <ROOT>) picks the darkprep binary, e.g. a second target dir built while a run holds the first.
set -u
name=$1; shift
declare -a HOST=(dregg-forge bb2 hbox)
declare -a ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /othersys/lanes/dl-gen6-prep)
declare -a WRAP=("nice -n 15 systemd-run --scope -q -p MemoryMax=12G" "nice -n 15 systemd-run --user --scope -q -p MemoryMax=24G" "env SWARM_MEM_MAX=16G swarm-build")
declare -a MP=(mpspdz mpspdz mpspdz)
if [ "${LAYOUT:-}" = wired ]; then
  HOST=(dregg-forge bb2 bb2); ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  WRAP=("${WRAP[0]}" "${WRAP[1]}" "${WRAP[1]}"); MP=(wired0/mpspdz wired1/mpspdz wired2/mpspdz)
elif [ "${LAYOUT:-}" = wired-new ]; then
  # TEST: a new committee (seats.sh new): seat 0 bb2, 1 forge, 2 bb2, each its own TLS and MAC key
  HOST=(bb2 dregg-forge bb2); ROOT=(/home/build/lanes/dl-gen6-prep /srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  F=${WRAP[0]}; B=${WRAP[1]}; WRAP=("$B" "$F" "$B"); MP=(wired-new0/mpspdz wired-new1/mpspdz wired-new2/mpspdz)
elif [ "${LAYOUT:-}" = wired-sh ]; then
  # TEST: the wired seats after an abort (seats.sh sh): same boxes and TLS identities, a MAC key of their own
  HOST=(dregg-forge bb2 bb2); ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  WRAP=("${WRAP[0]}" "${WRAP[1]}" "${WRAP[1]}"); MP=(wired0-sh/mpspdz wired1-sh/mpspdz wired2-sh/mpspdz)
elif [ "${LAYOUT:-}" = wired-new-sh ]; then
  # TEST: the wired-new seats after an abort (seats.sh newsh)
  HOST=(bb2 dregg-forge bb2); ROOT=(/home/build/lanes/dl-gen6-prep /srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  F=${WRAP[0]}; B=${WRAP[1]}; WRAP=("$B" "$F" "$B"); MP=(wired-new0-sh/mpspdz wired-new1-sh/mpspdz wired-new2-sh/mpspdz)
elif [ "${LAYOUT:-}" = reh-old ] || [ "${LAYOUT:-}" = reh-new ]; then
  # TEST: the orchestrator rehearsal's committees (seats.sh rehold / rehnew), on the wired seats
  HOST=(dregg-forge bb2 bb2); ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  WRAP=("${WRAP[0]}" "${WRAP[1]}" "${WRAP[1]}"); MP=(${LAYOUT}0/mpspdz ${LAYOUT}1/mpspdz ${LAYOUT}2/mpspdz)
elif L=${LAYOUT:-}; [ "${L#dir:}" != "$L" ]; then
  # LAYOUT=dir:NAME: a seat set from seats.sh fresh NAME PORT (0 forge, 1 bb2, 2 bb2), runtimes NAME<I>/mpspdz
  N=${L#dir:}
  HOST=(dregg-forge bb2 bb2); ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  WRAP=("${WRAP[0]}" "${WRAP[1]}" "${WRAP[1]}"); MP=(${N}0/mpspdz ${N}1/mpspdz ${N}2/mpspdz)
elif [ "${L#dir3:}" != "$L" ]; then
  # LAYOUT=dir3:NAME: a seat set from seats.sh fresh3 NAME PORT on the three custodian boxes (0 forge, 1 bb2, 2 hbox)
  N=${L#dir3:}; MP=(${N}0/mpspdz ${N}1/mpspdz ${N}2/mpspdz)
elif [ "${LAYOUT:-}" = wired-new-sh2 ]; then
  # TEST: the wired-new-sh seats after an abort (seats.sh newsh2)
  HOST=(bb2 dregg-forge bb2); ROOT=(/home/build/lanes/dl-gen6-prep /srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep)
  F=${WRAP[0]}; B=${WRAP[1]}; WRAP=("$B" "$F" "$B"); MP=(wired-new0-sh2/mpspdz wired-new1-sh2/mpspdz wired-new2-sh2/mpspdz)
fi
for i in 0 1 2; do
  r=${ROOT[$i]}
  args=""
  for a in "$@"; do a=${a//\{MP\}/$r/${MP[$i]}}; a=${a//\{I\}/$i}; args+=" $(printf '%q' "${a//\{ROOT\}/$r}")"; done
  ssh ${HOST[$i]} "mkdir -p $r/runs; cd $r; nohup ${WRAP[$i]} $r/${BIN:-target/release/darkprep}$args --party $i > runs/$name-P$i.log 2>&1 < /dev/null & echo \$! > $r/runs/$name-P$i.pid"
done
for i in 0 1 2; do
  r=${ROOT[$i]}
  ssh ${HOST[$i]} "while kill -0 \$(cat $r/runs/$name-P$i.pid) 2>/dev/null; do sleep 2; done; tail -c 3000 $r/runs/$name-P$i.log"
done
