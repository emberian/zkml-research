#!/usr/bin/env bash
# From the Mac: start or stop darkstep's resumable relay on the three custodian boxes, so MP-SPDZ's links survive
# Wi-Fi drops as stalls (darkstep relay, deploy lane, 9869e89f). Each box: local 127.0.0.1:(15200 + I) is its
# MP-SPDZ party port; 127.0.0.1:(15210 + j) reaches peer j. PID file <ROOT>/runs/relay.pid, log runs/relay.log.
#   relay3.sh start | stop | status
set -u
declare -a HOST=(dregg-forge bb2 hbox)
declare -a ROOT=(/srv/lanes/dl-gen6-prep /home/build/lanes/dl-gen6-prep /othersys/lanes/dl-gen6-prep)
declare -a WRAP=("nice -n 15 systemd-run --scope -q -p MemoryMax=4G" "nice -n 15 systemd-run --user --scope -q -p MemoryMax=4G" "env SWARM_MEM_MAX=4G swarm-build")
A="178.105.4.114:47410 2.31.77.40:47411 127.0.0.1:47412"
for i in 0 1 2; do
  r=${ROOT[$i]}
  case $1 in
    start) ssh ${HOST[$i]} "cd $r; nohup ${WRAP[$i]} $r/target/release/darkstep relay $i $A --tls $r/relaytls --local 127.0.0.1:$((15200 + i)) --forward-base 15210 > runs/relay.log 2>&1 < /dev/null & echo \$! > $r/runs/relay.pid" ;;
    stop) ssh ${HOST[$i]} "test -f $r/runs/relay.pid && kill \$(cat $r/runs/relay.pid) && rm $r/runs/relay.pid" ;;
    status) ssh ${HOST[$i]} "cat $r/runs/relay.pid 2>/dev/null; tail -3 $r/runs/relay.log" ;;
  esac
done
