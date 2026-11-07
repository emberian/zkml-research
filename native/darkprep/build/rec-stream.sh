#!/bin/zsh
# The run of record's preprocessing (LowGear N = 16384, -S 60, sealed), one stream per key, from the Mac:
#   rec-stream.sh A OUTDIR   old committee: waits for lg64f (custodian runtimes ROOT/mpspdz), then rec-c0, rec-c1, rec-c2
#                            (2 steps each) and rec-c3 (1 step), sealed under rec/seat<I>
#   rec-stream.sh B OUTDIR   new committee: waits for lg64n (runtimes ROOT/lgnew<I>), then rec-ho (33,554,448 Ar),
#                            rec-n-c0 (1 step) and rec-rel (M = 52), sealed under rec/new<I>
# Run detached: nohup rec-stream.sh A OUTDIR > OUTDIR/A.log 2>&1 & echo $! > OUTDIR/A.pid. Events go to OUTDIR/events.log
# as "<time> <stream> <chunk> start|ok|reattach|skip|FAIL|wait"; the stream stops at the first failure. OUTDIR is
# research/dark_learning_2026_11_06/runs/rec/prep (logs and PID files gitignored; <chunk>.json measurements kept).
# Restartable: a driver started again (after a reboot, say) skips a chunk whose three chunk dirs exist, waits for one
# whose wrappers are still alive by their PID files (it never launches a chunk twice), and launches the rest.
set -u
S=$1; O=$2; cd ${0:A:h}
ev() { echo "$(date -u +%FT%T) $S $*" >> $O/events.log; }
C=(--backend lowgear --extra -S,60,-lg2,64 --mpc-src {ROOT}/native/darkprep/mpc/darkprep.mpc --p 2305843009210515457 --d 4096
   --mode steady --truncs 11,19,7,8,8,19 --threads 8 --step-tapes-only --rs)
export BIN=target-g3/release/darkprep
if [ $S = A ]; then KEY=lg64f; export LAYOUT=; MP={ROOT}/mpspdz; IPF={ROOT}/ips.txt; V=seat; else KEY=lg64n; export LAYOUT=dir3:lgnew; MP={MP}; IPF={ROOT}/ips-lgnew.txt; V=new; fi
done3() { ssh dregg-forge "test -d /srv/lanes/dl-gen6-prep/chunks/$1" && ssh bb2 "test -d /home/build/lanes/dl-gen6-prep/chunks/$1" && ssh hbox "test -d /othersys/lanes/dl-gen6-prep/chunks/$1"; }
alive() { ssh -o ConnectTimeout=20 $1 "kill -0 \$(cat $2/runs/$KEY-P$3.pid) 2>/dev/null"; }
ev "$KEY wait"
until done3 $KEY; do
  for b in "dregg-forge /srv/lanes/dl-gen6-prep 0" "bb2 /home/build/lanes/dl-gen6-prep 1" "hbox /othersys/lanes/dl-gen6-prep 2"; do
    set -- ${=b}; alive $1 $2 $3 || { sleep 120; done3 $KEY && break 2; alive $1 $2 $3 || { ev "$KEY FAIL ($1 wrapper exited without the chunk)"; exit 1; }; }
  done
  sleep 300
done
ev "$KEY ok"
chunk() { # name args...
  local n=$1; shift
  local KEY=$n
  if ssh dregg-forge "test -d /srv/lanes/dl-gen6-prep/chunks/$n-P0" && ssh bb2 "test -d /home/build/lanes/dl-gen6-prep/chunks/$n-P1" && ssh hbox "test -d /othersys/lanes/dl-gen6-prep/chunks/$n-P2"; then
    ev "$n skip (already made)"; return 0
  fi
  if alive dregg-forge /srv/lanes/dl-gen6-prep 0 || alive bb2 /home/build/lanes/dl-gen6-prep 1 || alive hbox /othersys/lanes/dl-gen6-prep 2; then
    ev "$n reattach (wrappers alive)"
  else
    ev "$n start"
    # launch3 starts the three detached wrappers, then waits on them over ssh; that wait is not the verdict
    ./launch3.sh $n party-chunk "${C[@]}" --mpspdz $MP --ipfile $IPF --vault-file {ROOT}/../dl-gen6-deploy/rec/$V{I}/tls/vault.name "$@" --out {ROOT}/chunks/$n-P{I} > $O/$n.out.log 2>&1
  fi
  # the verdict comes from the boxes, not from launch3's ssh wait (which a Mac sleep or roaming can cut): wait for the
  # three wrappers to exit by their PID files, then require the three chunk dirs and fetch each seat's JSON
  while :; do a=0; alive dregg-forge /srv/lanes/dl-gen6-prep 0 && a=1; alive bb2 /home/build/lanes/dl-gen6-prep 1 && a=1; alive hbox /othersys/lanes/dl-gen6-prep 2 && a=1; [ $a = 0 ] && break; sleep 120; done
  if ssh dregg-forge "test -d /srv/lanes/dl-gen6-prep/chunks/$n-P0" && ssh bb2 "test -d /home/build/lanes/dl-gen6-prep/chunks/$n-P1" && ssh hbox "test -d /othersys/lanes/dl-gen6-prep/chunks/$n-P2"; then
    { ssh dregg-forge "cat /srv/lanes/dl-gen6-prep/chunks/$n-P0/chunk-P0.json"; echo; ssh bb2 "cat /home/build/lanes/dl-gen6-prep/chunks/$n-P1/chunk-P1.json"; echo; ssh hbox "cat /othersys/lanes/dl-gen6-prep/chunks/$n-P2/chunk-P2.json"; echo; } > $O/$n.json
    ev "$n ok"
  else ev "$n FAIL"; exit 1; fi
}
if [ $S = A ]; then
  chunk rec-c0 --steps 2 --proof --proof-triples 2225349
  chunk rec-c1 --steps 2 --proof --proof-triples 2225349
  chunk rec-c2 --steps 2 --proof --proof-triples 2225349
  chunk rec-c3 --steps 1 --proof --proof-triples 2225349
else
  chunk rec-ho --handover-ar 33554448
  chunk rec-n-c0 --steps 1 --proof --proof-triples 2225349
  chunk rec-rel --release 52,10,10 --lookup-triples 27 --proof-triples 38666490
fi
ev "stream done"
