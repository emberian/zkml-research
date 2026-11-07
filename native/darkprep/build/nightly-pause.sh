#!/bin/bash
# forge's fn2 nightly (10:00-11:00 UTC): pause this lane's processes on forge by their PID files only, for ONE window.
#   nightly-pause.sh ROOT YYYY-MM-DD     (run detached: nohup ... & echo $! > ROOT/runs/nightly-pause.pid)
# From 10:00:00 to 10:58:30 UTC on that date it SIGSTOPs, every 10 s, any PID named by a prep PID file
# (ROOT/chunks/*.tmp-P*/mascot-P*.pid: MP-SPDZ parties, LowGear included; ROOT/runs/*-P*.pid: darkprep wrappers) whose
# executable (argv[0] basename) is a *-party.x or darkprep, so a chunk that starts inside the window is paused too. At 10:58:30 it
# SIGCONTs exactly the PIDs it stopped (recorded in ROOT/runs/nightly-pause.stopped). It never reads another lane's PID
# files (the deploy lane's nightly.sh pauses dl-custodian). Safe only with the EINTR-fixed MP-SPDZ (mascot 4d50d76f,
# lowgear 38adf2bf). A file ROOT/runs/nightly-pause.skip cancels it before the window.
R=$1; DAY=$2; LOG=$R/runs/nightly-pause.log; ST=$R/runs/nightly-pause.stopped; SKIP=$R/runs/nightly-pause.skip
log() { echo "$(date -u +%FT%T) $*" >> $LOG; }
log "armed for $DAY 10:00:00-10:58:30 UTC"
until [ "$(date -u +%F%H%M%S)" \> "${DAY}095959" ]; do sleep 10; done
[ -e $SKIP ] && { log "skip file present, not pausing"; exit 0; }
[ "$(date -u +%F)" = "$DAY" ] || { log "past $DAY, nothing done"; exit 0; }
: > $ST
while [ "$(date -u +%H%M%S)" -lt 105830 ]; do
  for pf in $R/chunks/*.tmp-P*/mascot-P*.pid $R/runs/*-P*.pid; do
    [ -f "$pf" ] || continue
    p=$(cat "$pf" 2>/dev/null); [ -n "$p" ] || continue
    grep -qx "$p" $ST && continue
    exe=$(tr '\0' '\n' < /proc/$p/cmdline 2>/dev/null | head -1) || continue
    case "$(basename "$exe")" in *-party.x|darkprep) kill -STOP $p && echo $p >> $ST && log "SIGSTOP $p ($pf): $exe";; esac
  done
  sleep 10
done
for p in $(cat $ST); do kill -CONT $p 2>/dev/null && log "SIGCONT $p"; done
log "window over"
