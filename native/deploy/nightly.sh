#!/bin/bash
# nightly.sh LOG STOP CONT PIDFILE...: forge's nightly pause by PID file (MACHINES.md: fn2's 10:00-11:00 UTC).
# Every day at STOP (HHMMSS, UTC) SIGSTOP each live process a PID file names, only if its cmdline is one of this
# run's (dl-custodian, darkstep, dl-owner, or a run.py sampler's sh); at CONT SIGCONT exactly the ones it stopped.
# Launched inside the window it stops at once. PID files that do not exist yet (a new seat) are read each day.
# A SKIP file beside LOG skips a day. Runs until stopped by its own PID file (run.py stop).
LOG=$1 STOP=$2 CONT=$3; shift 3
SKIP=${LOG%.log}.skip
now() { echo $((10#$(date -u +%H%M%S))); }
log() { echo "$(date -u +%FT%TZ) $*" >> "$LOG"; }
log "start: stop $STOP cont $CONT, pid files: $*"
while true; do
  until [ "$(now)" -ge $((10#$STOP)) ] && [ "$(now)" -lt $((10#$CONT)) ]; do sleep 5; done
  stopped=()
  if [ -e "$SKIP" ]; then
    log "skip file present: not pausing today"
  else
    for pf in "$@"; do
      [ -f "$pf" ] || continue
      p=$(cat "$pf")
      cmd=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null)
      case "$cmd" in
        *dl-custodian*|*darkstep*|*dl-owner*|"sh -c p=\$(cat "*) ;;
        *) [ -n "$cmd" ] && log "pid $p ($pf) is not this run's: left alone"; continue ;;
      esac
      kill -STOP "$p" && stopped+=("$p") && log "SIGSTOP $p ($pf)"
    done
  fi
  until [ "$(now)" -ge $((10#$CONT)) ]; do sleep 5; done
  for p in "${stopped[@]}"; do kill -CONT "$p" && log "SIGCONT $p"; done
  # past CONT: wait for the next day's window
  while [ "$(now)" -ge $((10#$STOP)) ]; do sleep 30; done
done
