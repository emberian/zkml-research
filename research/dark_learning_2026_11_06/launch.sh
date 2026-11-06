#!/usr/bin/env bash
# usage: launch.sh NAME MEM cmd...   -> detached under swarm-build, log NAME.log, pid NAME.pid
set -euo pipefail
cd "$(dirname "$0")"
name=$1; mem=$2; shift 2
SWARM_MEM_MAX=$mem nohup setsid swarm-build "$@" > "$name.log" 2>&1 < /dev/null &
echo $! > "$name.pid"
echo "$name $(cat "$name.pid")"
