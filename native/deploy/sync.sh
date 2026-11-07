#!/bin/sh
# sync.sh HOST DEST: copy the native workspace (sources and Cargo.lock, no target dirs) to HOST:DEST.
# The boxes have no git credentials; this is how a run's sources reach them. Prints the commit it copied.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
host=$1 dest=$2
rsync -a --delete --exclude 'target*' --exclude '.git' "$here/" "$host:$dest/"
git -C "$here" rev-parse --short HEAD
