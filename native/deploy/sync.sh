#!/bin/sh
# sync.sh HOST DEST [REV]: copy the native workspace at commit REV (default HEAD) to HOST:DEST, from `git archive`,
# never from the working tree: other lanes' uncommitted edits share that tree, and a box's binary must be one commit.
# Prints the commit it copied.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
host=$1 dest=$2 rev=${3:-HEAD}
top=$(git -C "$here" rev-parse --show-toplevel)
sha=$(git -C "$top" rev-parse --short "$rev")
tmp=$(mktemp -d "${TMPDIR:-/tmp}/dl-sync.XXXXXX")
git -C "$top" archive "$sha" native | tar -x -C "$tmp"
rsync -a --delete --checksum --exclude 'target*' "$tmp/native/" "$host:$dest/"
rm -rf "$tmp"
echo "$sha"
