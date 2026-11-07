#!/usr/bin/env bash
# Keep one MP-SPDZ runtime's secrets in RAM: RT/Player-Data and RT/Persistence become symlinks into RAM/ (a tmpfs
# with no swap behind it), so MAC key shares (Mascot-Secrets-*, 3-p-*/Player-MAC-Keys-*), LowGear-/HighGear-Secrets,
# the memory dump (Memory-*) and the Transactions file (plain authenticated shares before sealing) never reach
# persistent storage, and the retire/wipe paths in darkprep erase the only copy.
#   ramdir.sh RT RAM          move (first use) or rebuild (after a reboot emptied RAM) the runtime; idempotent
#   ramdir.sh RT RAM status   print where each directory lives and whether a 61-bit MAC key share is in RAM
# The non-secret files (TLS certificates and their c_rehash links, this party's TLS key, PairwiseParams-*) are kept on
# disk in RT/Player-Data.skel and copied into RAM on a rebuild. A rebuild has no MAC key: the next chunk is refused
# by darkprep's chunk guard until it runs with --new-mac-key (a re-key; under LowGear that is a new key setup).
# RAM must be a tmpfs on a box without swap, or a tmpfs mounted noswap (hbox). The script checks this and refuses.
set -euo pipefail
RT=$(cd "$1" && pwd); RAM=$2; MODE=${3:-apply}
skel_file() { case "$1" in *.pem|*.0|*.key|PairwiseParams-*) return 0;; *) return 1;; esac; }
check_ram() {
  local fs opts; mkdir -p "$RAM"; chmod 700 "$RAM"
  fs=$(findmnt -n -o FSTYPE --target "$RAM"); opts=$(findmnt -n -o OPTIONS --target "$RAM")
  [ "$fs" = tmpfs ] || { echo "ramdir: $RAM is on $fs, not tmpfs" >&2; exit 2; }
  if [ "$(awk 'NR>1' /proc/swaps | wc -l)" != 0 ] && [[ ",$opts," != *,noswap,* ]]; then
    echo "ramdir: this box has swap and $RAM is not a noswap tmpfs" >&2; exit 2
  fi
}
if [ "$MODE" = status ]; then
  for d in Player-Data Persistence; do echo "$d -> $(readlink "$RT/$d" || echo "DISK (not a symlink)")"; done
  ls "$RT/Player-Data/" 2>/dev/null | grep -E '^(Mascot-Secrets-p-61-|LowGear-Secrets-|HighGear-Secrets-)' | sed 's/^/  key: /' || echo "  no 61-bit MAC key share"
  findmnt -n -o TARGET,FSTYPE,OPTIONS --target "$RAM"; exit 0
fi
check_ram
for d in Player-Data Persistence; do
  if [ -L "$RT/$d" ]; then
    if [ ! -d "$RAM/$d" ]; then   # RAM was emptied (reboot): rebuild from the skeleton, without any key
      mkdir -m 700 "$RAM/$d"
      [ "$d" = Player-Data ] && cp -a "$RT/Player-Data.skel/." "$RAM/$d/"
      ln -sfn "$RAM/$d" "$RT/$d"
      echo "ramdir: rebuilt $RAM/$d (no MAC key: the next chunk needs --new-mac-key)"
    fi
    continue
  fi
  [ -e "$RAM/$d" ] && { echo "ramdir: $RAM/$d exists but $RT/$d is not a symlink; refusing" >&2; exit 3; }
  mkdir -p "$RT/$d"
  cp -a "$RT/$d" "$RAM/$d"
  if [ "$d" = Player-Data ]; then
    rm -rf "$RT/Player-Data.skel.new"; mkdir "$RT/Player-Data.skel.new"
    for f in "$RT/$d"/*; do b=$(basename "$f"); skel_file "$b" && cp -a "$f" "$RT/Player-Data.skel.new/"; done
    rm -rf "$RT/Player-Data.skel"; mv "$RT/Player-Data.skel.new" "$RT/Player-Data.skel"
  fi
  mv "$RT/$d" "$RT/$d.disk-old"
  ln -s "$RAM/$d" "$RT/$d"
  # the disk copy: every regular file that is not a skeleton file is overwritten with zeros and unlinked
  find "$RT/$d.disk-old" -type f -print0 | while IFS= read -r -d '' f; do
    if [ "$d" = Player-Data ] && skel_file "$(basename "$f")"; then rm -f "$f"; else shred -n 0 -z -u "$f"; fi
  done
  rm -rf "$RT/$d.disk-old"
  echo "ramdir: $RT/$d -> $RAM/$d"
done
