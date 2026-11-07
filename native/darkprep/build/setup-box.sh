#!/usr/bin/env bash
# One custodian box's MASCOT runtime: setup-box.sh ROOT PARTY TARBALL
#   ROOT/mpspdz/{mascot,lowgear,highgear}-party.x, compile.py, Compiler/, Programs/Source/, Persistence/
#   ROOT/mpspdz/Player-Data/P<PARTY>.key  generated HERE, never leaves this box (mode 600)
#   ROOT/mpspdz/Player-Data/P<PARTY>.pem  this custodian's self-signed certificate, CN=P<PARTY>, to be pinned by
#                                         the other two (copy the .pem files only, then `c_rehash Player-Data`)
set -euo pipefail
ROOT=$(realpath "$1"); PARTY=$2; TB=$(realpath "$3")
M=$ROOT/mpspdz; mkdir -p "$M"; cd "$M"
tar xf "$TB"
mv -f static/*-party.x . && rmdir static
mkdir -p Player-Data Programs/Source Persistence
if [ ! -f Player-Data/P$PARTY.key ]; then
  (umask 077; openssl req -x509 -newkey rsa:3072 -nodes -keyout Player-Data/P$PARTY.key -out Player-Data/P$PARTY.pem \
      -days 60 -subj "/CN=P$PARTY" 2>/dev/null)
fi
openssl x509 -in Player-Data/P$PARTY.pem -noout -fingerprint -sha256
