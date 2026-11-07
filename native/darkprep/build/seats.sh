#!/usr/bin/env bash
# From the Mac: make a set of TEST seat runtime dirs on forge and bb2, each with its own TLS key generated on its box
# and the three certificates pinned in each (c_rehash). MAC keys are NOT copied: each dir draws its own on first run.
#   seats.sh new   wired-new<I>: new committee, seat 0 bb2, 1 forge, 2 bb2; ips-wired-new.txt, ports 15700 + I
#   seats.sh sh    wired<I>-sh:  per-seat copies of wired<I> (same box, a fresh TLS identity and MAC key of its own);
#                  ips-wired-sh.txt, ports 15800 + I
#   seats.sh newsh wired-new<I>-sh: the same for the wired-new committee; ips-wired-new-sh.txt, ports 15900 + I
#   seats.sh newsh2 wired-new<I>-sh2: the same again from wired-new<I>-sh; ips-wired-new-sh2.txt, ports 16000 + I
#   seats.sh rehold|rehnew  reh-old<I> / reh-new<I>: the orchestrator rehearsal's two committees on the wired seats
#                  (copies of wired<I>'s binaries; fresh TLS identities); ips-reh-old.txt / ips-reh-new.txt, ports 16100 / 16200 + I
#   seats.sh fresh NAME PORT  NAME<I>: any new seat set on the wired boxes (fresh TLS keys, no MAC key, RAM secrets)
set -euo pipefail
FR=/srv/lanes/dl-gen6-prep; BR=/home/build/lanes/dl-gen6-prep
FIP=178.105.4.114; BIP=2.31.77.40
case $1 in
  new) H=(bb2 dregg-forge bb2); R=($BR $FR $BR); D=(wired-new0 wired-new1 wired-new2); IP=($BIP $FIP $BIP); PORT=15700; IPF=ips-wired-new.txt;;
  sh)  H=(dregg-forge bb2 bb2); R=($FR $BR $BR); D=(wired0-sh wired1-sh wired2-sh); SRC=(wired0 wired1 wired2); IP=($FIP $BIP $BIP); PORT=15800; IPF=ips-wired-sh.txt;;
  newsh) H=(bb2 dregg-forge bb2); R=($BR $FR $BR); D=(wired-new0-sh wired-new1-sh wired-new2-sh); SRC=(wired-new0 wired-new1 wired-new2); IP=($BIP $FIP $BIP); PORT=15900; IPF=ips-wired-new-sh.txt;;
  newsh2) H=(bb2 dregg-forge bb2); R=($BR $FR $BR); D=(wired-new0-sh2 wired-new1-sh2 wired-new2-sh2); SRC=(wired-new0-sh wired-new1-sh wired-new2-sh); IP=($BIP $FIP $BIP); PORT=16000; IPF=ips-wired-new-sh2.txt;;
  rehold) H=(dregg-forge bb2 bb2); R=($FR $BR $BR); D=(reh-old0 reh-old1 reh-old2); SRC=(wired0 wired1 wired2); IP=($FIP $BIP $BIP); PORT=16100; IPF=ips-reh-old.txt;;
  rehnew) H=(dregg-forge bb2 bb2); R=($FR $BR $BR); D=(reh-new0 reh-new1 reh-new2); SRC=(wired0 wired1 wired2); IP=($FIP $BIP $BIP); PORT=16200; IPF=ips-reh-new.txt;;
  fresh)  # seats.sh fresh NAME PORT: a fresh seat set NAME<I> on the wired boxes (0 forge, 1 bb2, 2 bb2), binaries
          # from each box's custodian runtime mpspdz/ (the EINTR-fixed build), new TLS keys and no MAC key; ips-NAME.txt, ports PORT + I; launch3.sh LAYOUT=dir:NAME
    N=${2:?seats.sh fresh NAME PORT}; H=(dregg-forge bb2 bb2); R=($FR $BR $BR); D=(${N}0 ${N}1 ${N}2); SRC=(. . .)
    IP=($FIP $BIP $BIP); PORT=${3:?seats.sh fresh NAME PORT}; IPF=ips-$N.txt;;
  fresh3)  # seats.sh fresh3 NAME PORT: a fresh seat set NAME<I> on the three custodian boxes (0 forge, 1 bb2, 2 hbox,
           # which only dials out), binaries from each box's mpspdz/; ips-NAME.txt, ports PORT + I; LAYOUT=dir3:NAME
    N=${2:?seats.sh fresh3 NAME PORT}; H=(dregg-forge bb2 hbox); R=($FR $BR /othersys/lanes/dl-gen6-prep); D=(${N}0 ${N}1 ${N}2)
    SRC=(. . .); IP=($FIP $BIP 127.0.0.1); PORT=${3:?seats.sh fresh3 NAME PORT}; IPF=ips-$N.txt;;
  *) echo "usage: seats.sh new|sh|newsh|newsh2|rehold|rehnew | fresh NAME PORT | fresh3 NAME PORT"; exit 2;;
esac
S=$(mktemp -d)
for i in 0 1 2; do
  r=${R[$i]}; d=$r/${D[$i]}
  if [ "$1" = new ]; then  # fresh TLS keys made on the box
    ssh ${H[$i]} "cd $r && bash native/darkprep/build/setup-box.sh $d $i $r/mpspdz-tau5.tar.xz"
  else
    # copy the binaries and compiler; leave every MAC key / secrets file AND the TLS identity behind: each seat set
    # gets a fresh TLS key made on its box, so after a rotation an old seat's key is pinned by no new seat
    ssh ${H[$i]} "set -e; src=$r/${SRC[$i]}/mpspdz; dst=$d/mpspdz; mkdir -p \$dst/Player-Data \$dst/Persistence; cp -a \$src/*-party.x \$src/compile.py \$src/Compiler \$src/Programs \$dst/; rm -f \$dst/Programs/Bytecode/* \$dst/Programs/Schedules/* 2>/dev/null; cd \$dst; (umask 077; openssl req -x509 -newkey rsa:3072 -nodes -keyout Player-Data/P$i.key -out Player-Data/P$i.pem -days 30 -subj /CN=P$i 2>/dev/null); ls Player-Data"
  fi
  scp -q ${H[$i]}:$d/mpspdz/Player-Data/P$i.pem $S/P$i.pem
done
printf "%s:%d\n%s:%d\n%s:%d\n" ${IP[0]} $PORT ${IP[1]} $((PORT+1)) ${IP[2]} $((PORT+2)) > $S/$IPF
for i in 0 1 2; do
  r=${R[$i]}; d=$r/${D[$i]}
  for j in 0 1 2; do [ $j = $i ] || scp -q $S/P$j.pem ${H[$i]}:$d/mpspdz/Player-Data/P$j.pem; done
  scp -q $S/$IPF ${H[$i]}:$r/$IPF
  ssh ${H[$i]} "c_rehash $d/mpspdz/Player-Data > /dev/null && ls $d/mpspdz/Player-Data | tr '\n' ' '; echo"
  # MP-SPDZ secrets (MAC keys, Transactions) live in RAM from the first run (ramdir.sh; RAM base per box)
  ssh ${H[$i]} "cd $r && native/darkprep/build/ramdir.sh $d/mpspdz \$( [ -d /othersys/lanes ] && echo $r/ram/${D[$i]} || echo /dev/shm/dl-gen6-prep/${D[$i]} ) | tail -1"
done
for i in 0 1 2; do openssl x509 -in $S/P$i.pem -noout -fingerprint -sha256; done
rm -rf $S
