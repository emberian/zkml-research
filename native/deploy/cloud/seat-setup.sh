#!/usr/bin/env bash
# A rented VM made into a custodian seat like hbox's, run as root on the box:
#   seat-setup.sh base     swap off for good (checked), packages (keyutils for the keyring checks), rust at forge's
#                          version; checks: no swap, the kernel keyring takes a key and invalidates it, /dev/shm tmpfs
#   seat-setup.sh rust WS.tgz      the run's custodian build from a git archive of native/ (r13: darkdeploy, darkstep,
#                                  dl-hand; t13: the test-harness build) under R/ws-target-{r13,t13}, as build13.sh
#   seat-setup.sh mpspdz HEAD.tgz  prep's build-mpspdz.sh (same script, same source tarballs, checked against bb2's
#                                  dl.sha256) into P/, and P/mpspdz-tau5.tar.xz
# Jobs run under nice -n 15 with logs and PID files in R/setup/. R=/srv/lanes/dl-gen6-deploy, P=/srv/lanes/dl-gen6-prep.
set -euo pipefail
R=/srv/lanes/dl-gen6-deploy; P=/srv/lanes/dl-gen6-prep; J=${J:-18}
mkdir -p $R/setup $P
case "$1" in
base)
  swapoff -a
  sed -i -E '/^[^#].*\sswap\s/s/^/#dl-cloud: /' /etc/fstab
  systemctl mask --now swap.target >/dev/null 2>&1 || true
  [ "$(awk 'NR>1' /proc/swaps | wc -l)" = 0 ] || { echo "swap still on" >&2; exit 2; }
  ls /sys/block | grep -q '^zram' && { echo "zram device present" >&2; exit 2; } || true
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -qq
  apt-get install -y -qq build-essential cmake python3 libssl-dev curl git keyutils pkg-config xz-utils ca-certificates \
      autoconf automake libtool rsync iproute2 procps >/dev/null
  [ -x /root/.cargo/bin/cargo ] || curl -sSf https://sh.rustup.rs | sh -s -- -y -q --profile minimal --default-toolchain 1.99.1
  id=$(keyctl add user dl-cloud-probe x @u); keyctl invalidate "$id"; sleep 1
  keyctl list @u | grep -q dl-cloud-probe && { echo "keyring: invalidated key still listed" >&2; exit 2; } || true
  findmnt -n -o FSTYPE /dev/shm | grep -qx tmpfs
  echo "BASE-OK swap $(awk 'NR>1' /proc/swaps | wc -l) keyring ok shm $(findmnt -n -o SIZE /dev/shm)"
  ;;
rust)
  rm -rf $R/ws && mkdir -p $R/ws && tar xzf "$2" -C $R/ws --strip-components=1
  cd $R/ws
  cat > $R/setup/build13.sh <<'B'
set -e
. /root/.cargo/env
cd /srv/lanes/dl-gen6-deploy/ws
D=/srv/lanes/dl-gen6-deploy
CARGO_TARGET_DIR=$D/ws-target-r13 cargo build -j 18 --release -p darkdeploy -p darkstep --bins
CARGO_TARGET_DIR=$D/ws-target-r13 cargo build -j 18 --release -p darkhand --bin dl-hand
CARGO_TARGET_DIR=$D/ws-target-t13 cargo build -j 18 --release -p darkdeploy --features test-harness --bins
CARGO_TARGET_DIR=$D/ws-target-t13 cargo build -j 18 --release -p darkstep --features test-harness --bins
echo BUILD13-DONE
B
  nohup nice -n 15 bash $R/setup/build13.sh > $R/setup/build13.log 2>&1 < /dev/null & echo $! > $R/setup/build13.pid
  cat $R/setup/build13.pid
  ;;
mpspdz)
  rm -rf $P/native && mkdir -p $P/native && tar xzf "$2" -C $P/native --strip-components=1
  nohup nice -n 15 env J=$J bash $P/native/darkprep/build/build-mpspdz.sh $P 5 > $R/setup/mpspdz.log 2>&1 < /dev/null & echo $! > $R/setup/mpspdz.pid
  cat $R/setup/mpspdz.pid
  ;;
*) echo "usage: seat-setup.sh base|rust WS.tgz|mpspdz HEAD.tgz" >&2; exit 2;;
esac
