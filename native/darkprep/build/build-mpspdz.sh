#!/usr/bin/env bash
# Build MP-SPDZ v0.4.4 mascot-party.x from source with MASCOT's combining parameter tau = N_AMPLIFY (default 5), as one
# binary for every custodian box: dependencies built into $ROOT/local (no system packages), libraries static, arch
# x86-64-v3 + ADX/AES/PCLMUL (the common subset of dregg-forge, bb2, hbox), glibc the only dynamic dependency.
#   usage: build-mpspdz.sh ROOT [TAU]        e.g. build-mpspdz.sh ~/lanes/dl-gen6-prep 5
# Output: $ROOT/mp-spdz-0.4.4/static/{mascot,lowgear,highgear}-party.x and $ROOT/mpspdz-tau$TAU.tar.xz (binary, compile.py, Compiler/).
set -euo pipefail
ROOT=$(realpath "$1"); TAU=${2:-5}; J=${J:-16}
L=$ROOT/local; mkdir -p "$L" "$ROOT/dl"; cd "$ROOT/dl"
fetch() { [ -f "$(basename "$1")" ] || curl -fsSLO "$1"; }
fetch https://ftp.gnu.org/gnu/m4/m4-1.4.19.tar.xz
fetch https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz
fetch https://download.libsodium.org/libsodium/releases/libsodium-1.0.20.tar.gz
fetch https://zlib.net/fossils/zlib-1.3.1.tar.gz
fetch https://libntl.org/ntl-11.5.1.tar.gz
fetch https://github.com/facebook/zstd/releases/download/v1.5.6/zstd-1.5.6.tar.gz
fetch https://github.com/data61/MP-SPDZ/releases/download/v0.4.4/mp-spdz-0.4.4.tar.xz
sha256sum *.tar.* > "$ROOT/dl.sha256"
export PATH=$L/bin:$PATH CFLAGS="-O2 -fPIC" CXXFLAGS="-O2 -fPIC"
[ -x "$L/bin/m4" ] || { tar xf m4-1.4.19.tar.xz; (cd m4-1.4.19 && ./configure --prefix="$L" -q && make -j$J -s && make -s install); }
[ -f "$L/lib/libgmp.a" ] || { tar xf gmp-6.3.0.tar.xz; (cd gmp-6.3.0 && ./configure --prefix="$L" --enable-cxx --disable-shared --with-pic -q && make -j$J -s && make -s install); }
[ -f "$L/lib/libsodium.a" ] || { tar xf libsodium-1.0.20.tar.gz; (cd libsodium-stable 2>/dev/null || cd libsodium-1.0.20; ./configure --prefix="$L" --disable-shared --with-pic -q && make -j$J -s && make -s install); }
[ -f "$L/lib/libz.a" ] || { tar xf zlib-1.3.1.tar.gz; (cd zlib-1.3.1 && ./configure --prefix="$L" --static && make -j$J -s && make -s install); }
# the distribution's static libcrypto (OpenSSL 3) references zstd
[ -f "$L/lib/libzstd.a" ] || { tar xf zstd-1.5.6.tar.gz; (cd zstd-1.5.6/lib && make -j$J -s libzstd.a CFLAGS="-O2 -fPIC" && cp libzstd.a "$L/lib/" && cp zstd.h zstd_errors.h zdict.h "$L/include/"); }
[ -f "$L/lib/libntl.a" ] || { tar xf ntl-11.5.1.tar.gz; (cd ntl-11.5.1/src && ./configure PREFIX="$L" GMP_PREFIX="$L" NTL_GMP_LIP=on NTL_THREADS=on SHARED=off TUNE=x86 NATIVE=off CXXFLAGS="-O2 -fPIC" && make -j$J -s && make -s install); }
unset CFLAGS CXXFLAGS
export CMAKE_PREFIX_PATH=$L PKG_CONFIG_PATH=$L/lib/pkgconfig
cd "$ROOT"; [ -d mp-spdz-0.4.4 ] || tar xf dl/mp-spdz-0.4.4.tar.xz
cd mp-spdz-0.4.4
sed -i "s/^#define N_AMPLIFY .*/#define N_AMPLIFY $TAU/" OT/NPartyTripleGenerator.h
grep -q "^#define N_AMPLIFY $TAU$" OT/NPartyTripleGenerator.h
cat > CONFIG.mine <<CFG
ERROR =
USE_NTL = 1
ARCH = -march=x86-64-v3 -madx -maes -mpclmul
MY_CFLAGS = -I$L/include
MY_LDLIBS = -L$L/lib
MY_BOOST = -L$L/lib
CFG
[ -f local/lib/libboost_thread.a ] || make -j$J boost
# the bundled base-OT libraries' own builds find libsodium through the compiler's search paths, and SimplestOT_C's
# Makefile target tries a git submodule update first (the release is not a git checkout): configure it directly
export CPATH=$L/include LIBRARY_PATH=$L/lib
[ -f deps/SimplestOT_C/ref10/Makefile ] || (cd deps/SimplestOT_C/ref10 && cmake . -DOC_THIRDPARTY_HINT=$L -DCMAKE_PREFIX_PATH=$L)
# WAN links (hbox on Wi-Fi): MP-SPDZ's stock socket settings abort on any stall over ~16 s (keepalive idle 1 s,
# interval 3 s, 5 probes), on a blocked send or receive over 10 s (client sockets), and on a party waiting 300 s for a
# peer (player sockets; LowGear key setup over a slow link waits longer). Tolerate stalls of up to an hour instead.
sed -i "s/unsigned int timeout_milli = 10000;/unsigned int timeout_milli = 0; \/\/ darkprep: no send\/receive timeout/" Networking/sockets.cpp
sed -i "s/int keepalive_strobe_interval_secs = 3;/int keepalive_strobe_interval_secs = 30;/; s/int num_keepalive_strobes = 5;/int num_keepalive_strobes = 120;/; s/int keepalive_idle_time_secs = 1;/int keepalive_idle_time_secs = 30;/" Networking/sockets.cpp
sed -i "s/tv.tv_sec = 300;/tv.tv_sec = 3600; \/\/ darkprep: was 300/" Networking/Player.cpp
grep -q "timeout_milli = 0" Networking/sockets.cpp && grep -q "num_keepalive_strobes = 120" Networking/sockets.cpp && grep -q "tv.tv_sec = 3600" Networking/Player.cpp
grep -q -- "-lz -lzstd" Makefile || sed -i "s/\$(LDLIBS) -lz -Wl,-Bdynamic/\$(LDLIBS) -lz -lzstd -Wl,-Bdynamic/" Makefile
make -j$J static/mascot-party.x static/lowgear-party.x static/highgear-party.x
ldd static/mascot-party.x || true
tar cJf "$ROOT/mpspdz-tau$TAU.tar.xz" static/mascot-party.x static/lowgear-party.x static/highgear-party.x compile.py Compiler License.txt
sha256sum static/*-party.x "$ROOT/mpspdz-tau$TAU.tar.xz"
