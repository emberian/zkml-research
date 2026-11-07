"""Preprocessing from TAPES instead of the ideal dealer: reads the per-party tapes that native/darkprep writes
(MASCOT over MP-SPDZ, three custodian processes) and serves them to spdz.Engine in program order.

2026-11-06 (dark-learning gen 5, lane "prep"). spdz.py is unchanged. TapeDealer has the Dealer interface that
spdz.Engine and the HE helpers use (p, n, alpha_sh, rng, auth, streams, count, commitments). auth(v, tag) IGNORES
v (the ideal value the engine drew from dealer.rng) and returns the next tape entry of every party, refusing a
tag that differs from the one the engine asks for. TapeEngine overrides Engine.input only: the data owner's mask
r comes from the owner's file (it learned r from the custodians' input-tuple shares after checking a b = c),
not from the owner's own rng.

Tape format (little-endian; native/darkprep/src/lib.rs is the authority):
  b"DLTAPE1\\n", u64 p, u32 n_parties, u32 party, u64 alpha_i, u32 d, u8 inputs_mode, 4 x (u8 s, u8 K),
  u64 n, then n x (u8 tag, u64 share, u64 mac_share);  tags 0..8 = in ta tb tc tr trb trh lp ar.
Owner file: b"DLOWNR1\\n", u64 p, u64 n, n x u64 r.
"""
import random
import struct

import spdz

TAGS = ["in", "ta", "tb", "tc", "tr", "trb", "trh", "lp", "ar"]

def read_tape(path):
    b = open(path, "rb").read()
    if b[:8] != b"DLTAPE1\n":
        raise ValueError(f"{path}: not a DLTAPE1 tape")
    p, n_parties, party, alpha_i, d, mode = struct.unpack_from("<QIIQIB", b, 8)
    trunc = [tuple(b[37 + 2 * t: 39 + 2 * t]) for t in range(4)]
    (n,) = struct.unpack_from("<Q", b, 45)
    if len(b) != 53 + 17 * n:
        raise ValueError(f"{path}: length does not match {n} entries")
    entries = [(TAGS[t], s, m) for t, s, m in struct.iter_unpack("<BQQ", b[53:])]
    return dict(p=p, n_parties=n_parties, party=party, alpha_i=alpha_i, d=d, mode=mode, trunc=trunc, entries=entries)

def read_owner(path):
    b = open(path, "rb").read()
    if b[:8] != b"DLOWNR1\n":
        raise ValueError(f"{path}: not a DLOWNR1 file")
    p, n = struct.unpack_from("<QQ", b, 8)
    return p, list(struct.unpack_from(f"<{n}Q", b, 24))

class TapeDealer:
    def __init__(self, tape_dir, n=3):
        tapes = [read_tape(f"{tape_dir}/tape-P{i}.bin") for i in range(n)]
        if sorted(t["party"] for t in tapes) != list(range(n)) or len({t["p"] for t in tapes}) != 1:
            raise ValueError("tapes are not one consistent set")
        self.p, self.n = tapes[0]["p"], n
        self.meta = {k: tapes[0][k] for k in ("d", "mode", "trunc")}
        self.alpha_sh = [t["alpha_i"] for t in tapes]       # party i holds alpha_sh[i] only
        # TEST-ONLY global view (no party knows alpha): used by he_outer's full-collusion falsifier alone.
        self.alpha = sum(self.alpha_sh) % self.p
        self.tapes = [t["entries"] for t in tapes]
        op, self.owner = read_owner(f"{tape_dir}/owner.bin")
        if op != self.p:
            raise ValueError("owner file is for another prime")
        self.pos = self.owner_pos = 0
        self.streams = [[] for _ in range(n)]
        self.count = 0
        # spdz.Engine draws the ideal values from dealer.rng before calling auth; the tapes ignore them.
        self.rng = random.Random("tape-dealer: values drawn here are discarded")

    def auth(self, v, tag):
        k = self.pos
        if k >= len(self.tapes[0]):
            raise spdz.Abort(f"tape exhausted at entry {k} (the step asks for {tag})")
        out = []
        for i in range(self.n):
            t, s, m = self.tapes[i][k]
            if t != tag:
                raise spdz.Abort(f"tape: party {i} entry {k} is {t!r}, the step asks for {tag!r}")
            out.append((s, m))
            self.streams[i].append((tag, (s, m)))
        self.pos += 1
        self.count += 1
        return out

    def owner_mask(self):
        r = self.owner[self.owner_pos]
        self.owner_pos += 1
        return r

    def exhausted(self):
        return self.pos == len(self.tapes[0]) and self.owner_pos == len(self.owner)

    def commitments(self):
        return [spdz.h(s) for s in self.streams]

class TapeEngine(spdz.Engine):
    def input(self, values, owner_rng, phase="input"):
        if self.audit:
            return super().input(values, owner_rng, phase)
        out = []
        for v in values:
            r = self.prep("in", lambda: 0)
            rv = self.dealer.owner_mask()
            c = (v - rv) % self.p
            self.transcript.append((phase, {}, c))
            self.count(phase, self.n)
            out.append(self.cadd(c, r))
        return out
