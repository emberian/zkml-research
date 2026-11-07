"""The data owner's signature on each training batch (signed-input binding, from ePrint 2026/2721 §1.3 / §5.3:
"if all the MPC nodes misbehave, nothing is stopping them from choosing new inputs").

2026-11-06. Hash-based and post-quantum, in keeping with the program's PQ requirement: a Merkle tree of 2^h
Lamport one-time keys over SHA-256 (XMSS without WOTS+ chains, for clarity). Leaf index = step number, so each
(model, epoch, step) is signed once with its own one-time key. The owner refuses to sign a second batch for a step
it has already signed. That refusal is the owner's state, which a key-reuse falsifier would have to break.
Signature: leaf index u32 | 256 revealed preimages | 256 hashes of the unrevealed halves | h-node auth path,
(4 + 32 (512 + h)) bytes.
"""
import hashlib
import os
import secrets
import struct

def H(*xs):
    m = hashlib.sha256()
    for x in xs:
        m.update(x if isinstance(x, bytes) else repr(x).encode())
    return m.digest()

_DET_OWNERS = [0]

def _det_seed():
    """TEST ONLY (native bit-exact checks): with DL_DETERMINISTIC=<seed> set, the k-th Owner made without a seed in
    this process gets sha256("dl-proof|<seed>|owner|<k>"). Unset, None (the seed comes from `secrets`)."""
    seed = os.environ.get("DL_DETERMINISTIC")
    if seed is None:
        return None
    k = _DET_OWNERS[0]
    _DET_OWNERS[0] += 1
    return hashlib.sha256(f"dl-proof|{seed}|owner|{k}".encode()).digest()

class Owner:
    """state_path: the owner's durable record of the next unused leaf. One-time keys are used in strictly
    increasing leaf order, independent of step numbers. A restart reads the counter, so it never reuses a key;
    without a state file the counter lives in memory only (tests)."""
    def __init__(self, h=12, seed=None, state_path=None):
        self.state_path = state_path
        self.h = h
        self.seed = seed or _det_seed() or secrets.token_bytes(32)
        self.leaves = [self._pkhash(i) for i in range(1 << h)]
        self.tree = [self.leaves]
        lvl = self.leaves
        while len(lvl) > 1:
            lvl = [H(lvl[i], lvl[i + 1]) for i in range(0, len(lvl), 2)]
            self.tree.append(lvl)
        self.pk = self.tree[-1][0]
        self.next_leaf = 0
        if state_path and os.path.exists(state_path):
            self.next_leaf = int(open(state_path).read().strip())

    def _sk(self, i):
        return [[H(self.seed, i, b, j) for j in range(256)] for b in (0, 1)]

    def _pkhash(self, i):
        sk = self._sk(i)
        return H(*[H(x) for b in (0, 1) for x in sk[b]])

    def sign(self, msg):
        leaf = self.next_leaf
        if leaf >= 1 << self.h:
            raise ValueError("owner key tree exhausted: rotate the owner key (a ledger event)")
        self.next_leaf = leaf + 1
        if self.state_path:                  # persist BEFORE releasing the signature
            tmp = self.state_path + ".tmp"
            with open(tmp, "w") as f:
                f.write(str(self.next_leaf)); f.flush(); os.fsync(f.fileno())
            os.replace(tmp, self.state_path)
        dig = H(msg)
        bits = [(dig[j // 8] >> (7 - j % 8)) & 1 for j in range(256)]
        sk = self._sk(leaf)
        rev = [sk[b][j] for j, b in enumerate(bits)]
        oth = [H(sk[1 - b][j]) for j, b in enumerate(bits)]
        path, k = [], leaf
        for lvl in self.tree[:-1]:
            path.append(lvl[k ^ 1])
            k //= 2
        return struct.pack(">I", leaf) + b"".join(rev) + b"".join(oth) + b"".join(path)

def sig_len(h):
    return 4 + 32 * (512 + h)

def sig_leaf(sig):
    return struct.unpack(">I", sig[:4])[0]

def verify(pk, h, min_leaf, msg, sig):
    """Valid iff the signature verifies under pk and its leaf is >= min_leaf (the ledger passes one more than
    the last leaf it accepted, so a one-time key is never accepted twice)."""
    if len(sig) != sig_len(h):
        return False
    leaf = sig_leaf(sig)
    if leaf < min_leaf or leaf >= 1 << h:
        return False
    rev = [sig[4 + 32 * j:36 + 32 * j] for j in range(256)]
    oth = [sig[4 + 32 * (256 + j):36 + 32 * (256 + j)] for j in range(256)]
    path = [sig[4 + 32 * (512 + j):36 + 32 * (512 + j)] for j in range(h)]
    dig = H(msg)
    bits = [(dig[j // 8] >> (7 - j % 8)) & 1 for j in range(256)]
    halves = [[None] * 256, [None] * 256]
    for j, b in enumerate(bits):
        halves[b][j] = H(rev[j])
        halves[1 - b][j] = oth[j]
    node = H(*[x for b in (0, 1) for x in halves[b]])
    k = leaf
    for sib in path:
        node = H(node, sib) if k % 2 == 0 else H(sib, node)
        k //= 2
    return node == pk

def batch_message(ctx, roots_x, roots_y):
    """What the owner signs: the binding context and the share-tuple roots of its x and y commitments."""
    return H("dark-learning batch", tuple(ctx), tuple(roots_x), tuple(roots_y))
