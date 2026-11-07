"""The data owner of the gen 6 run (train lane): MNIST, checked; the encoder; the seeded init and order; the step
input feed. The reference for native/darktrain (which must equal it: tests/vs_python.rs).

A genesis is darktrain's Cfg JSON: the step program (s1a = s1b = S1, k1, s2, k2, s3, k3, rnd3 -> R3 = 2^(S3-1)),
the init (seed_init, a1, a2, hid, and the layout tile/bias -> nin, reps -> nout = 10 reps), and the encoder (xenc,
tile, bias, reps, ypos, yneg, rnd2). The order seed is the owner's own (seed_order).

    python3 -I train_owner.py feed GENESIS.json DATA_DIR START COUNT     # one JSON line per step: t, k, x, y
    python3 -I train_owner.py digest GENESIS.json DATA_DIR STEPS         # run step_spec STEPS steps, print digests
"""
import hashlib
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import step_spec as S

MNIST = {
    "train-images-idx3-ubyte": "ba891046e6505d7aadcbbe25680a0738ad16aec93bde7f9b65e87a2fc25776db",
    "train-labels-idx1-ubyte": "65a50cbbf4e906d70832878ad85ccda5333a97f0f4c3dd2ef09a8a9eef7101c5",
    "t10k-images-idx3-ubyte": "0fa7898d509279e482958e8ce81c8e77db3f2f8254e26661ceb7762c4d494ce7",
    "t10k-labels-idx1-ubyte": "ff7bcfd416de33731a308c3f266cc351222c34898ecbeaf847f06e48f7ec33f2",
}


def _read(d, name):
    b = open(os.path.join(d, name), "rb").read()
    h = hashlib.sha256(b).hexdigest()
    if h != MNIST[name]:
        raise ValueError(f"{name}: sha256 {h} != pinned {MNIST[name]}")
    return b


def load(d):
    """{'train': (images bytes, labels bytes, n), 'test': ...}; IDX headers checked."""
    out = {}
    for sp, pre in (("train", "train"), ("test", "t10k")):
        im, lb = _read(d, f"{pre}-images-idx3-ubyte"), _read(d, f"{pre}-labels-idx1-ubyte")
        be = lambda b, o: int.from_bytes(b[o:o + 4], "big")
        n = be(im, 4)
        assert be(im, 0) == 0x803 and be(lb, 0) == 0x801 and be(lb, 4) == n and be(im, 8) == be(im, 12) == 28
        assert len(im) == 16 + 784 * n and len(lb) == 8 + n and max(lb[8:]) <= 9
        out[sp] = (im[16:], lb[8:], n)
    return out


def means(m):
    im, _, n = m["train"]
    return [(sum(im[t * 784 + k] for t in range(n)) + n // 2) // n for k in range(784)]


def program(g):
    assert g["s1a"] == g["s1b"], "the pinned program has one S1"
    return S.Program(S1=g["s1a"], K1=g["k1"], S2=g["s2"], K2=g["k2"], S3=g["s3"], K3=g["k3"],
                     R3=(1 << (g["s3"] - 1)) if g["rnd3"] else 0, T_LO=g.get("t_lo", -128), WMAX=None)


def nin(g):
    return g["tile"] * 784 + int(g["bias"])


def init(g):
    return S.Init(g["seed_init"], g["a1"], g["a2"], nin(g), g["hid"], 10 * g["reps"])


def encode(g, mu, img, label):
    d = g["d"]
    x = [0] * d
    for t in range(g["tile"]):
        for k, p in enumerate(img):
            if g["xenc"] == "pos":
                v = (7 * p + 127) // 255
            elif g["xenc"] == "ctr":
                v = (14 * p + 127) // 255 - 7
            else:
                mm = 7 if g["xenc"] == "mc" else 14
                v = max(-7, min(7, (2 * mm * (p - mu[k]) + 255) // 510))
            x[t * 784 + k] = v
    if g["bias"]:
        x[g["tile"] * 784] = 7
    off = (1 << (g["s2"] - 1)) if g["rnd2"] else 0
    y = [0] * d
    for i in range(10 * g["reps"]):
        y[i] = (g["ypos"] if i % 10 == label else g["yneg"]) - off
    return x, y


def order(seed, n):
    v = list(range(n))
    random.Random(seed).shuffle(v)
    return v


def feed(g, m, start, count):
    """The owner's step inputs: step t trains on training example order[t % n]."""
    im, lb, n = m["train"]
    mu = means(m) if g["xenc"] in ("mc", "mc2") else None
    o = order(g["seed_order"], n)
    for t in range(start, start + count):
        k = o[t % n]
        x, y = encode(g, mu, im[k * 784:(k + 1) * 784], lb[k])
        yield t, k, x, y


def digest(g, m, steps):
    W1, W2 = init(g).weights(g["d"])
    P = program(g)
    H = lambda o: hashlib.sha256(repr(o).encode()).hexdigest()
    out = dict(init=H((W1, W2)))
    for t, k, x, y in feed(g, m, 0, steps):
        W1, W2, _ = S.step(W1, W2, x, y, P)
    out["after"] = H((W1, W2))
    import train_eval as TE
    im, lb, _ = m["test"]
    mu = means(m) if g["xenc"] in ("mc", "mc2") else None
    ex = [(encode(g, mu, im[t * 784:(t + 1) * 784], lb[t])[0], lb[t]) for t in range(g.get("n_check_eval", 20))]
    out["release"] = TE.release(P, W1, W2, ex, g["reps"])
    out["per_example"] = [TE.correct_one(P, W1, W2, x, l, g["reps"]) for x, l in ex]   # test only: never released
    return out


DEFAULTS = dict(d=4096, hid=4096, reps=1, s1a=11, s1b=11, s2=4, s3=14, k1=19, k2=8, k3=19, t_lo=-128, rnd3=False,
                rnd2=False, ypos=32, yneg=0, xenc="pos", tile=1, bias=False, a1=64, a2=0, seed_init=1, seed_order=2)

if __name__ == "__main__":
    cmd, gpath, ddir = sys.argv[1:4]
    g = dict(DEFAULTS, **json.load(open(gpath)))
    m = load(ddir)
    if cmd == "feed":
        for t, k, x, y in feed(g, m, int(sys.argv[4]), int(sys.argv[5])):
            print(json.dumps(dict(t=t, k=k, x=x, y=y)))
    elif cmd == "digest":
        print(json.dumps(digest(g, m, int(sys.argv[4]))))
