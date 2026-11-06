"""gpt-oss-20b weights, read from the safetensors shards with no framework.

Every tensor is returned exactly as stored:
  * BF16 tensors as (significand, exponent) integer pairs or as float32 (bf16 -> f32 is exact);
  * MXFP4 expert tensors as int8 q in [-12, 12] (E2M1 value times 2) and int32 block exponents,
    so that the weight is exactly q * 2^(e - 128) (E8M0 scale 2^(s-127), times 1/2 for the x2).
The shards are checked against the registry's full-mode commitment before use.
"""
import hashlib
import json
import os
import struct

import numpy as np

ROOT = os.environ.get("GPTOSS_DIR", "/Users/ember/models/gpt-oss-20b/6cee5e81")
MANIFEST = os.path.join(os.path.dirname(__file__), "../../registry/manifests/openai__gpt-oss-20b.6cee5e81ee83.full.json")

# E2M1 code -> value * 2 (exact small integers). Low nibble is the even element (transformers mxfp4.py).
FP4_X2 = np.array([0, 1, 2, 3, 4, 6, 8, 12, 0, -1, -2, -3, -4, -6, -8, -12], dtype=np.int8)


class Shards:
    def __init__(self, root=ROOT):
        self.root = root
        idx = json.load(open(os.path.join(root, "model.safetensors.index.json")))
        self.where = idx["weight_map"]
        self.headers = {}
        self.maps = {}

    def _open(self, shard):
        if shard not in self.maps:
            path = os.path.join(self.root, shard)
            with open(path, "rb") as f:
                n = struct.unpack("<Q", f.read(8))[0]
                self.headers[shard] = (json.loads(f.read(n)), 8 + n)
            self.maps[shard] = np.memmap(path, dtype=np.uint8, mode="r")
        return self.headers[shard], self.maps[shard]

    def raw(self, name):
        shard = self.where[name]
        (hdr, base), mm = self._open(shard)
        t = hdr[name]
        b, e = t["data_offsets"]
        return t["dtype"], t["shape"], mm[base + b: base + e]

    def bf16_bits(self, name):
        dt, shape, buf = self.raw(name)
        assert dt == "BF16", (name, dt)
        return np.frombuffer(buf, dtype=np.uint16).reshape(shape)

    def f32(self, name):
        bits = self.bf16_bits(name).astype(np.uint32) << 16
        return bits.view(np.float32)

    def u8(self, name):
        dt, shape, buf = self.raw(name)
        assert dt == "U8", (name, dt)
        return np.frombuffer(buf, dtype=np.uint8).reshape(shape)

    def mxfp4(self, prefix, e=None):
        """(q, e) for an expert weight: q int8 [E, out, nblk, 32], e int32 [E, out, nblk]; w = q*2^(e-128).
        With e given, only that expert ([out, nblk, 32], [out, nblk])."""
        blocks = self.u8(prefix + "_blocks")  # [E, out, nblk, 16]
        scales = self.u8(prefix + "_scales")  # [E, out, nblk]
        if e is not None:
            blocks, scales = blocks[e], scales[e]
        q = np.empty(blocks.shape[:-1] + (32,), dtype=np.int8)
        q[..., 0::2] = FP4_X2[blocks & 0x0F]
        q[..., 1::2] = FP4_X2[blocks >> 4]
        return q, scales.astype(np.int32)


def bf16_to_int(bits):
    """bf16 bit patterns -> (m, e) with value = m * 2^e exactly, m a signed integer with |m| < 2^8.
    Zero gives (0, 0). Subnormals and non-finite values are refused."""
    bits = bits.astype(np.int32)
    sign = np.where(bits & 0x8000, -1, 1)
    ex = (bits >> 7) & 0xFF
    man = bits & 0x7F
    if np.any(ex == 0xFF):
        raise ValueError("non-finite bf16")
    if np.any((ex == 0) & (man != 0)):
        raise ValueError("subnormal bf16")
    m = np.where(ex == 0, 0, (man | 0x80)) * sign
    e = np.where(ex == 0, 0, ex - 127 - 7)
    return m.astype(np.int32), e.astype(np.int32)


def verify_shards(root=ROOT):
    core = json.load(open(MANIFEST))["core"]
    out = {}
    for s in core["shards"]:
        h = hashlib.sha256()
        with open(os.path.join(root, s["path"]), "rb") as f:
            for chunk in iter(lambda: f.read(1 << 24), b""):
                h.update(chunk)
        out[s["path"]] = h.hexdigest() == s["file_hash"]
    return out


if __name__ == "__main__":
    print(json.dumps(verify_shards(), indent=1))
