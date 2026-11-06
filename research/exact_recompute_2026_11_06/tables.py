"""Public tables of gptoss-int v0, each entry from a fixed sequence of float64 operations, rounded
once to an integer, then pinned by digest. Recipes follow FlashProve docs/model.md section 4
(Apache-2.0) where gpt-oss has the same op; YaRN and the clamped SwiGLU are gpt-oss's own."""
import hashlib
import math

import numpy as np

CS = 14        # rotary scale exponent
RX = 8         # softmax key step: u counts 2^-RX units of logit
EXPS = 15      # softmax table scale
GK = 8         # gate key step exponent (gate quantized to 2^-GK for the table)
GLO, GHI = -16, 7  # gate table domain [GLO, GHI] (gate is clamped above at 7 by the model)
FT = 12        # gate table scale


def rha(v):
    return np.where(v >= 0, np.floor(v + 0.5), -np.floor(-v + 0.5)).astype(np.int64)


def yarn_inv_freq(theta=150000.0, dim=64, factor=32.0, orig=4096, beta_fast=32.0, beta_slow=1.0):
    """gpt-oss YaRN (truncate = false), in float64. Returns (inv_freq[dim/2], attention_factor)."""
    def corr_dim(rot):
        return (dim * math.log(orig / (rot * 2 * math.pi))) / (2 * math.log(theta))
    low, high = max(corr_dim(beta_fast), 0.0), min(corr_dim(beta_slow), dim - 1.0)
    i = np.arange(0, dim, 2, dtype=np.float64)
    pos = theta ** (i / dim)
    extra, inter = 1.0 / pos, 1.0 / (factor * pos)
    ramp = np.clip((np.arange(dim // 2, dtype=np.float64) - low) / (high - low), 0.0, 1.0)
    keep = 1.0 - ramp
    inv = inter * (1.0 - keep) + extra * keep
    att = 0.1 * math.log(factor) + 1.0
    return inv, att


def rope_tables(T, dim=64):
    inv, att = yarn_inv_freq(dim=dim)
    x = np.arange(T, dtype=np.float64)[:, None] * inv[None, :]
    return rha((2.0 ** CS) * att * np.cos(x)), rha((2.0 ** CS) * att * np.sin(x))


def exp_table():
    ex = []
    u = 0
    while True:
        v = int(np.rint((2.0 ** EXPS) * math.exp(-u / 2.0 ** RX)))
        if v == 0:
            break
        ex.append(v)
        u += 1
    return np.array(ex, dtype=np.int64)


def glu_table():
    keys = np.arange(GLO * 2 ** GK, GHI * 2 ** GK + 1, dtype=np.float64)
    g = keys / 2.0 ** GK
    return rha((2.0 ** FT) * g / (1.0 + np.exp(-1.702 * g)))


def digest(arr):
    return hashlib.sha256(np.ascontiguousarray(arr, dtype="<i8").tobytes()).hexdigest()
