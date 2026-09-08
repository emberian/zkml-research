"""[DERIVED] Finite integer Gaussian sampler; see DESIGN.md for the law.

Pure Python, integer arithmetic only, OS random bytes. Coefficients are returned
in memory and are never persisted. This is variable-time research code.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import os
import time

PRECISION = 320
BITS = 256
PREFIX_BITS = 32
SUFFIX_BITS = BITS - PREFIX_BITS
Q = 1 << PRECISION
COIN_RANGE = 1 << BITS
CAP = 4096
GRID = 512
CELLS = 8 * GRID
BLOCK_PROPOSALS = 8192


def _ceildiv(n: int, d: int) -> int:
    return -(-n // d)


@lru_cache(maxsize=1)
def pi_interval() -> tuple[int, int]:
    """Outward 320-bit Machin interval, exactly as finite_sampler/SPEC.md."""
    intervals = []
    for c in (5, 239):
        s = sum((Fraction((-1) ** j, (2 * j + 1) * c ** (2 * j + 1))
                 for j in range(80)), Fraction())
        intervals.append((s, s + Fraction(1, 161 * c ** 161)))
    lo = 16 * intervals[0][0] - 4 * intervals[1][1]
    hi = 16 * intervals[0][1] - 4 * intervals[1][0]
    lower = lo.numerator * Q // lo.denominator
    upper = _ceildiv(hi.numerator * Q, hi.denominator)
    assert upper - lower <= 3
    return lower, upper


def rho_interval(k: int, sigma: int) -> tuple[int, int]:
    """Return integer endpoints enclosing Q*exp(-pi*k*k/sigma**2).

    Public deterministic arithmetic. The endpoint |k|=8*sigma is also valid
    for table construction because pi/4<1.
    """
    if not isinstance(sigma, int) or sigma < 1 or sigma & (sigma - 1):
        raise ValueError("sigma must be a positive integer power of two")
    k = abs(k)
    if k > 8 * sigma:
        raise ValueError("rho_interval needs |k| <= 8*sigma")
    if k == 0:
        return Q, Q
    pl, pu = pi_interval()
    denominator = 256 * sigma * sigma
    ul = pl * k * k // denominator
    uu = _ceildiv(pu * k * k, denominator)
    assert 0 <= ul <= uu <= Q and uu - ul <= 4
    tl = tu = Q
    sl = su = Q
    for j in range(1, 81):
        d = j * Q
        tl = tl * ul // d
        tu = min(Q, _ceildiv(tu * uu, d))
        if j & 1:
            sl -= tu
            su -= tl
        else:
            sl += tl
            su += tu
    vl, vu = max(0, sl - 1), min(Q, su)
    for _ in range(8):
        vl = vl * vl >> PRECISION
        vu = min(Q, _ceildiv(vu * vu, Q))
    assert 0 <= vl <= vu <= Q and vu - vl < (1 << 19)
    return vl, vu


def threshold(k: int, sigma: int) -> int:
    """The SPEC lower 256-bit threshold, including its zero shortcut."""
    return rho_interval(k, sigma)[0] >> (PRECISION - BITS)


@lru_cache(maxsize=1)
def squeeze_table() -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Common normalized grid: certified lower/upper decision thresholds."""
    intervals = [rho_interval(j, GRID) for j in range(CELLS + 1)]
    shift = PRECISION - BITS
    low = tuple(max(0, (intervals[j + 1][0] >> shift) - 1)
                for j in range(CELLS))
    high = tuple(min(COIN_RANGE, _ceildiv(intervals[j][1], 1 << shift))
                 for j in range(CELLS))
    assert all(0 <= a <= b <= COIN_RANGE for a, b in zip(low, high))
    return low, high


class GaussianSampler:
    """sample(sigma,count) returns a list of centered integer coefficients.

    last_stats contains aggregate counts only. OS entropy is consumed locally
    per call; unused buffered bytes are discarded. No user-supplied RNG hook is
    exposed by the production API.
    """

    def __init__(self) -> None:
        start = time.perf_counter()
        self._low, self._high = squeeze_table()
        self._prefix_low = tuple(x >> SUFFIX_BITS for x in self._low)
        self._prefix_high = tuple(_ceildiv(x, 1 << SUFFIX_BITS) for x in self._high)
        self.table_seconds = time.perf_counter() - start
        self.last_stats: dict[str, int | float] = {}

    def sample(self, sigma: int, count: int) -> list[int]:
        if isinstance(sigma, bool) or not isinstance(sigma, int) or sigma < 1 or sigma & (sigma - 1):
            raise ValueError("sigma must be a positive integer power of two")
        if isinstance(count, bool) or not isinstance(count, int) or count < 0:
            raise ValueError("count must be a nonnegative integer")
        start = time.perf_counter()
        a = sigma.bit_length() - 1
        proposal_bytes = (a + 4 + 7) // 8
        stride = proposal_bytes + 4
        mask = 16 * sigma - 1
        boundary = 8 * sigma
        low, high = self._prefix_low, self._prefix_high
        direct = threshold
        from_bytes = int.from_bytes
        output: list[int] = []
        append = output.append
        proposals = squeeze_accepts = squeeze_rejects = gray = caps = boundaries = 0
        entropy_bytes = suffix_draws = 0
        attempt = 0
        buf = b""
        offset = 0
        while len(output) < count:
            if offset >= len(buf):
                block = min(BLOCK_PROPOSALS, max(32, (count - len(output)) * 16))
                buf = os.urandom(stride * block)
                entropy_bytes += len(buf)
                offset = 0
            k = (from_bytes(buf[offset:offset + proposal_bytes], "little") & mask) - boundary
            prefix = from_bytes(buf[offset + proposal_bytes:offset + stride], "little")
            offset += stride
            proposals += 1
            attempt += 1
            accepted = False
            if k == -boundary:
                boundaries += 1
            elif k == 0:
                squeeze_accepts += 1
                accepted = True
            else:
                cell = abs(k) * GRID // sigma
                if prefix < low[cell]:
                    squeeze_accepts += 1
                    accepted = True
                elif prefix >= high[cell]:
                    squeeze_rejects += 1
                else:
                    gray += 1
                    level = direct(k, sigma)
                    top, remainder = divmod(level, 1 << SUFFIX_BITS)
                    if prefix < top:
                        accepted = True
                    elif prefix == top and remainder:
                        suffix = from_bytes(os.urandom(SUFFIX_BITS // 8), "little")
                        entropy_bytes += SUFFIX_BITS // 8
                        suffix_draws += 1
                        accepted = suffix < remainder
            if accepted:
                append(k)
                attempt = 0
            elif attempt == CAP:
                append(0)
                caps += 1
                attempt = 0
        elapsed = time.perf_counter() - start
        self.last_stats = {
            "sigma": sigma, "count": count, "seconds": elapsed,
            "coefficients_per_second": count / elapsed if elapsed else 0,
            "proposals": proposals, "squeeze_accepts": squeeze_accepts,
            "squeeze_rejects": squeeze_rejects, "direct_threshold_evaluations": gray,
            "boundary_rejections": boundaries, "cap_fallbacks": caps,
            "os_random_bytes_requested": entropy_bytes,
            "random_bytes_consumed_in_proposals": proposals * stride,
            "suffix_draws": suffix_draws,
            "acceptance_prefix_bits": PREFIX_BITS,
            "proposal_bytes": proposal_bytes, "table_cells": CELLS,
        }
        return output


_default: GaussianSampler | None = None


def sample(sigma: int, count: int) -> list[int]:
    """Module convenience API; construct GaussianSampler for isolated stats."""
    global _default
    if _default is None:
        _default = GaussianSampler()
    return _default.sample(sigma, count)


def last_stats() -> dict[str, int | float]:
    return {} if _default is None else dict(_default.last_stats)
