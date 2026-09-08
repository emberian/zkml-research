"""[DERIVED] Native screening with the pinned exact finite Gaussian fallback.

See DESIGN.md. Output law and stats interface match the frozen Python baseline
for widths up to 2^59; only public-source native build artifacts are persisted.
"""
from __future__ import annotations

import ctypes as C
from functools import lru_cache
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import types

HERE = Path(__file__).resolve().parent
REFERENCE_SHA256 = "2258da232fb6a3459f58c9842f9560baef7796bacaedfd757a4ae27b37c033dd"
_reference_bytes = (HERE / "reference.py").read_bytes()
if hashlib.sha256(_reference_bytes).hexdigest() != REFERENCE_SHA256:
    raise RuntimeError("frozen threshold reference source hash mismatch")
reference = types.ModuleType("_fast_sampler_exact_reference")
exec(compile(_reference_bytes, str(HERE / "reference.py"), "exec"), reference.__dict__)
CAP = reference.CAP
SUFFIX_BITS = reference.SUFFIX_BITS
BLOCK_PROPOSALS = 65536
threshold = reference.threshold


class _State(C.Structure):
    _fields_ = [(name, C.c_uint64) for name in
                ("offset", "produced", "proposals", "squeeze_accepts", "squeeze_rejects",
                 "gray", "boundaries", "caps", "attempt")] + [
                     ("pending_k", C.c_int64), ("pending_prefix", C.c_uint64)]


@lru_cache(maxsize=1)
def _native():
    source = HERE / "proposal_screen.c"
    compiler = shutil.which("cc")
    if compiler is None:
        raise RuntimeError("a C compiler named cc is required for the native sampler")
    flags = ["-O3", "-std=c11", "-fPIC", "-Wall", "-Wextra", "-Werror",
             "-dynamiclib" if sys.platform == "darwin" else "-shared"]
    digest = hashlib.sha256(source.read_bytes() + repr(flags).encode()).hexdigest()
    build = HERE / "_build"
    build.mkdir(exist_ok=True)
    library = build / ("proposal_screen_" + digest[:20] + ".so")
    command = [compiler, *flags, str(source), "-o", str(library)]
    if not library.exists():
        temporary = library.with_suffix(f".{os.getpid()}.tmp.so")
        subprocess.run([compiler, *flags, str(source), "-o", str(temporary)],
                       check=True, capture_output=True, text=True)
        temporary.replace(library)
    native = C.CDLL(str(library))
    native.screen.argtypes = [C.c_char_p, C.c_uint64, C.c_uint,
                              C.POINTER(C.c_uint64), C.POINTER(C.c_uint64),
                              C.POINTER(C.c_int64), C.c_uint64, C.POINTER(_State)]
    native.screen.restype = C.c_int
    return native, command, library


class GaussianSampler:
    def __init__(self) -> None:
        start = time.perf_counter()
        low, high = reference.squeeze_table()
        self._prefix_low = (C.c_uint64 * len(low))(*(v >> SUFFIX_BITS for v in low))
        self._prefix_high = (C.c_uint64 * len(high))(*(
            reference._ceildiv(v, 1 << SUFFIX_BITS) for v in high))
        self.table_seconds = time.perf_counter() - start
        build_start = time.perf_counter()
        self._library, self.build_command, self.library_path = _native()
        self.native_load_seconds = time.perf_counter() - build_start
        self.last_stats: dict[str, int | float] = {}

    def sample(self, sigma: int, count: int) -> list[int]:
        if isinstance(sigma, bool) or not isinstance(sigma, int) or sigma < 1 or sigma & (sigma - 1):
            raise ValueError("sigma must be a positive integer power of two")
        if sigma > (1 << 59):
            raise ValueError("native sampler supports sigma <= 2^59")
        if isinstance(count, bool) or not isinstance(count, int) or count < 0:
            raise ValueError("count must be a nonnegative integer")
        start = time.perf_counter()
        a = sigma.bit_length() - 1
        proposal_bytes = (a + 11) // 8
        stride = proposal_bytes + 4
        storage = (C.c_int64 * count)()
        state = _State()
        state_ptr = C.byref(state)
        screen = self._library.screen
        entropy_bytes = suffix_draws = native_calls = 0
        while state.produced < count:
            block = min(BLOCK_PROPOSALS, max(32, (count - state.produced) * 16))
            buf = os.urandom(stride * block)
            entropy_bytes += len(buf)
            state.offset = 0
            while state.offset < block and state.produced < count:
                code = screen(buf, block, a, self._prefix_low, self._prefix_high,
                              storage, count, state_ptr)
                native_calls += 1
                if code < 0:
                    raise RuntimeError("native proposal screening invariant rejected")
                if code == 0:
                    break
                k, prefix = state.pending_k, state.pending_prefix
                top, remainder = divmod(threshold(k, sigma), 1 << SUFFIX_BITS)
                accepted = prefix < top
                if prefix == top and remainder:
                    suffix = int.from_bytes(os.urandom(SUFFIX_BITS // 8), "little")
                    entropy_bytes += SUFFIX_BITS // 8
                    suffix_draws += 1
                    accepted = suffix < remainder
                if accepted:
                    storage[state.produced] = k
                    state.produced += 1
                    state.attempt = 0
                elif state.attempt == CAP:
                    storage[state.produced] = 0
                    state.produced += 1
                    state.caps += 1
                    state.attempt = 0
        result = list(storage)
        elapsed = time.perf_counter() - start
        self.last_stats = {
            "sigma": sigma, "count": count, "seconds": elapsed,
            "coefficients_per_second": count / elapsed if elapsed else 0,
            "proposals": state.proposals, "squeeze_accepts": state.squeeze_accepts,
            "squeeze_rejects": state.squeeze_rejects,
            "direct_threshold_evaluations": state.gray,
            "boundary_rejections": state.boundaries, "cap_fallbacks": state.caps,
            "os_random_bytes_requested": entropy_bytes,
            "random_bytes_consumed_in_proposals": state.proposals * stride,
            "suffix_draws": suffix_draws,
            "acceptance_prefix_bits": reference.PREFIX_BITS,
            "proposal_bytes": proposal_bytes, "table_cells": reference.CELLS,
            "native_calls": native_calls,
        }
        return result


_default: GaussianSampler | None = None


def sample(sigma: int, count: int) -> list[int]:
    global _default
    if _default is None:
        _default = GaussianSampler()
    return _default.sample(sigma, count)


def last_stats() -> dict[str, int | float]:
    return {} if _default is None else dict(_default.last_stats)
