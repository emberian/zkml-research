#!/usr/bin/env python3
"""Five public-value exponentiations using an already installed native library.

This is an arithmetic feasibility probe, not a replacement IPFE implementation
or a constant-time audit. No credential or protected input is loaded.
"""
from pathlib import Path
import ctypes as c
import hashlib
import importlib.util
import json
import statistics
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
from additive_ipfe import P, Q, G


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    path = Path("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib").resolve()
    man = Path("/opt/homebrew/opt/openssl@3/share/man/man3/BN_mod_exp_mont.3ssl")
    library = c.CDLL(str(path))
    library.OpenSSL_version.argtypes = [c.c_int]
    library.OpenSSL_version.restype = c.c_char_p
    for name in ("BN_new", "BN_CTX_new"):
        getattr(library, name).argtypes = []
        getattr(library, name).restype = c.c_void_p
    for name in ("BN_clear_free", "BN_CTX_free"):
        getattr(library, name).argtypes = [c.c_void_p]
        getattr(library, name).restype = None
    library.BN_bin2bn.argtypes = [c.c_void_p, c.c_int, c.c_void_p]
    library.BN_bin2bn.restype = c.c_void_p
    library.BN_bn2binpad.argtypes = [c.c_void_p, c.c_void_p, c.c_int]
    library.BN_bn2binpad.restype = c.c_int
    library.BN_mod_exp_mont_consttime.argtypes = [c.c_void_p]*6
    library.BN_mod_exp_mont_consttime.restype = c.c_int

    def bn(value):
        raw = value.to_bytes(256, "big")
        buffer = c.create_string_buffer(raw)
        result = library.BN_bin2bn(buffer, len(raw), None)
        assert result
        return result

    # Fixed public values derived here. They are not a hidden-key challenge.
    base, exponent = pow(G, 123456789, P), Q//3
    a, e, modulus = bn(base), bn(exponent), bn(P)
    result, context = library.BN_new(), library.BN_CTX_new()
    assert result and context
    python_ns, native_ns = [], []
    try:
        for _ in range(5):
            start = time.perf_counter_ns()
            expected = pow(base, exponent, P)
            python_ns.append(time.perf_counter_ns()-start)
            start = time.perf_counter_ns()
            assert library.BN_mod_exp_mont_consttime(result, a, e, modulus, context, None) == 1
            native_ns.append(time.perf_counter_ns()-start)
            buffer = c.create_string_buffer(256)
            assert library.BN_bn2binpad(result, buffer, 256) == 256
            assert int.from_bytes(buffer.raw, "big") == expected
    finally:
        for pointer in (a, e, modulus, result):
            library.BN_clear_free(pointer)
        library.BN_CTX_free(context)
    report = {
        "passed": True, "scope": "five repeated public exponentiations; no IPFE replacement or secret data",
        "script_sha256": sha(__file__), "library_path": str(path), "library_sha256": sha(path),
        "library_version": library.OpenSSL_version(0).decode(),
        "manual_path": str(man), "manual_sha256": sha(man),
        "manual_location": "DESCRIPTION, source lines169-176: fixed-window exponent routine",
        "function": "BN_mod_exp_mont_consttime", "same_2048_bit_MODP_group": True,
        "public_base_rule": "pow(2,123456789,P)", "public_exponent_rule": "Q//3",
        "samples": 5, "python_ns": python_ns, "native_ns": native_ns,
        "python_median_ns": statistics.median(python_ns),
        "native_median_ns": statistics.median(native_ns),
        "whole_protocol_constant_time_claim": False,
        "full_crypto_measurement": False, "package_installations": 0,
        "installed_python_modules": {n: (str(importlib.util.find_spec(n).origin)
            if importlib.util.find_spec(n) else None) for n in ("gmpy2", "nacl", "cryptography", "Crypto", "sympy")},
    }
    (HERE/"native_results.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
