"""Same-group native exponent helper; no whole-protocol constant-time claim."""
from pathlib import Path
import ctypes as c

LIBRARY = Path("/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib").resolve()


class NativePow:
    def __init__(self, modulus, record_for_private_verification=False):
        self.modulus = modulus
        self.width = (modulus.bit_length()+7)//8
        self.calls = [] if record_for_private_verification else None
        lib = self.lib = c.CDLL(str(LIBRARY))
        for name in ("BN_new", "BN_CTX_new"):
            getattr(lib,name).argtypes = []
            getattr(lib,name).restype = c.c_void_p
        for name in ("BN_clear_free", "BN_CTX_free"):
            getattr(lib,name).argtypes = [c.c_void_p]
            getattr(lib,name).restype = None
        lib.BN_bin2bn.argtypes = [c.c_void_p,c.c_int,c.c_void_p]
        lib.BN_bin2bn.restype = c.c_void_p
        lib.BN_bn2binpad.argtypes = [c.c_void_p,c.c_void_p,c.c_int]
        lib.BN_bn2binpad.restype = c.c_int
        lib.BN_mod_exp_mont_consttime.argtypes = [c.c_void_p]*6
        lib.BN_mod_exp_mont_consttime.restype = c.c_int
        self.modulus_bn = self.bn(modulus)
        self.result = lib.BN_new()
        self.context = lib.BN_CTX_new()
        assert self.result and self.context

    def bn(self, integer):
        raw = integer.to_bytes(max(1,(integer.bit_length()+7)//8),"big")
        result = self.lib.BN_bin2bn(c.create_string_buffer(raw), len(raw), None)
        if not result:
            raise RuntimeError("BN allocation")
        return result

    def __call__(self, base, exponent, modulus):
        if modulus != self.modulus:
            raise ValueError("different modulus")
        original = (base, exponent, modulus)
        base %= modulus
        if exponent < 0:
            # Inversion is CPython's variable-time operation. Private encryption
            # uses only public-base inversion in its fixed message table.
            base, exponent = pow(base,-1,modulus), -exponent
        a, e = self.bn(base), self.bn(exponent)
        try:
            if self.lib.BN_mod_exp_mont_consttime(self.result,a,e,self.modulus_bn,self.context,None) != 1:
                raise RuntimeError("native modular exponentiation")
            buffer = c.create_string_buffer(self.width)
            if self.lib.BN_bn2binpad(self.result,buffer,self.width) != self.width:
                raise RuntimeError("native output encoding")
            value = int.from_bytes(buffer.raw,"big")
        finally:
            self.lib.BN_clear_free(a)
            self.lib.BN_clear_free(e)
        if self.calls is not None:
            # Micro audit only; this list never leaves its private role process.
            self.calls.append((*original,value))
        return value

    def close(self):
        self.lib.BN_clear_free(self.modulus_bn)
        self.lib.BN_clear_free(self.result)
        self.lib.BN_CTX_free(self.context)
        if self.calls is not None:
            self.calls.clear()
