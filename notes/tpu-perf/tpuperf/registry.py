"""All workload kernels, by name."""
from .kernels import freivalds, mxfp4, rns_ntt, sumcheck

KERNELS = {k["name"]: k for mod in (mxfp4, rns_ntt, sumcheck, freivalds) for k in mod.KERNELS}
