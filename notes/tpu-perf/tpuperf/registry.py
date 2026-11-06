"""All workload kernels, by name."""
from .kernels import mxfp4, rns_ntt, sumcheck

KERNELS = {k["name"]: k for mod in (mxfp4, rns_ntt, sumcheck) for k in mod.KERNELS}
