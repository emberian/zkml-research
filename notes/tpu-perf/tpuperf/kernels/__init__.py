"""Workload kernels. Each module exposes KERNELS: a list of dicts with
  name, cfgs {cfg_name: params}, inputs(rng, **params) -> tuple of numpy arrays,
  ref(*np_inputs, **params) -> numpy output (exact, int64/object math),
  impl(**params) -> jittable fn over device arrays (the tuned kernel),
  count(**params) -> jittable pure-jnp fn with the same math, used only for op/byte counts,
  check(out, ref) -> bool (bit-exact),  mxu_edge-independent.
"""
