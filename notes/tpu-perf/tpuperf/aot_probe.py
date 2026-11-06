"""Deviceless TPU AOT probe: does JAX + libtpu compile for a TPU topology on a host with no TPU attached?
Runs a plain int8 dot and a Pallas TPU kernel through lower+compile against get_topology_desc, and prints
what the real TPU compiler produced (optimized HLO head, cost_analysis, memory_analysis)."""
import json, sys, traceback
import jax, jax.numpy as jnp
from jax.experimental import topologies
from jax.sharding import SingleDeviceSharding

R = {"jax": jax.__version__, "backend_default": None}
try:
    R["backend_default"] = jax.default_backend()
except Exception as e:
    R["backend_default"] = repr(e)[:200]
name = sys.argv[1] if len(sys.argv) > 1 else "v5e:1x1"
try:
    topo = topologies.get_topology_desc(platform="tpu", topology_name=name)
    devs = topo.devices
    R["topology"] = name
    R["devices"] = [str(d) for d in devs][:4]
    R["device_kind"] = devs[0].device_kind
except Exception as e:
    R["topology_error"] = traceback.format_exc()[-1500:]
    print(json.dumps(R, indent=1)); sys.exit(1)

shd = SingleDeviceSharding(devs[0])
def spec(shape, dt):
    return jax.ShapeDtypeStruct(shape, dt, sharding=shd)

def go(tag, f, *args):
    try:
        low = jax.jit(f).lower(*args)
        c = low.compile()
        txt = c.as_text()
        R[tag] = {"ok": True, "hlo_lines": txt.count("\n"), "hlo_head": txt[:1500],
                  "cost": {k: v for k, v in (c.cost_analysis() or {}).items()} if not isinstance(c.cost_analysis(), list) else c.cost_analysis()[0],
                  "mem": str(c.memory_analysis())}
    except Exception:
        R[tag] = {"ok": False, "err": traceback.format_exc()[-2500:]}

go("int8_dot", lambda a, b: jnp.dot(a, b, preferred_element_type=jnp.int32),
   spec((1024, 1024), jnp.int8), spec((1024, 1024), jnp.int8))

from jax.experimental import pallas as pl
def kern(a_ref, b_ref, o_ref):
    o_ref[...] = jnp.dot(a_ref[...], b_ref[...], preferred_element_type=jnp.int32)
def pmm(a, b):
    return pl.pallas_call(kern, out_shape=jax.ShapeDtypeStruct((1024, 1024), jnp.int32),
                          grid=(4, 4),
                          in_specs=[pl.BlockSpec((256, 1024), lambda i, j: (i, 0)),
                                    pl.BlockSpec((1024, 256), lambda i, j: (0, j))],
                          out_specs=pl.BlockSpec((256, 256), lambda i, j: (i, j)))(a, b)
go("pallas_int8", pmm, spec((1024, 1024), jnp.int8), spec((1024, 1024), jnp.int8))
print(json.dumps(R, indent=1, default=str))
