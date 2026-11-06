"""G2 on a Kaggle accelerator: fetch layer 0's pinned bytes, run gptoss-int v0 layer 0 with the int8-limb
JAX kernel on the device, compare every intermediate's digest with the Mac's numpy reference, then run
the float32 falsifier on the same device. Results go to $ACCEL_RESULTS."""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault("GPTOSS_DIR", "/tmp/gptoss")
os.environ["GPTOSS_IDS_FROM_PARAMS"] = "1"

import jax
jax.config.update("jax_enable_x64", True)
import jax.numpy as jnp

import remote

res = {"jax_version": jax.__version__, "backend": jax.default_backend(),
       "devices": [str(d.device_kind) for d in jax.devices()][:8]}
want = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("G2_WANT", "gpu")
out_path = os.environ["ACCEL_RESULTS"]


def save():
    json.dump(res, open(out_path, "w"), indent=1)


if res["backend"] != want:
    res["error"] = f"backend {res['backend']} is not {want}"
    save()
    sys.exit(3)

# what the device compiles an int8 x int8 -> int32 dot to (evidence, not a requirement)
a = jnp.ones((64, 2880), jnp.int8)
b = jnp.ones((512, 2880), jnp.int8)
f = jax.jit(lambda a, b: jax.lax.dot_general(a, b, (((1,), (1,)), ((), ())), preferred_element_type=jnp.int32))
hlo = f.lower(a, b).compile().as_text()
res["int8_dot_hlo"] = sorted({ln.strip()[:160] for ln in hlo.splitlines() if ("dot(" in ln or "custom-call" in ln or "convolution(" in ln)})[:8]

res["fetch"] = remote.materialize(os.path.join(HERE, "plan-layer0.json"), os.environ["GPTOSS_DIR"])
save()

import g1

ref = json.load(open(os.path.join(HERE, "g1-numpy.json")))["digests"]
for be in ("jax", "jax-f32"):
    t0 = time.time()
    try:
        g1.main(be)
        rec = json.load(open(os.path.join(HERE, f"g1-{be}.json")))
        res[be] = {"kernel": rec["backend"], "seconds": rec["seconds"], "digests": rec["digests"],
                   "equal_to_mac_numpy": {k: rec["digests"][k] == ref[k] for k in ref}}
    except Exception as e:
        res[be] = {"error": repr(e)[:2000]}
    res[be]["wall"] = round(time.time() - t0, 1)
    save()
res["bit_identical"] = bool(res.get("jax", {}).get("equal_to_mac_numpy")) and all(res["jax"]["equal_to_mac_numpy"].values())
save()
print(json.dumps({k: v for k, v in res.items() if k != "int8_dot_hlo"}, indent=1)[:4000])
