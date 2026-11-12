"""Run LLMCompass (PrincetonUniversity/LLMCompass @2e015fd) on our shapes and devices.
usage: cd <a COPY of the LLMCompass repo> && python <this> <models dir>   (LLMCompass appends to its own
systolic_array_model/look_up_table_*.csv on cache misses, so never run it in a pristine clone)."""
import json, sys, time, pathlib
sys.path.insert(0, ".")
HERE = pathlib.Path(sys.argv[1]); sys.path.insert(0, str(HERE))
from devices import DEV
from hardware_model.compute_module import VectorUnit, SystolicArray, Core, ComputeModule, overhead_dict
from hardware_model.io_module import IOModule
from hardware_model.memory_module import MemoryModule
from hardware_model.device import Device
from software_model.matmul import Matmul, BatchedMatmul
from software_model.utils import Tensor, DataType

DT = {"int8": DataType("int8", 1), "fp8": DataType("fp8", 1), "fp16": DataType("fp16", 2)}

def gpu(name, dtype, hbm=None):
    d = DEV[name]
    peak = {"int8": d["int8"], "fp8": d["fp8"], "fp16": d["fp16"]}[dtype]
    if peak is None:
        return None
    arrays = 4
    mac = peak / (d["sm"] * arrays * 256 * d["clk"])       # mac_per_cycle per 16x16 array
    wsz = DT[dtype].word_size
    sa = SystolicArray(16, 16, mac, wsz, 4 if dtype != "fp16" else 2)
    vu = VectorUnit(512, 2, 35, 32, 4)                       # LLMCompass's A100 vector unit, per SM
    core = Core(vu, sa, arrays, d["smem_kb"] * 1024)
    cm = ComputeModule(core, d["sm"], d["clk"], d["l2"], d["l2_bpc"], overhead_dict["A100"])
    return Device(cm, IOModule(hbm or d["hbm"], 1e-6), MemoryModule(80e9))

def tpu(name, dtype):
    d = DEV[name]
    peak = d["int8"] if dtype in ("int8", "fp8") else d["bf16"]
    mac = peak / (d["mxu"] * d["mxu_dim"] ** 2 * d["clk"])
    sa = SystolicArray(d["mxu_dim"], d["mxu_dim"], mac, DT[dtype].word_size, 4)
    vu = VectorUnit(128 * 8 * 4, 4, 15, 128, 8)
    core = Core(vu, sa, d["mxu"], 16 << 20)                  # scoped VMEM default 16 MiB [READ: tpuperf lint vmem_limit]
    # LLMCompass's TPU convention (TPUv3 entry): HBM is the "L2", io bandwidth infinite
    cm = ComputeModule(core, 1, d["clk"], 16 << 30, d["hbm"] / d["clk"], overhead_dict["TPUv3"])
    return Device(cm, IOModule(float("inf"), 1e-6), MemoryModule(float("inf")))

def run(dev, s, mode):
    dt = DT[s["dtype"]]
    if s["batch"] > 1:
        # LLMCompass BatchedMatmul builds its inner Matmuls with fp16 Tensors whatever the dtype
        # (AssertionError for int8): its two formulas, restated with the dtype passed through.
        bs, M, K, N = s["batch"], s["M"], s["K"], s["N"]
        if mode == "roofline":
            m = Matmul(dt); m(Tensor([M, K], dt), Tensor([K, N], dt))
            return m.roofline_model(dev) * bs
        m1 = Matmul(dt); m1(Tensor([M, K], dt), Tensor([K, N], dt))
        l1 = m1.compile_and_simulate(dev, mode) * bs
        m2 = Matmul(dt); m2(Tensor([M, K * bs], dt), Tensor([K * bs, N], dt))
        l2 = m2.compile_and_simulate(dev, mode) + (bs - 1) * M * N * dt.word_size / dev.io_module.bandwidth
        return min(l1, l2)
    else:
        op = Matmul(dt)
        op(Tensor([s["M"], s["K"]], dt), Tensor([s["K"], s["N"]], dt))
    if mode == "roofline":
        return op.roofline_model(dev)
    return op.compile_and_simulate(dev, mode)

shapes = json.load(open(HERE / "shapes.json"))["gemm"]
out = []
targets = [("T4", None), ("T4@copy", 242e9), ("A100", None), ("H100", None), ("B200", None), ("B300", None), ("v5e", None), ("v6e", None)]
for tname, hbm in targets:
    base = tname.split("@")[0]
    for s in shapes:
        for dtype in ([s["dtype"]] + (["fp8"] if s["dtype"] == "int8" and base in ("H100", "B200", "B300") else [])):
            is_tpu = base.startswith("v")
            dev = tpu(base, dtype) if is_tpu else gpu(base, dtype, hbm)
            if dev is None:
                continue
            row = dict(device=tname, shape=s["name"], dtype=dtype)
            for mode in ("roofline", "heuristic-TPU" if is_tpu else "heuristic-GPU"):
                t0 = time.time()
                try:
                    row["roofline_s" if mode == "roofline" else "sim_s"] = run(dev, dict(s, dtype=dtype), mode)
                except Exception as e:
                    row["err_" + mode] = repr(e)[:200]
                row["wall_" + mode] = round(time.time() - t0, 2)
            if "t4_measured_s" in s and base == "T4" and dtype == s["dtype"]:
                row["t4_measured_s"] = s["t4_measured_s"]
            if "tpu_v5e_optimal_seconds" in s and base == "v5e":
                row["v5e_optimal_seconds"] = s["tpu_v5e_optimal_seconds"]
            print(json.dumps(row), flush=True)
            out.append(row)
json.dump(out, open(HERE / "out" / "llmcompass.json", "w"), indent=1)
