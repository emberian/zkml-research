"""Run NeuSight (sitar-lab/NeuSight @6945927, ASPLOS'25) pretrained MLP_WAVE BMM predictor on our shapes, CPU only.
usage: python run_neusight.py <NeuSight repo> <models dir>
neusight/__init__.py imports Dataset/collect.py, which creates torch.cuda.Event at import time and fails without
CUDA; we register a stub package so only Model/ and Dataset/dataset.py load."""
import sys, types, json, pathlib, importlib
repo, here = pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve()
pkg = types.ModuleType("neusight"); pkg.__path__ = [str(repo / "neusight")]; sys.modules["neusight"] = pkg
import torch
mp = importlib.import_module("neusight.Model.model_provider")
sys.path.insert(0, str(here)); from devices import DEV

A = repo / "scripts/asplos/data"
model = mp.model_provider(A / "predictor/MLP_WAVE/BMM/config.json", device="cpu")
model.load_state(A / "predictor/MLP_WAVE/BMM/model.pth")
model.set_meta_table(A / "dataset/train/bmm.csv")
model.eval()

cfgs = {n: json.load(open(A / f"device_configs/{f}.json")) for n, f in
        [("T4", "Tesla_T4"), ("A100", "NVIDIA_A100-SXM4-40GB"), ("H100", "NVIDIA_H100_80GB_HBM3")]}
shapes = json.load(open(here / "shapes.json"))["gemm"]
out = []
for dname, cfg in cfgs.items():
    for variant in ("fp32_config", "tensor_peak_as_SingleFLOPs"):
        c = dict(cfg)
        if variant != "fp32_config":
            c["SingleFLOPs"] = 2 * DEV[dname]["int8"] / 1e9      # GOPS, int8 dense peak: out of training range
        for s in shapes:
            if s["name"].startswith("xla"):
                continue
            p = dict(B=s["batch"], M=s["M"], N=s["N"], K=s["K"]); p.update(c)
            x = torch.tensor([[float(p[f]) for f in model.features]])
            with torch.no_grad():
                sec = float(model(opname=["bmm"], x=x, device=c["Device"], culib="cu121").squeeze())
            row = dict(device=dname, variant=variant, shape=s["name"], pred_s=sec,
                       tiles=[float(t) for t in model.last_tiles.squeeze().tolist()])
            if dname == "T4" and "t4_measured_s" in s:
                row["t4_measured_s"] = s["t4_measured_s"]; row["ratio"] = row["pred_s"] / s["t4_measured_s"]
            print(json.dumps(row)); out.append(row)
json.dump(out, open(here / "out/neusight.json", "w"), indent=1)
