"""Sanity check (model output is SECONDS; dataset Latency is ms) of our NeuSight invocation: predict 12 of its own T4 BMM rows (training set) and compare with labels."""
import sys, types, json, pathlib, importlib
repo = pathlib.Path(sys.argv[1]).resolve()
pkg = types.ModuleType("neusight"); pkg.__path__ = [str(repo / "neusight")]; sys.modules["neusight"] = pkg
import torch, pandas as pd
mp = importlib.import_module("neusight.Model.model_provider")
A = repo / "scripts/asplos/data"
model = mp.model_provider(A / "predictor/MLP_WAVE/BMM/config.json", device="cpu")
model.load_state(A / "predictor/MLP_WAVE/BMM/model.pth"); model.set_meta_table(A / "dataset/train/bmm.csv"); model.eval()
cfg = json.load(open(A / "device_configs/Tesla_T4.json"))
df = pd.read_csv(A / "dataset/train/bmm.csv"); df = df[df.Device == "Tesla T4"]
df = df.assign(fl=df.B * df.M * df.N * df.K).sort_values("fl").iloc[::max(1, len(df) // 12)]
for _, r in df.iterrows():
    p = dict(B=r.B, M=r.M, N=r.N, K=r.K); p.update(cfg)
    x = torch.tensor([[float(p[f]) for f in model.features]])
    with torch.no_grad():
        y = float(model(opname=["bmm"], x=x, device=cfg["Device"], culib="cu121").squeeze())
    print(f"B{r.B} M{r.M} N{r.N} K{r.K}: label {r.Latency:.4f} ms pred {y * 1e3:.4f} ms ratio {y * 1e3 / r.Latency:.2f} GFLOP/s(label) {2 * r.fl / r.Latency / 1e6:.0f}")
