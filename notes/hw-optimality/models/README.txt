hw-optimality/models: analytical and learned GPU/TPU performance predictors, run on our shapes (2026-11-06)

Inputs (edit these, everything else derives):
  devices.py   peak rates, HBM bandwidth, SM/clock per SKU, each tagged [DS]/[M]/[F3]/[SB]/[A]/[INF]
  shapes.json  our GEMM shapes with the T4 measurements (MMA.md) and the TPU static results (tpu-perf)

Tools, pinned (Mac, CPU only; no GPU or traces needed):
  LLMCompass   github.com/PrincetonUniversity/LLMCompass @2e015fd (BSD-3)
  NeuSight     github.com/sitar-lab/NeuSight @6945927 (MIT), pretrained MLP_WAVE BMM predictor
  aiconfigurator github.com/ai-dynamo/aiconfigurator @6cd6f96 (Apache-2.0), sparse checkout of
               aic-core/src/aiconfigurator_core/systems/data/{a100_sxm,h100_sxm,b200_sxm,b300_sxm}/gemm/trtllm/
  venv: uv venv -p 3.11; uv pip install numpy==1.26.4 pandas==2.2.3 pyarrow==18.1.0 scalesim==2.0.2 torch==2.5.1
        pyyaml==6.0.2 transformers==4.38.1 tqdm==4.67.1 scipy==1.14.1 tensorboard==2.18.0 torchvision==0.20.1

Rerun (W = this directory, V = venv python):
  cp -R <LLMCompass clone> run-llmc && mkdir -p run-llmc/systolic_array_model/temp && cd run-llmc
  nice -n 15 V W/run_llmcompass.py W        # ~40 min on the Mac (heuristic mapper search); writes out/llmcompass.json
     LLMCompass appends to its own look-up tables on a miss: always run in a copy.
  V -I W/check_neusight.py <NeuSight>       # self-check on its own T4 rows (out/neusight_selfcheck.txt)
  V -I W/run_neusight.py <NeuSight> W       # out/neusight.json
  V -I W/aic_lookup.py <aiconfigurator> W   # out/aiconfigurator_gemm.{json,txt}
  python3 -I W/summarize.py W               # out/summary.txt (all tables)

Workarounds applied (in our drivers, not in the tools' trees):
  LLMCompass BatchedMatmul builds fp16 inner tensors whatever the dtype (AssertionError for int8): restated in
    run_llmcompass.py with the dtype passed through. LLMCompass Matmul.roofline_model counts elements, not bytes
    (exact for int8, 2x optimistic for fp16), and gives the output the input dtype (int32 output undercounted 4x).
  NeuSight's package __init__ creates torch.cuda.Event at import: we load neusight.Model via a stub package.
    Its BMM model returns SECONDS; the dataset labels are ms.
