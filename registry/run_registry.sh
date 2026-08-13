#!/usr/bin/env bash
# Reproduce the registry: every commitment in COMMITMENTS.md comes from this
# script.  Sequential on purpose -- the link is the bottleneck (~12 MB/s
# measured, and parallel range streams do not raise the aggregate), so running
# models concurrently would only corrupt the per-model cost measurements.
#
# Usage: ./run_registry.sh [full|structure|gated|rerun|all]
set -u
cd "$(dirname "$0")"
TOOL="python3 registry_tool.py"
LOGS="runs"
mkdir -p "$LOGS" manifests

stamp() { date -u +%Y-%m-%dT%H:%M:%SZ; }

commit_full() {  # repo
  local repo="$1" slug="${1//\//__}"
  echo "=== $(stamp) FULL $repo ==="
  $TOOL commit "$repo" --mode full 2>&1 | tee "$LOGS/${slug}.full.log"
}

commit_structure() {  # repo
  local repo="$1" slug="${1//\//__}"
  echo "=== $(stamp) STRUCTURE $repo ==="
  $TOOL commit "$repo" --mode structure 2>&1 | tee "$LOGS/${slug}.structure.log"
}

probe_gated() {  # repo -- expected to fail; we record HOW
  local repo="$1" slug="${1//\//__}"
  echo "=== $(stamp) GATED PROBE $repo ==="
  $TOOL commit "$repo" --mode structure --out "$LOGS/${slug}.attempt.json" \
    2>&1 | tee "$LOGS/${slug}.gated.log"
  echo "exit=$?" | tee -a "$LOGS/${slug}.gated.log"
}

what="${1:-all}"

if [ "$what" = full ] || [ "$what" = all ]; then
  commit_full openai/gpt-oss-20b
  # reproducibility gate: same repo, from scratch, into a separate file
  echo "=== $(stamp) FULL RERUN openai/gpt-oss-20b ==="
  $TOOL commit openai/gpt-oss-20b --mode full \
    --out "$LOGS/openai__gpt-oss-20b.rerun.json" 2>&1 \
    | tee "$LOGS/openai__gpt-oss-20b.rerun.log"
  commit_full Qwen/Qwen3-8B
  echo "=== $(stamp) FULL RERUN Qwen/Qwen3-0.6B ==="
  $TOOL commit Qwen/Qwen3-0.6B --mode full \
    --out "$LOGS/Qwen__Qwen3-0.6B.rerun.json" 2>&1 \
    | tee "$LOGS/Qwen__Qwen3-0.6B.rerun.log"
fi

if [ "$what" = structure ] || [ "$what" = all ]; then
  commit_structure openai/gpt-oss-120b
  commit_structure deepseek-ai/DeepSeek-V3.1
  commit_structure moonshotai/Kimi-K3
fi

if [ "$what" = gated ] || [ "$what" = all ]; then
  probe_gated deepseek-ai/DeepSeek-V4
  probe_gated meta-llama/Llama-3.1-8B-Instruct
  probe_gated google/gemma-3-27b-it
fi

echo "=== $(stamp) DONE ==="
