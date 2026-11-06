# GPU decisions — source study, 2026-11-06

[READ] Research method: local source inspection plus direct fetches of the primary pages linked below; zero Kagi/search queries. No GPU rented, application submitted, remote host accessed, or performance measured. Numbers attributed to providers are advertised rates or specifications, not capacity reservations. [MEASURED] is intentionally absent: these are not benchmark results.

## 2. Apply for VCF access to produce fresh FlashProve proofs?

**Question.** Is Lucid-operated Verifiable Compute Foundation access worth applying for while Ember interviews with Lucid?

**Options.** Continue the two stored-proof experiment; buy commercial capacity; or apply to VCF for a bounded, openly publishable experiment.

**Recommendation [INFERRED].** Apply through VCF's ordinary research program. Ask for **one exclusive H100 80 GB on `h100-sxm-8-0`, 512 GB host RAM, at least 500 GB local scratch, and an initial eight GPU-hours**, with a checkpoint after the first fresh exact-match proof. Those resource margins and time budget are my proposed allocation, not measured requirements. Require permission to publish positive and negative results, full reproducibility artifacts, and the sponsorship disclosure. Keep hiring and access decisions separate. Disclose the interview relationship in the application; report donated compute in the eventual experiment. This is a manageable potential conflict, not a reason to forgo useful research. Do not describe results as an independent evaluation of Lucid's own product.

**Evidence.**

- [READ] The [current VCF page](https://verifiablecompute.ai/) says its free research program is open to academic, nonprofit, startup, industry and government researchers; two H100 nodes are operational. Its [specification](https://docs.google.com/document/d/1wjHIr3uPJ9BAuxNqzGFgXjuGArb7_D7LNi_UnG5RfBE/edit) lists an 8×H100 DGX with 2 TiB RAM and 34 TB raw NVMe, and a separate confidential-computing H100 NVL with 768 GB RAM. Therefore the hardware already exists in beta; the interview brief's older “opening in November” is no longer the best availability evidence. The [Lucid cluster page](https://lucidcomputing.ai/experimentation-cluster) confirms free VCF access and reconfiguration by arrangement.
- [READ] `/Users/ember/src/FlashProve/README.md:55–69`: supported prover needs exclusive H100 80 GB, x86 Linux, CUDA 13.2.86, gcc/g++ 13 and local disk. Small synthetic proving needs 10 GB RAM, full-size synthetic 280 GB, real Maverick 330 GB and 245 GB disk. Thus the grounding's 330 GB applies to its real-weight ambition, not every fresh-proof experiment. [VCF Slurm documentation](https://docs.vcf.lucidcomputing.ai/guides/running-jobs/gpu-jobs/) allocates only 200 GB/GPU by default: explicitly request more. Its FAQ says ordinary users have no sudo; settle driver/toolchain and local-scratch access before scheduling.
- [READ] `notes/flashprove-audit/GROUNDING.md` §§1,3,5: the current population repeats two stored triples; the existing experiment already measures real verifier calls, withholding and false-claim detection. Fresh generation adds new requests/outputs, source-to-commitment-to-proof execution, actual producer failure/abort behavior and adversarial producer modifications. It does **not** discharge the C++/Lean verifier correspondence, random-oracle assumptions, model identity outside the supplied commitment, or completeness of an external service. Begin with synthetic small/full-size proofs, then real public weights with calibration; don't conflate the tiers.
- [READ] `/Users/ember/dev/whatember/LUCID-INTERVIEW-BRIEF-2026-11-05.md` §§1–5 records the overlap and interview context. [INFERRED] Use ordinary DGX capacity first: FlashProve's cryptographic claim does not require a trusted host. CC experiments are separately useful, not a prerequisite.

**What changes my mind.** Publication veto, exclusivity/IP restrictions, incompatible driver, inability to allocate host RAM/local disk, or a queue longer than buying equivalent time. Eight hours is a setup budget, not a promise of complete real-Maverick results.

**Cost of being wrong.** Setup time and research delay; perceived sponsor influence. Preserve a commodity-cloud reproduction path and publish failed runs as well as successes.

## 10. Which GPU should initiative 14 rent for one hour?

**Question.** What is the cheapest useful next hardware experiment, without borrowing another project's machine?

**Options.** Wait for VCF; rent H100; rent B200/B300; or leave the result at a counts model.

**Recommendation [INFERRED].** Prepare the complete runnable probe package, then book **one exclusive Runpod H100 SXM for one hour**, with a proposed **$10 total cap** allowing setup/storage. Use VCF instead if access has already arrived. H100 directly checks the TensorZKP comparison and the unknown Hopper binary-matrix rate. Follow with B200 only when the Blackwell instruction probes are ready. B300 is ultimately more informative for the lane's FP8-versus-degraded-INT8 hypothesis; B200 does not answer that B300-specific question.

**Evidence and price snapshot, fetched 2026-11-06.**

| Provider | H100, one GPU-hour | B200, one GPU-hour | Meaning |
|---|---:|---:|---|
| [Runpod Pods](https://www.runpod.io/pricing) [READ] | SXM $3.99; PCIe $2.89 | $7.99 | Page updated November 4; displayed Pod rates, subject to SKU/region availability and storage. B300 is $8.99. |
| [Modal](https://modal.com/pricing) [READ→INFERRED] | SXM $3.9492 | $6.2496 | GPU-only: published per-second rates ×3,600; CPU, memory and other charges additional. Preemptible Functions baseline, not a dedicated-machine guarantee. |
| [Lambda](https://lambda.com/pricing) [READ] | Current quote requires login | Current quote requires login | Public $4.89 SXM/$7.99 B200 single-GPU rows take effect **November 16**, ten days after this study; do not quote them as today's rates. |
| [VCF](https://verifiablecompute.ai/) [READ] | Free grant if accepted | Not currently listed operational | Beta H100 capacity; queue/admission cost rather than rental charge. |

[INFERRED] One hour on H100 plus one on B200 totals $11.98 in Runpod GPU charges, before setup/storage; propose $20 for the two-stage investigation, not an open-ended rental. This is a recommendation, not spending authorization or an executed purchase. Choose SXM over cheaper PCIe to match the published TensorZKP hardware and its bandwidth comparison. Normal cloud access suffices for arithmetic correctness and speed; neither these prices nor “Secure Cloud” establish a verified confidential-computing path.

[READ] `notes/tensor-core-holography/GROUNDING.md` §§2–4 and `F3-MODEL.md` §§1–3 make memory bandwidth, accumulator behavior, binary-matrix instruction rate and Keccak speed the unresolved inputs. `/Users/ember/dev/degg-research/experiments/mma-accumulator-probe/README.md:7–35` prefers B300 for Blackwell questions, but its actual `probe.cu:1–13` is uncompiled and explicitly covers the C-accumulator path only; the within-instruction group probe is still a recipe. [INFERRED] A “one-hour protocol” is not yet a ready one-hour artifact. Compile/package dependencies first; preserve source, driver/compiler versions, GPU model/clocks and raw outputs. A hashcat benchmark is a workload proxy, not automatically the exact Keccak-f permutation count used by the prover.

[READ] `/Users/ember/swarm/MACHINES.md`, “Other hosts”: `vast` and the other named aliases belong to other projects; no GPU is recorded for Ember's designated build machines. Do not use those aliases.

**What changes my mind.** Immediate VCF access; unavailable SXM capacity; or a ready Blackwell kernel whose uncertainty dominates the decision. For that last case, rent B300 first and keep its result separate from H100 claims.

**Cost of being wrong.** Roughly the proposed $10–20 experiment cap and a wasted setup session. The larger risk is inferring whole-prover acceleration from peak matrix throughput: the present Tower256 model is mostly hash work, so even a successful matrix experiment need not accelerate the prover much.
