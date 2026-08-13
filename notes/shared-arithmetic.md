# Interspersing inference with proving: where the arithmetic genuinely shares

2026-08-12. Ember's question: "is there any way whatsoever to intersperse
inference with proving and reduce total cost by shared arithmetics?" Yes — at
four levels, with one hard bound. Status: L1 known, L2–L3 unclaimed designs,
L4 an observation about vFHE. None measured by us yet.

## The hard bound first

Everything that depends on a post-commitment challenge can never be shared
with inference — the randomness arrives after the computation is fixed; that
is what makes it sound (roots-before-challenges). So the shareable surface is
exactly: witness generation, commitment, and the challenge-independent part of
the sumcheck rounds. Amdahl over those.

## L1 — witness generation collapses into inference (known; formats decide it)

Witness-gen is re-running the computation. If the model's native format embeds
exactly into the field — MXFP4/exact-integer paths, where a k=32 block dot is
an exact ≤13-bit integer — then **the inference run IS the field-valued
witness**: no quantize-recompute pass, no float→field re-execution. This is
the deep reason exact native formats matter beyond soundness: they make
witness generation *free by identity*, not cheap. (Non-exact paths pay a full
re-execution; zkPoG and the zkVM SoK are the only places the field even
measures witness-gen cost.)

## L2 — choose the PCS so commitment is matmul-shaped (unclaimed design)

The Ω(m) commitment floor on activations stands in op-count. But in
linear-code PCS (Brakedown/Orion/Ligero family) **encoding is a linear map —
a matmul** — over small integers. That is the hardware's native op. So choose
the PCS by *op-class match with inference*: commitment work becomes more
matmul, interleavable in the same kernel stream on tensor cores idling in the
memory-bound decode bubble, instead of Poseidon on the saturated-nothing int
pipeline. Nobody frames PCS choice this way (the mine: 64 crypto-on-AI-hardware
papers, zero SNARK provers on tensor cores).

## L3 — harvest the reduction tree (novel; needs a harness)

Sumcheck's round structure is a variable-at-a-time fold — a binary tree. The
matmul kernel's accumulation is ALSO a reduction tree. If the proof's variable
ordering is chosen to match the kernel's tree, then round-1's g(0)/g(1) are
literally the left/right subtree partial sums the kernel already computed.
Later rounds bind challenges and need fresh folds — BUT the small-value
sumcheck line (Dao–Thaler 2024/1038, 2026/587's 2–20×) computes early rounds
directly from original small values, i.e. over exactly the data inference is
already streaming. The shareable fraction is real and unmeasured; the design
question is "co-scheduled sumcheck": pick variable order = kernel tree order,
fuse the passes. Bonus: the proof then pins the tree the hardware actually
used, eating part of the order-dependence problem from the OCP spec.

## L4 — vFHE has the sharing property BY CONSTRUCTION

FHE evaluation already happens in Z_q ring arithmetic. There is no
float→field gap AT ALL: the ciphertext trace IS a field-valued witness, and
proving FHE evaluation is proving arithmetic the FHE engine already performed
in the proof-compatible domain. This is a concrete, structural reason
"STARK × FHE" is a synergy rather than a product of two overheads — beyond
Vitalik's almost-linearity point. The NTTs inside FHE ops are also exactly the
transform machinery STARK provers know how to amortize.

## What this changes

The bubble idea (missed-threads item 2) was about *hardware co-location* —
idle pipelines. This is stronger: L1 and L3 are *the same arithmetic*, not
adjacent arithmetic. The stack that falls out: exact native format (L1) +
Brakedown-family PCS (L2) + co-scheduled small-value sumcheck (L3), fused into
the serving kernel — with the challenge-dependent tail as the only
irreducibly-extra work. Next concrete step: cost the challenge-dependent tail
as a fraction of total prover work in a real system; if it is small, "proving
costs about one inference-time" stops being an observation about Attestable
and becomes a design target with a mechanism.
