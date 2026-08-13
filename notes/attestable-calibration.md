# Attestable, calibrated — and a correction to our own relay

2026-08-13. Recon lane final (S-two whitepaper deep read + public recon + a
54-minute founder interview, ~28 min whisper-transcribed and grep-verified).
Every claim tagged [stated] / [inferred] / [unknown].

## The correction to OUR record first

I relayed Vitalik's "single-digit overhead for LLM proving" as established.
**The truer statement: the overhead number is a baseline choice, not a
measurement.** The lane derived 1.4–2.0× against a batch-1 single-thread
decode baseline and 123–241× against a prefill/throughput baseline — and the
CEO, unprompted, gives the same answer [stated]:

> "It's not like the overhead is 10%. The overhead, it depends on how you
> count it. It's between, I don't know, between 2x and, I don't know, 100x,
> really depending on the configuration."

**"<10×" is Vitalik's estimate against the most favorable baseline, not
Attestable's claim. Their own CEO's top of range is 100×.** Cite the 2×–100×
quote. And he volunteers the reconciliation [stated]: *"It's enough to prove a
very small portion of what you've been doing"* — i.e. the sampling firewall
means overhead is not paid per inference. **Their deployment economics are the
commit-then-audit amortization** (our missed-threads item 1; prior art
2026/541), not a cheap prover. The single-digit ladder rung is real only in
that composite sense.

## The trust base, as stated vs as is

[stated] "specifically we use hash based zero knowledge proofs," collision
resistance presented as THE trust assumption. Two gaps:

1. [inferred, conditional] If they ship the whitepaper's **conjectured**
   parameter set, the trust base additionally includes **Conjectures 1–2**
   (RS list/line-decodability to the Elias radius) — unproven, introduced in
   §A.5 by his own co-founders, and sitting in territory where 2025/2046-class
   refutations are active. Proven vs conjectured readings of "100 bits" differ
   by **~30 bits**. Which regime ships: [unknown].
2. [mine] **"Zero knowledge" may be doing unearned work.** S-two §6 lists ZK
   as an unimplemented future release. Either Attestable built ZK themselves,
   or the phrase means "succinct." For a product proving inference over
   private weights, that distinction is the whole ballgame.

Both are questions to ask, collegially — alongside the (blowup, queries,
grinding) triple, which 28 minutes of free founder speech never named (zero
instances of STARK/FRI/AIR/sumcheck/GKR/Mersenne/S-two; grep-verified).

## Corroborations of the hybrid reading

[stated] *"the larger the model is, it's actually easier for us to prove…
**8 billion is the hard part**"* — inverse scaling is the signature of a
matmul-specialized sumcheck prover whose fixed costs amortize with size. With
the roofline analysis (trace-committed AIR matmul would be 2–8× over H100
bandwidth) and Papini's "combine both": three independent supports for
**AIR + sumcheck hybrid**, none conclusive.

[stated] Formal verification is aspirational: *"we're **trying** to…
generate the mathematical proof that our solution is also implemented
correctly."* The tense is the evidence. (The Avigad formalization covers the
CASM core of S-two, not their product, and stops before FRI.)

## The argument of theirs we can make better

[stated] Their anti-TEE case: *"nvidia themselves have access to just fake
those kind of verifiability proofs… if china needs to verify the us they will
never trust nvidia signing only true things."* Correct, well-chosen — and it
argues for OPEN verification even more strongly than for their closed
verifier, since "trust our proprietary verifier" reproduces the same shape
one level up. Ours would be publicly checkable end to end.

## Standing unknowns

Soundness regime unpinned (needs a shipped verifier or proof file — query
count is readable off one). Prover architecture: hybrid best-supported,
unconfirmed. Quantization pipeline: int8 per their blog, details unknown.
