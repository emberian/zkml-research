# Field choice vs recursion cost: the evidence, including a measurement that may be the only one

2026-08-13. Delivered by a peer session (relayed agent-message; full extracts
in its scratchpad, papers in ~/paperbin). Tags preserved from the peer:
[stated] = primary source verbatim, [inferred] marked, [could not source]
explicit. This feeds the field-choice memo.

## The meta-finding: NOBODY chose their field for recursion

- SP1 [stated]: BabyBear/KoalaBear justified by "efficient arithmetic" —
  recursion cost attributed to COLUMN COUNT, not field width (Jagged-PCS
  paper). No BabyBear→KoalaBear rationale published anywhere.
- RISC Zero [stated]: BabyBear defined with NO rationale and no
  recursion-cost discussion at all in the proof-system PDF.
- Stwo [stated]: M31 justified purely by field arithmetic; their actual
  design response to 31-bit recursion cost is two dedicated opcodes
  (blake_compress 168 cols, qm_31_add_mul 72 cols) — never framed as a
  field-choice cost [peer's inference, flagged].
- Plonky3 [stated]: UPSTREAM ships zero recursion (895 files, no path
  matches "recurs"); downstreams build their own. ⚠ Ember's correction: OUR
  orbit has `~/dev/plonky3-recursion` (the emberian fork — ~67K lines,
  full in-circuit FRI verifier + Poseidon2-in-circuit AIR), consumed by
  ~30 breadstuffs circuit-prove files with a reimplemented verifier. So
  "no Plonky3 recursion exists" is false for us specifically — we hold one
  of the few working BabyBear recursion stacks, which is itself evidence
  for the field memo: the 31-bit recursion cost is not hypothetical to us,
  it is measured in our own wrap accounting (40.9M → 1.02M R1CS via native
  hashing).

So ember's "we're only using BabyBear because Plonky3 already was" is the
INDUSTRY-WIDE pattern: fields chosen for arithmetic, recursion paid as an
afterthought, nobody wrote the tradeoff down.

## The gap is real and named in print

eprint 2026/1371 §5.5 verbatim: the controlled head-to-head "across
Goldilocks, BabyBear, Mersenne-31, and the binary towers … under matched
security parameters does not exist in the peer-reviewed literature. We flag
this as the sharpest empirical gap in the area." Confirmed against the
25,765-paper mirror. Telos ran BabyBear-only numbers on a harness that
supports the comparison and never published it.

⚠ Citation hazard the peer caught: 2026/1371 attributes the
Goldilocks-for-recursion rationale to the Plonky2 report, WHICH SAYS NO SUCH
THING (field chosen "for speed of computation"; two-adicity unmentioned).
Do not repeat that attribution.

## The measurement (possibly the only one in existence)

Peer ran the goldibear harness (patching its bit-rotted Plonky3 pin):
**Goldilocks recursive_proof ~236 ms vs BabyBear ~489 ms; merge_proofs
457 ms vs 947 ms — both ratios 2.07×** at the configs' self-declared
100-bit conjectured target (blowup 8, 28 queries, pow 16, zk off).

Caveats, the peer's own and correct:
- **Field + hash jointly confounded** (Poseidon-width-12 on GL vs
  Poseidon2-BabyBear) — the 2.07× is not field alone.
- Measures "BabyBear ported into a Goldilocks-shaped recursion system," not
  a best-effort 31-bit recursion design (SP1/RISC Zero native recursion VMs
  unrepresented; D=4 extension, 8 hash-out elements, 6 challenges all
  field-forced).
- One machine (M2 Max), one run, criterion 20 samples. **A data point, not
  the controlled study 2026/1371 calls for.**
- Security equality between the configs was self-declared, not verified.

## The wrap pattern (all three production systems)

Pre-SNARK step is always a HASH-FIELD SWAP (SP1 "shrink" replaces the
Poseidon2 field with a Groth16-compatible one; RISC Zero identity_p254
switches to Poseidon254; Polygon's Final Stage moves the transcript hash to
the bn128 field) — then BN254 Groth16/PLONK. [could not source] anyone
quantifying wrap-cost dependence on the BASE field; the peer marks
31-bit/deg-4 vs 64-bit/deg-2 packing into BN254 as unmeasured either way.

## What this gives the field memo

1. The BabyBear default is not a considered position anywhere in the
   industry — interrogating it is genuinely novel, not remedial.
2. The 2.07× GL-vs-BB recursion data point (with its confounds named) is
   likely the only matched-target cross-field recursion number in
   existence — publishable as part of filling 2026/1371's named gap.
3. Any field decision for Selvage should weigh: recursion cost is dominated
   by hash-in-circuit (the wrap pattern's existence proves everyone treats
   it as swappable), column count (SP1's attribution), and the extension
   degree forced at 31 bits — not raw field arithmetic, which is what every
   vendor optimized for.
