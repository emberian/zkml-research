# Prompt for GPT-6-Astra — the joint algebra problem

Written 2026-09-04 for a model we expect to be stronger than us at this. It is
given the real problem, the real constraints with their provenance, everything we
already priced so it does not re-derive it, and license to reject the framing.
Paste everything below the line.

---

You are being asked a research question by a small group doing basic research in
verifiable computation: machine-checked proof systems (Lean 4), verifiable
computation over encrypted data, and verifiable machine learning, all post-quantum
and hash- or lattice-based, all open. We are not building a product and we do not
need a winner. We need the strongest true statement about a design space, with its
refutations attached. Treat us as colleagues who will check every claim you make,
and who would rather hear "no such object exists, and here is why" than a pitch.

## The question

Four objects currently live in four different algebras, and every seam between
them is paid for in proof cost:

1. the FHE ciphertext ring element (BFV/BGV-style RLWE over Z_q[X]/(X^N+1));
2. the commitment word (a Merkle leaf over a small prime field today; a
   Module-SIS/Ajtai commitment over a ring in our folding design);
3. the proof-system witness word (a small prime field element under an AIR with
   FRI, or under sumcheck/GKR);
4. the ML accumulator (block-floating-point: shared-exponent integer sums in a
   ~26-bit window, bf16-class unary ops as 2^16-entry tables).

Find an algebraic substrate, or a small tower of substrates with explicit and
priced connectors, on which these four objects coincide or align, such that a
single sound, post-quantum, machine-checkable proof system can (a) prove FHE
ciphertext operations natively, (b) fold/accumulate (IVC) without a Merkle
re-verification per step, (c) prove ML inference and training steps at native
integer/block-float semantics with zero model modification, and (d) be
zero-knowledge where the workload requires it. If no single substrate can do
this, say so with the obstruction named precisely, and characterize the Pareto
frontier of towers instead.

## Hard constraints, with provenance

- **FHE.** BFV, N = 4096, log q ≈ 109 (three RNS limbs) at the deployed point;
  a single 61-bit joint prime wins on both sides but costs one multiplicative
  depth level, and whether it survives a 2.4-bit noise margin is open. A single
  ~109-bit joint prime is measured a net loss (1.2–2.2× worse FHE, 1.1–1.5×
  worse proving). Deployed depth is 2; plaintext modulus t = 2^20, which binds
  any BFV polynomial nonlinearity to degree ≤ 2, so nonlinearities cross an
  MPC or PBS boundary. The Zama HPU's ring is Z/2^64. We do not yet know whether
  we control the FHE modulus in deployment; assume we do and also say what
  changes if we do not.
- **Proof system, deployed.** BabyBear p = 2^31 − 2^27 + 1, Poseidon2 width 16
  α = 7 R_F = 8 R_P = 13, FRI at log-blowup 6, Ext4 challenges. Honest soundness
  of the query column: 34 bits in the unique-decoding regime, 73 in the Johnson
  regime; the capacity-regime 130 is withdrawn and never quoted. Hash-bound at
  5–7× at every feasible blowup. Proof time for small traces is almost all
  fixed cost, so the lever is amortization, not prover speed.
- **Hash choice is pinned by recursion, in both characteristics.** In-circuit
  Poseidon2 beats Blake3/Keccak by 30–210×; natively it loses 5.8×; recursion
  cost is verifier cost, and binary-field systems converge on proving but stay
  12–25× apart on verification (eprint 2025/1893). So any algebra you propose
  must carry a hash whose verification relation is cheap in that algebra and
  expensive in the adversary's (Gröbner/FreeLunch-modelable relations are the
  attack surface; the structure that makes a question decidable is the
  structure an attacker reads).
- **Folding.** Hash commitments do not fold: measured ordering DL fold 1× <
  PQ lattice fold 4–50× < Merkle wrap ~10^3×. Our candidate is a dual-mode ring
  object over R_q, q = 2^64 − 257, X^N+1 splitting into τ = 2 factors, norm
  bound B = 2^16: an Ajtai/MSIS commitment in linear mode and a Fiat–Shamir
  hash in full mode, one parameter set. Additive-commitment folding is proved
  safe through T = 2^47 − 2 fold steps and loses binding unconditionally at
  2^47 − 1. Sponge indifferentiability of the full mode is the one unproved
  wall. Pay-per-bit lattice folding (Neo) is structurally incompatible with
  characteristic 2: lattice norms do not exist there.
- **Sumcheck over a product ring** Z_Q = F_{q0} × F_{q1} × F_{q2} works with
  challenges from a sampling set A of pairwise-invertible differences, soundness
  v·d/|A|, and |A| ≤ min q_i ≈ 2^36 is a theorem-level ceiling; a shared
  degree-4 ring extension clears a 124-bit bar. Cross-limb binding is two holes:
  provenance (a quantifier swap; closed for free by row-interleaving) and
  expressibility (⌊t·x/Q⌉ reads the CRT reconstruction; no per-limb equation
  exists; proved impossible for any Z_Q polynomial).
- **ML.** Unmodified models, zero loss. Bit-exact against block floating point
  with an exact accumulator, matching what tensor cores physically do; the
  26-bit window fits one BabyBear element. Approximate/error-tolerant proving
  is rejected: the best float system loses to quantized by ~12× (Spain, OSDI'26,
  its own Figure 4), and generic layerwise tolerance is provably exploitable by
  the party you are proving against (Zamir, arXiv 2602.15756). Every bit of
  tolerance granted to the prover is a bit the adversary steers. Target scale
  is a 2.4T-parameter MoE with sparse activation; router selections must be
  hidden (expert choices recover 91% of tokens).
- **Audit, not proof, where possible.** A machine-checked commit-then-audit
  theorem gives expected leakage ≤ b/q at audit rate p with
  q = p(1 − ε_chk) − ε_bind − ε_beacon; it converts any prover into a deployable
  one at ~20× system-level. Its beacon term needs fresh entropy each round: a
  prover-held or low-discrepancy schedule is a prover-controlled beacon (q ≤ 0),
  and a warden-secret Kronecker shift is learned from ≈ ℓ/log2(1/p) observed
  audits.
- **Formal.** Our proof-system layer is a bag of Lean 4 ingredients, sorry-free:
  RBR→Fiat–Shamir compiler (t+k)·ε, BCS transform at the deployed alphabet,
  additive BaseFold, ring switching, accumulation depth (including a
  machine-checked corner case where the published theorem fails), sponge
  indifferentiability, the audit theorem. 13 of 18 keystones are field-agnostic.
  Anything you propose should name the Prop it would need us to prove first,
  with a satisfying witness and a falsifying case (we refuse theorems over
  uninhabited carriers).

## Already priced — do not re-derive, do disagree if you can

- BabyBear + KoalaBear limbs, zero-emulation vFHE: overhead 1.00× per limb,
  binding via Z_Q sumcheck, rescale routed through a basis witness.
- 61-bit joint prime: wins both sides, costs one level, margin open.
- Binary towers + additive BaseFold + ring switching: landed; no lattice norms,
  so no pay-per-bit folding; verification stays expensive under recursion.
- Neo/SuperNeo: unscoreable (no implementation, no verifier constraint count),
  killed at our dual-mode parameters twice.
- Circle STARK over M31 (StarkWare S-two): fastest CPU prover; formalized by
  Avigad's group; not examined by us for FHE alignment.
- Galois rings GR(2^k, d), Z/2^k arithmetic with sumcheck over exceptional sets
  (Rinocchio line), lattice PCS over power-of-two moduli: not examined by us.
- Non-power-of-two cyclotomics (Φ_{3^k} and prime conductors): we hold a
  cyclotomic-inertia theorem; not examined for alignment.

## What we want back

1. **The axis map.** Every axis of the algebra space you consider relevant
   (characteristic; field vs ring vs Galois ring; cyclotomic conductor; splitting
   behaviour of X^N+1 mod q and its effect on challenge spaces and NTT; 2-adicity
   vs circle-group structure; extension towers vs product rings vs Hensel lifts;
   commitment algebra hash vs lattice vs both; where the ML accumulator window
   lands), including axes we did not list.
2. **Three to five syntheses**, each with: the algebra; how each of the four
   objects embeds in it, exactly; every seam that remains and its cost derived
   from the numbers above (show the arithmetic); the soundness leg with its
   regime named (unique-decoding / Johnson / capacity, or the lattice
   assumption with its parameters); the cryptanalytic surface of the hash it
   needs, and whether that surface is decidable (Gröbner-modelable) or argued;
   the zero-knowledge mechanism and its price; the single cheapest experiment
   that would refute it using our tooling (a Lean statement, an exact
   operation-count harness, or a script), and the honest generality label:
   real, cosmetic, or trap.
3. **If no single substrate works, the obstruction as a statement** we could
   try to prove: which two of the four objects cannot share an algebra under
   which constraint, and what relaxation would dissolve it.
4. **The three Lean Props you would want proved first**, statement-level, with
   their satisfying witness and falsifying case sketched.
5. **What we are not asking that we should be.** You are likely to see a
   framing error in this prompt; name it.

## Rules

Label every claim [READ] with an identifier we can check (eprint id, arXiv id,
theorem number), [DERIVED] with the inputs and the arithmetic, or [INFERRED].
A number without provenance does not go in. Quote the pessimistic bound. Prefer
refutation to advocacy: a candidate you kill with a precise reason is worth as
much as one you keep. Distinguish "known to the literature" from "novel" and say
which is which. Do not optimize for being interesting; optimize for being
checkable by people who will run the check.
