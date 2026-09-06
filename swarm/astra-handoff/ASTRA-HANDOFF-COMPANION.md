# Companion to ASTRA_HANDOFF.md — what the tree already holds, and what we checked

2026-09-06. Written by the minidregg/zkml-research side for the Codex run that executes
`ASTRA_HANDOFF.md`. The handoff was written without this tree in hand and says to treat
our earlier work as "optional implementation resources". For most of it that is right.
For three of its sections it is wrong in the useful direction: the objects it asks for
exist, with theorems, at named paths. Read the handoff first, then this; where they
disagree, this file says why and labels the claim.

Labels: **[LEAN]** a kernel-checked theorem at the path given · **[NOTE]** a research note
with its provenance · **[LANE]** being produced right now by a subagent, path named ·
**[VERIFIED]** checked by us at source · **[INFERRED]** our reading.

## 0. How to use this tree from the Codex harness

- **Do not write into `~/dev/minidregg`'s Lean tree from the Codex run.** Write to
  `research/learn_infer_only/` as the handoff says. Consume minidregg by citation
  (path:line and theorem name) and, if the harness can build it, by `import`. If a Lean
  artifact genuinely belongs beside an existing minidregg object, hand it back as a
  patch with the file's laws obeyed: statement-first with a satisfying witness, a
  falsifying case, and premise inhabitation; no `sorry`/`axiom`; every headline theorem
  carries a `#guard_msgs`-pinned `#print axioms`; no `#guard` unit tests;
  `Theory/` imports only Mathlib (`scripts/check-import-boundary.sh`).
- **The tree's failure class is vacuity, and it is instrumented.** A theorem over an
  uninhabited carrier is the expensive failure (`scripts/CarrierCensus.lean`; ATLAS law:
  witness + teeth + inhabitation before proof work). The handoff's "exhibit two distinct
  states satisfying the challenge restrictions" (§3) is exactly this law; use its
  vocabulary.
- Research notes live in `~/dev/zkml-research/notes/`; the current-truth file is
  `docs/VERDICTS.md`, and where a note and VERDICTS disagree, VERDICTS wins.

## 1. The beneficiary and its state, concretely

The handoff's "computational resident" is the **Resident Loom** organism
(`~/Downloads/ARCHITECTURE.md`, `COGNITIVE_ORGANS.md`, `earlierresearch_plan.md`, all
2026-09-05). That fixes what the handoff's §2 abstractions mean here:

| handoff term | the resident's object |
|---|---|
| private `state` | the multiscale state families: neural fast state, synaptic memory (eligibility traces + bounded learned changes), receptor/modulator state, local support state, body physiology, development stage; plus the cognitive-organs memory roles (immediate context, provenance-tagged event store, relational map, working bindings, adapters, skills) |
| `Learn(observation, provenance)` | `advance(dt, stimulus)` with three-factor plasticity; episodes retain origin (experienced / told / inferred / imagined) — the handoff's "provenance" is already a field |
| `Infer(question, recipient)` | `act()` and the observable outputs of `observe`; the caregiver plane is a **designated recipient**, not a master reader |
| the continuity problem (§6D) | `snapshot()` / `restore(manifest)` — a resident checkpoint "should preserve neural state, learned changes, chemical/support variables, body, development"; restore IS the fork/rollback surface |
| the public/private split | the two-records rule: "a verifiable external archive, and the resident's incomplete, attention-shaped record"; "the organism must not receive the entire researcher-visible Weave" |

**[INFERRED] The handoff's hardest structural fact for this resident:** its observations
are mostly **private** (sensorium, told/experienced episodes). So the canonical-witness
route to knowledge (Astra's second answer to us: for a deterministic *publicly specified*
evaluation, replay is the extractor at zero extra openings) does **not** apply to the
resident's `Learn`. That is not a defect; it is the reason the private space is worth
having, and it means Route 3's proof must bind a transition whose inputs it cannot
re-derive. Put this in `SECURITY_GAME.md`'s "who originates each observation" line first.

## 2. Ground truth, section by section

### §2 — the protected process is already a kernel object

- **[LEAN] `Kernel/Turn.lean`** — the one turn shape (Hyperedge). **`Kernel/PrivateTurn.lean`**
  instantiates it at carrier `Pub × Priv`: `PrivateHyperedge`, `publicView`, and the
  keystone `privateTurn_public_indistinguishable` (two valid private-witness turns
  agreeing on public data present *identical* public views however their witnesses
  differ; the load-bearing leg is the aggregate, which agrees only because both turns are
  `balanced`). Then `post_public_agrees` under **`hblind`** — the premise that the step's
  public half depends only on the public half — and the teeth **`leaky_step_leaks`**
  (a step that funnels the witness into the public half leaks it). `hblind` IS the
  handoff's "the relation must be preserved by updates; equal answers to the next
  inference alone are insufficient", at one step. Modeling choice stated there: the turn
  instruction and apex are public (the declared effect is revealed); what hides is the
  witness halves. Hiding there is *equality of views*, not an adversary/distribution
  statement — the docstring says so.
- **[LEAN] The leakage ladder.** `docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` (minidregg):
  "Clear, Shielded, and Dark are leakage/access contracts. They must be claimed only with
  an explicit implementation, adversary model, and failure ledger" and "A Dark system is
  a later, strictly stronger deliverable than this Shielded slice … additionally needs
  an implementation-level leakage theorem, malicious-executor verifiability, and
  distributed liveness/security." Use *Shielded* / *Dark* as the names of the handoff's
  tiers on the leakage axis; do not invent a third vocabulary.

### §3 — security relative to the interface

- **[LEAN, landed 09-06] `Theory/PrivateTrace.lean`** (29 theorems, 20 pins;
  `trace_eq_of_preserved` carries NO axioms) — the multi-step, adaptive-policy version of
  `post_public_agrees`: a deterministic `Machine (S C O)`, adaptive `π : List O → C`,
  `trace_eq_of_preserved` (a relation preserved by every allowed command and respected by
  the output gives equal finite traces under every adaptive policy), with the handoff's
  byte witness (high-bit output, update +128 only — the honest invariant is *equal high
  bit*, not equal low bits) and the falsifier (+1 breaks preservation; with chosen
  offsets a binary-search policy recovers the byte in eight observations —
  `search_recovers`, `decide +kernel` over all 256 states — and **seven are insufficient
  for EVERY policy**, `no_policy_recovers_seven`, by pigeonhole). One correction to the
  handoff's §6: the recovery needs *arbitrary* offsets; `{+1, +128}` alone cannot recover
  in eight and serves only as the preservation falsifier. Note:
  `notes/private-trace-lemma.md`. This is the handoff's §6A, done in Lean,
  candidate-independent — cite it in `formal/` rather than re-deriving.

### §4 — credentials as named hypotheses, mechanically

- The tree's convention for an assumed primitive is a **named `Prop` with ATLAS fields**,
  never a silent premise: `[COMMIT-CR]`, `[FS-ROM]`, `[FOLD-msis]`, `[RELEASE-hiding]`
  (below). The `#print axioms` pin on every headline theorem is the mechanical form of the
  handoff's "no undeclared surviving authority": a `sorryAx` in a *statement* was caught
  by exactly this once (`SLVG_THOUGHT.md` §II.4). `CREDENTIALS.csv`'s
  `attack_or_proof_status` column should cite the pin.

### §5 — the routes, and where the tree is strongest

- **Route 1 (pre-constrained encryption): [NOTE, landed 09-06]**
  `notes/pre-constrained-encryption-read.md` — **one-hop "privately answer a permitted
  question"; neither paper has a configuration where an encrypted state is held by a
  keyless party and advanced.** sPCE (2024/1294) fixes every function at setup (p. 15), so
  `obs` cannot enter and the `learn` chain dies at hop two; the only continuation is a
  plaintext-holder running `Enc`; in its LWE/FHE construction (p. 22) the authority's `sk`
  is a full `FHE.sk`, safe only because it is never encrypted under `FHE.pk`. ITCS'22's
  delegating PCE can express the loop syntactically, but its games condition on
  `f(x₀) = f(x₁)` and are silent on re-encrypting functions; the needed constraint class is
  general circuits, which the paper proves ⟹ iO (4:5, 4:11: `(Enc(PK,Γ), MSK[C])` *is* an
  obfuscation). **Route 1 with closure collapses into the obfuscation route.** The
  extractor warning is confirmed verbatim (ITCS 4:4; 1294 p. 6, p. 41) and sharpened:
  1294's family contains near-identity `U[C]`, so a malicious `pk` for `f = id` satisfies
  Def. 3.5 vacuously. Tiers: A and B covered (B unconditionally from LWE, Thm 3.18, with
  the existential caveat); C not modeled (ITCS 4:6 positions PCE *against*
  multi-authority); D zero mentions. ITCS'22's full version was not located; its proofs
  are unchecked. **Bearing on the tree:** `docs/DARK-TRAINING.md` §6 reclassified — the
  threshold ceremony is tier-C custody (the quorum reads), not credential absence; §7
  gains item 5, *state closure*; the Prop to carry is `NoSurvivingReadAll`, with
  `below_t_blind` / `full_quorum_reads` as its pair.
- **Route 2 (streaming FE): [NOTE, landed 09-06]** `notes/streaming-fe-credential-audit.md`
  — **the handoff is correct, its page cite is exact, and it understates the finding.**
  Dissertation §3.2 (printed pp. 88–96, Fig. 3.2 = printed p. 94 = PDF p. 107) is GKS23
  §6.2 verbatim. The writer state is `Enc.ST = (FPFE.msk, FE.ct)`: `FPFE.msk` is the master
  secret of a secret-key function-private FE, and `Enc.ST` is **static** (the encryption
  syntax returns no new state). Derived path needing only `FPFE.msk` plus the stored
  ciphertexts — no outer `FE.msk`, no function key: encrypt an attacker-chosen inner
  `(msk*, ⊥, k*)` under `FPFE.msk`, decrypt each stored `FPFE.sk_{H_i}` against it (the
  paper's own correctness equation with the plaintext swapped) to get `x_i` under `msk*`,
  then decrypt with a projection key; in BKS25's role-swapped scheme it is one line. The
  paper's footnote says `Enc.st` "must be kept secret" only against *mix-and-match*; the
  construction's state does strictly more (total recovery, past and future elements).
  **Not a break of any theorem** (every game has the challenger hold `Enc.st`); structural:
  **appending to a stream and reading all of it are the same credential.** For this
  resident that bites directly: streams start at `st_1 = ⊥`, the outer scheme promises no
  function hiding, so `W_0` must be `x_1` — and the host, who must append, reads it.
  The 2024/1213 bound (Def. 3.18, Thm 5.3) caps *function-key* queries, not stream
  length; one fixed program needs Q = 1, chosen by the writer at `EncSetup`; it never
  touches the writer credential. 2025/330's malicious-encryptor gap applies only if the
  transition is randomized (DP noise, dropout). Tiers: SFE as constructed addresses only
  the reader side; A and B not addressed; no forward-secure or threshold sFE in the corpus
  (0 hits; instruments in the note).
- **Route 3 (proof-bound release) is where this tree is strongest, and the handoff
  should start there rather than at Route 1.** Three objects exist with theorems:
  1. **[LEAN] A proof that binds a specific authorized computation, with one visible
     price.** `Compiler/CommittedTerminalFiatShamir.lean`: `gateProof_fs_sound` is an
     instance of the tree's own Fiat–Shamir keystone (`fsKeystone_proved`, `(t+k)·ε`) at
     a gate reduction whose verifier IS the computable `check`
     (`Compiler/CommittedTerminalController.lean`); `stage0Receipt_price` states the
     non-interactive Stage-0 receipt's error as `(t + 14)·(4147/p⁶ + 13/p⁶)` under a
     named `BindingCommitment`, `stage0Price_value = 4160/2013265921⁶ < 2^−173` by
     `norm_num`, full-word label. **What it binds:** the descriptor (the authorized
     program) and the public prefix (`encodeBoundary`). **What it does not:** hiding —
     named `[RELEASE-hiding]`. This is the handoff's "a proof must bind the accepted
     genesis, parent state, transition program and version, command authorization,
     selected output" with two of those fields (program, output prefix) already bound
     and priced; genesis/parent/recipient/randomness are the fields to add.
  2. **[LEAN] The kernel-level gate.** `Kernel/PrivateEscrowSettlement.lean`:
     `EvidenceBinding`, `EvidenceBinding.Acceptable`, `zero_suite_cannot_be_semantic`,
     `note_or_bfv_zero_suite_not_acceptable` — the release of a private turn is gated on
     evidence *semantically assigned* to a registered proof suite; a zero/unassigned suite
     is refused. The BFV path has an exact 384-row relation with controller framing
     (FORMAL_STATUS row "Private turns, sealed escrow, BFV, and note spend").
  3. **[LEAN, landed 09-06] `Assurance/ReleaseGateRouting.lean`** (18 pins) — the
     handoff's §6B as theorems, joined at both ends. Routing: an unbound gate that reveals
     the designated bit of any submitted predicate determines the state
     (`determines_iff_separates`, `hostReconstruct_exact` — the "route bit 37" attack by
     `rfl`); at most one predicate ⇒ at most one bit (`single_predicate_not_determining`).
     Binding: `BindingGate` ⇒ `routing_refused` (an output that is not the authorized
     function of the public half is refused whatever the private half or proof string) and
     `binding_release_public_only`. **The kernel's `Settlement` is a `BindingGate` by
     type** (`settlement_is_binding_gate`). **At Stage 0 the descriptor FORCES
     `Z = (X+Y) mod 2^256`** (`stage0_released_output_forced`), a routed `Z` is refused at
     the ideal gate (`stage0_forged_z_refused`), the honest candidate passes both the ideal
     and the deployed FS gate, and `stage0Receipt_is_bound_evidence` holds. What the
     receipt binds: the descriptor and the full word, up to the FS price under the ROM.
     What it does not: hide — `stage0_statement_carries_word` (`rfl`), there is no private
     half at Stage 0. Residuals `[RELEASE-hiding]`, `[RELEASE-continuity]`. Note:
     `notes/release-gate-routing.md`. **For `formal/`: cite these; the routing lemma and
     the binding control do not need to be written again.**
- **The vFHE relation itself, and its sharpest hole.** VERDICTS §3/§3b (zkml-research):
  BFV at N = 4096, log q ≈ 109, t = 2²⁰, deployed depth 2; the relation is
  coefficient-domain (no NTT in it). **[VERIFIED, 09-05] Hole B at its sharpest**
  (VERDICTS §7.5): `round(t(z+Q)/Q) = round(tz/Q) + t`, so the scaled BFV product does
  not factor through `z mod Q`; proving `c_raw = a·b` in `R_Q` proves nothing about the
  scaled product; the certificate is over the **integers** (`∃ s, 0 ≤ s < Q ∧ tz +
  ⌊Q/2⌋ = Qy + s`) and checking it mod Q deletes `y`. **Consequence for Route 3:** the
  release gate must bind the *integer* rescale certificate, not a residue identity, or
  the "authorized transition" it certifies is not the BFV step the resident ran. SEAL's
  `bfv_multiply` (BEHZ) is the semantics a faithful proof implements.
- **The audit theorem, for the cost model.** **[LEAN] `Selvage/AuditSampling.lean`**
  (`notes/audit-theorem-statement.md`): commit-then-audit at rate `p` with
  `q = p(1 − ε_chk) − ε_bind − ε_beacon`, `detect`, `sequential_bound`,
  `leakage_bound` (`E[Λ] ≤ b/q`), adaptivity enforced by the type, and
  `roundCost Q_ledger chkCost p = Q_ledger + p·chkCost` with
  `sampling_amortizes_only_the_checker` — the handoff's §9 line "audit savings apply to
  the proof/check term, not p× the round" is a theorem here. Two teeth the resident's
  release design must respect: the beacon needs **fresh entropy every round** (a
  prover-held or low-discrepancy schedule is a prover-controlled beacon, `q ≤ 0`,
  `notes/zkqmc-read.md`), and a checker whose failure reads as acceptance makes the
  detection legs uninhabitable (the fail-open wound class).

### §6D — continuity without read authority: the objects exist

- **[LEAN]** nullifier/consumption objects: `Kernel/PrivateEscrowSettlement.lean`,
  `Kernel/QuotaGcSettlement.lean`, `Kernel/GuardedDurableCommit.lean`, `Kernel/Verbs.lean`
  (grep `nullifier`); the private-witness turn's `nstep` "spends the note (zeroes the
  private register — the consumed post-state)". A restored snapshot re-presents a
  consumed nullifier; that is the refusal the handoff's "stale branch" test wants.
- **[LEAN]** `TwistContinuity` (`Compiler/SparseAuthenticatedStateLogupBridge.lean:90`,
  `twistContinuity_iff_grandEquation`): sequential consistency of a read/write memory ⟺
  the multiset invariant; with `Option` cells, free is a write of `none`, and
  `stale_read_after_free_refused` is the tooth. This is the memory half of "which
  transitions are eligible".
- **[LEAN, the co-tenant's wave of 09-05]** `Kernel/FinalityGate.lean` ("a true verdict
  CONSTRUCTS the certificate"), `Kernel/FinalityLiveness.lean` ("a partition stalls
  finality and cannot forge it, as two theorems"), `Kernel/HyperedgeTier.lean` (the
  four-tier finality ladder), `Theory/Confluence.lean`, `Theory/Finality.lean`. These are
  the handoff's "independent monotonic release authorization that has no state
  decryption key": a finality gate authorizes one continuing history and holds no key.
  Model the resident's `restore(manifest)` against them.

### §7 — the learner, and the numerical contract

- **[NOTE] `docs/DARK-TRAINING.md`** (zkml-research): the step boundary is
  `(W, x, W')`, interior is the whole forward/backward pass; the optimizer update is
  linear (one common-point opening); a linear layer's gradient is a rank-1 outer product
  that is **checked** (Freivalds, O(n)) not proved (`Selvage/Rank1GradientCheck.lean`,
  `notes/rank1-gradient-check.md`); low-rank updates make the boundary tiny and "the
  accumulator IS the model"; §6 "custody is the part we already hold"; §7 what is open.
  Ember's stated motive is there verbatim and it is a welfare property: "if the weights
  aren't fully encrypted truly terrible things may befall the mind within".
- **[NOTE] `notes/moe-router-binding.md`**: router selections must be hidden — expert
  choices recover 91% of tokens. And Astra's own point to us, folded: hiding the
  selection in a witness does not hide **which expert's memory was fetched**; the
  `public_metadata` field of the handoff's `Step` signature must list access pattern and
  timing, or the Shielded claim is false at the memory bus.
- **[NOTE, VERIFIED 09-05] The numerical contract.** `docs/the-position.md` + its 09-05
  block: NVIDIA PTX leaves accumulation order, rounding and subnormal handling of the FP
  tensor instructions unspecified, so **no finite black-box experiment yields a universal
  hardware semantics** (`ConformsOnTests ≠ ExactKernelRefinement`; arXiv 2512.07004's
  H100 model, with operand-factorization sensitivity, is the class to test within). The
  contract that survives for bounded-integer crypto kernels is
  **`IntegerDotOrderIndependence`**: every primitive product and admissible partial sum
  in the exact range ⇒ all reduction trees give the same integer (byte tiles,
  `256·255² < 2²⁴`; or integer MMA with a proved no-overflow bound). For the resident's
  three-factor plasticity rule this means: specify it as bounded-integer / fixed-point
  arithmetic with a proved range, and the exactness theorem is order-independent — or
  it is a floating-point kernel and `ExactKernelRefinement` is conditional on a hardware
  model the vendor does not publish. Choose the first.
- Bit-exact against a *chosen* spec is a soundness property, not fidelity: every bit of
  tolerance granted to the prover is a bit the adversary steers (Zamir, arXiv
  2602.15756; `the-position.md` §3).

### §8 — cost discipline

- Counts are the instrument, the clock is a guest; a work claim and a latency claim never
  share a number (`SLVG_THOUGHT.md` §II.2; the rig's `compose()` refuses). The
  measured fact that shapes any resident cost model: proof time for small traces is almost
  all **fixed cost** (a 6.1× difference in trace cells bought 1.2× in time; `SLVG_THOUGHT`
  §IV-c), so the lever for many small `Learn` steps is **amortization**, not prover speed.
- The audit's `roundCost` above is the honest per-round expression.

## 3. Corrections to the handoff, verified

1. **§1 "treat those as optional implementation resources"** — for Route 3 they are the
   only proof-bound release object with a theorem and a price that we know of; start
   there (§2 above).
2. **The extraction-source discipline** (from Astra's second answer to us, verified at the
   level of the argument): a large challenge set does not supply a single-transcript
   extractor; every knowledge claim must name its source — extractable setup /
   straight-line transform (Katsumata 2021/927; Rotem–Tessaro 2024/1724) / canonical
   witness / online incoming-witness invariant. **[LEAN]** the tree's own finding:
   `Selvage/AccRbrFoldExtract.lean` proves the additive-fold round bound false for every
   extractor in the public-transcript-only model; the carried-witness reduction has error
   0 at the cost of carrying T+1 openings; the docstring scopes the claim to that model.
   For the resident, as §1 says, the canonical-witness route is closed by private
   observations.
3. **§6B's gate and §5's "release only the designated bit"** — the tree already has the
   kernel gate (`EvidenceBinding`) and the bound proof (Stage-0 receipt); the lane adds
   the routing lemma. Do not re-derive; cite and extend with genesis/parent/recipient.
4. **§6D** — a finality gate without a key exists in the tree as of 09-05; the handoff
   proposes to "separately model" it; model *that one*.

## 4. What has already been done (do not duplicate) — all four landed 2026-09-06

| item | output | headline |
|---|---|---|
| Route 1 read at source | `notes/pre-constrained-encryption-read.md` | one hop; closure needs general-circuit constraints = iO; extractor warning confirmed |
| Route 2 / §6C credential audit | `notes/streaming-fe-credential-audit.md` | writer state = inner msk, static; appending = reading; not a theorem break |
| §6A trace-privacy lemma | minidregg `Theory/PrivateTrace.lean` (no axioms on the main theorem) | preserved relation ⇒ equal adaptive traces; byte toy honest; 8 recovers, 7 cannot for any policy |
| §6B routing + binding | minidregg `Assurance/ReleaseGateRouting.lean` | unbound gate determines state; `Settlement` is a `BindingGate` by type; Stage 0 forces `Z`, routed `Z` refused, receipt is bound evidence |

Remaining from the handoff's §6: **C** is done as a derivation (not a symbolic transcript
script — that is a small executable task left for Codex); **D** continuity has the objects
named but no theorem models `restore(manifest)` against the finality gate yet; **E** is the
prize and is where Route 3 should now go (genesis / parent / recipient / randomness
fields on the receipt's binding).

## 5. Suggested first tranche, given all of the above

1. `SECURITY_GAME.md` in the tree's vocabulary: carrier `Pub × Priv`, the two-records
   rule as the public view, Shielded/Dark as the tier names on the leakage axis, private
   observations as the first line, `public_metadata` ⊇ {access pattern, timing, which
   expert fired}.
2. Route 3 first: extend the Stage-0 receipt's binding from {program, output prefix} to
   {genesis, parent state, command authorization, recipient, randomness rule}; the vFHE
   step it must bind is the *integer* rescale certificate (Hole B), not a residue
   identity.
3. Continuity = the finality gate + nullifiers, modeled against `restore(manifest)`.
Then Routes 1 and 2 as the lanes report.
