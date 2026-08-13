# The audit theorem: formal statement (the Lean spec)

2026-08-13. Final form after the 2026/541 + beacon-grinding lane. This is the
statement the Lean development proves. Claims-survival verdict and the
ε_beacon derivation are below it.

## Setting

Rounds t = 1, 2, …. Each round the prover posts to an append-only ledger a
commitment `c_t = Com(τ_t; r_t)` to an execution trace and a claimed output.
Round t is **corrupt** (`V_t = 1`) if τ_t does not satisfy the relation R:
`y_t = F(W, x_t, s_t)` for registry-committed weights W and a generation seed
s_t fixed before generation. After c_t is fixed, a beacon emits ρ_t; audit
fires per public rule `Sel` with nominal rate p. Audited rounds run a
**checker** with error ε_chk; alarms on rejection.

The checker is an abstraction 2026/541 forces: instantiate ε_chk as ε_snd
(cryptographic argument — falls with a security parameter) or as ε_tst+ε_sep
(their statistical trace test — an ML distributional assumption that does
NOT fall with a parameter). The statement must not privilege either.

- `ε_bind` — commitment binding, **priced as a term, never folded into negl**.
- `ε_beacon := max_t ( p − ess inf Pr[Sel(ρ_t,t)=1 | F_{t−1}, c_t] )`,
  quantified over the option set **as it stands at beacon-emission time**,
  not commitment time (the Gaži et al. cutoff lesson: later events can
  retroactively promote candidates; closing the set early under-counts).

## Per-round detection lemma

If `V_t = 1` then, for every history,
`Pr[alarm at t | F_{t−1}] ≥ q := p(1 − ε_chk) − ε_bind − ε_beacon`.

**ε_beacon instantiation.** For a grindable beacon with option-count G after
c_t is fixed: `ε_beacon ≤ p · Pr[G ≥ 2]`. For a longest-chain beacon with
adversarial stake α: `Pr[G ≥ 2] = α`, so **ε_beacon ≤ α·p** — the beacon
multiplies the audit rate by (1−α). Ethereum with forking at α=0.30:
Pr[G≥2] = 0.382 (from the 2025/037 MDP epoch split). A datacenter-local
PRNG: G unbounded, q ≤ 0 — vacuous at any audit rate.

⚠ **Min-entropy is the wrong interface.** H∞ bounds the mass of a point —
an UPPER bound on selection probabilities — and a distribution with high
H∞ can put zero mass on the audit set. The figure of merit for an audit
beacon is **Pr[G ≥ 2]**, and min-entropy ranks beacons backwards (one bit
of grinding available 90% of the time beats thirty bits at 2^-40, yet H∞
prefers the former).

## Main theorem (fully adaptive sequential bound)

With per-round payload cap b, first alarm τ, corrupt count C, leakage Λ:
`M_t := q·C_{t∧τ} − 1{τ ≤ t}` is a supermartingale; optional stopping gives

  **E[C_τ] ≤ 1/q,  E[Λ] ≤ b/q**

for ANY F_{t−1}-measurable cheating rule — the adversary sees all past
beacons and verdicts, no independence, no fixed rate, no binomial. (This
replaces Rinberg App C.2's oblivious inverse-binomial.)

**Corollary (false positives).** Under honest-alarm rate α_fp and alarm
budget B_A over horizon M: the bound holds iff α_fp·M ≤ B_A; past that,
B_A — not p — binds.

## Matching lower bounds (what makes the hypotheses load-bearing)

1. **Tightness**: E[C_τ] = 1/q attainable; constant not improvable.
2. **Temporal burst**: L bits in one message exfiltrate with prob ≥ 1−q; no
   capacity-independent bound exists, so b is a hypothesis, not decoration.
3. **Spatial burst (new, from 2026/541)**: a single-path trace check on
   width-N layers has ε_chk ≥ 1 − 1/N, so q ≤ p/N − ε_bind − ε_beacon.
   **Temporal and spatial concentration multiply**; nobody has composed them.

**Floor (HLvA)**: ε_chk > 0 unconditionally if OWFs exist. The theorem is a
RATE bound with a named residual channel, never "leakage is negligible."

## Where 2025/358 sits

`Cost(round) = Q_ledger + p·Cost(Chk)`. Our theorem prices the second term;
Boyle–Komargodski–Vafa prove the FIRST does not fall under the covert
relaxation: soundness error up to 1/3 still costs Ω(log n / log log n)
physical accesses per logical op (their "covert" = constant soundness
error, NOT Aumann–Lindell's simulation notion — cite accordingly).
**"Sampling makes the ledger cheap" is provably false: sampling amortizes
the checker; the ledger is paid in full every round.** Boundary: read-only
reads, secret local state, w_ℓ=1, sublinear verifier storage — an
append-only log never read back with integrity is outside the bound.

## Claims survival (post-2026/541)

1. **q-composition: NARROWED.** 2026/541 composes ε_tst + ε_sep + negl —
   so "everyone assumes rate = detection" is struck. The true claim: three
   legs exist separately (541: checker; 541 Thm 2: binding-as-negl; Gaži:
   grinding, in a beacon paper that never met an audit), and the two
   closest works each assume another leg away (541: trusted uniform
   challenge, FS flagged open citing Campanelli–Datta 2024/1645; Rinberg:
   "private and non-manipulable" as a stated assumption). Nobody composes.
2. **Machine-checking: SURVIVES, reframed.** Two legs already exist in
   Loom: `lightClientSound` (ε_chk leg, bound attained) and
   `lightClientGrinding_sound` (an ε_beacon leg in the ROM/FS model, with
   the try-count factor exhibited as necessary). ε_bind is named open
   (`[ACC-extract]`). **But "a refactor, not a campaign" was too strong**:
   the sequential composition, stopping time, and ε_bind are new work; the
   existing theorems are cited lemmas, not the theorem.
3. **Adaptive sequential bound: SURVIVES VERBATIM** — three independent
   confirmations of absence (Rinberg oblivious; 541 single-shot; 2608.09055
   stationary-rate with its supermartingale on the wrong object).
4. **Burst hypothesis: NARROWED + gains the spatial dimension.**

## Reading pointers earned

Campanelli–Datta, "Fiat-Shamir goes rational" (2024/1645) — FS for
protocols with non-negligible soundness error; our ε_beacon transport and
541's own named open problem. 2026/541's refereed-delegation appendix
(Thm 3) for the two-server variant.
