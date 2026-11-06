# Selvage against FlashProve and ArkLib: a critical evaluation (2026-11-05)

Tags: [READ] seen at file:line (by me, or by a helper lane whose transcript reports file:line);
[MEASURED] I ran it; [CLAIM] asserted elsewhere; [INFERRED] my derivation. Method:
refute-then-repair. Each weakness gets a repair or a settling experiment. Codex's adversarial
read is folded in and attributed (`notes/proof-system-codex-synthesis.md` §A); the conclusions
are mine.

Snapshots: minidregg `c4ecabe0f` (2026-10-31); ArkLib HEAD `4d9d67b` (2026-11-05) and
`22dbd4e` (2026-09-04); FlashProve v0.16.0 (2026-11-02); breadstuffs `22fad151e`.

---

## 0. Headline

1. **By the frontier's own standard, our deployed proofs carry 34 bits.** Setty's 2026 systems
   report only provable unique-decoding bits: BinarySpartan (ePrint 2026/1656 §4) gives 100 UD
   bits, no PoW, ≤ 2^-102.6. Magnetar (2026/2423 §6.1) gives "every round … at most 2^-120 …
   only proven proximity gaps … within the unique-decoding radius". FlashProve proves Johnson-
   regime list decoding in Lean. Our deployed IR-v2 `(lb 6, q 19, pow 16)` reads **UDR 34 /
   JBR 73** (`docs/VERDICTS.md` §2), and the Johnson figure rests on an unproved hypothesis in
   our own Lean (§2.2). That gap is the most important fact in this note. It is cheap to close
   on the prover side (§3 W1), because queries cost the prover almost nothing: +5 permutations
   for +38 queries (`notes/blowup-drop.md` §4).
2. **Our record of the comparator is stale, so two strategy documents argue from false
   premises.** `docs/SELVAGE.md` §1: "ArkLib's composition theorems are `sorry`".
   `notes/binaryspartan-position.md` §12.3(c): ArkLib's FRI-Binius "has no soundness statement
   at all" with "33 `sorry`s in the Binius leaves". At ArkLib HEAD [READ, helper census], live
   `sorry` fell **292 → 4** since 09-04 and there are 0 axioms. Proved sorry-free since then:
   sumcheck RBR knowledge soundness, FRI soundness, RBR soundness and knowledge soundness,
   BCIKS20 Thms 1.2/1.4/1.5/1.6 over the open Johnson range, RS mutual correlated agreement up to
   Johnson (BCHKS25 Thm 4.6 via DKT26), and **Binary BaseFold plus ring switching, composed**.
   Sequential composition of RBR knowledge soundness is proved for *guarded* verifiers. Some of
   the drop is deletion (STIR main theorem, duplex-sponge FS), not proof.
3. **The FS/BCS compilation layer is still where Selvage is ahead of both.** ArkLib has no
   IOP→NARG theorem: `OracleReduction/BCS/Basic.lean` is a stub, and `FiatShamir/
   Completeness.lean:748` still says "TODO: state-restoration … soundness implies … soundness
   after Fiat–Shamir". FlashProve has a monolithic end-to-end theorem for one system. Selvage has
   the general RBR→FS compiler over an inhabited lazy oracle (`FiatShamir.lean:512`,
   `Depth.lean:1956`, error `(t+k)ε`). Codex confirmed it is proved, not an axiom. This is the
   piece to keep, harden and upstream.
4. **Toolchains are identical today.** minidregg is on `leanprover/lean4:v4.35.0` with Mathlib
   `56a00585…`, and so is ArkLib HEAD [MEASURED, both `lean-toolchain`s and manifests].
   **Importing ArkLib's MCA theorem to discharge our Johnson hypothesis is a dependency edit, not
   a port.** Remaining risks are VCVio/CompPoly pins and ArkLib's `requiresModuleSystem`.

---

## 1. The three formalizations side by side

| axis | Selvage | ArkLib HEAD | FlashProve |
|---|---|---|---|
| size | 152 files, 0 sorry | 1152 files, 4 live sorry (lower bounds only), 0 axioms | 29,563 files, ~6.0M lines, 0 sorry/axiom/native_decide, ~15.7k `decide` |
| framework | own `Rbr`/`Depth`/`FiatShamir`/`AccRbrBcs`; probabilities as finite uniform sums | VCVio `OracleComp`, `Reduction`/`OracleReduction`, guarded seq-composition | own; Mathlib only; 141 vendored ArkLib-derived files under `lean/ThirdParty/` (AI-adapted from ArkLib `2817d8c7`) |
| sumcheck | `SumcheckRbr`, `QuadraticSumcheck`, cubic rung in `Assurance/` | `oracleVerifier_rbrKnowledgeSoundness` error `deg/|R|` per round (`Sumcheck/Spec/General.lean:513`) | inside the online IOP |
| proximity, UD | `rs_proximityGap_UD_sharp` needs `d < (1−3δ)n`: **one-third band** (`ProximityGapUDSharp.lean:54`) | `rs_mcaError_le_of_le_relUDR`, **full UDR** (`BCIKS20/EpsCa.lean:179`) | not used |
| proximity, Johnson | `JohnsonMcaBridge`: Haböck 2025/2110 Thm 2 as **explicit hypothesis** `hHab`; `WHIRConjecture412` a named hypothesis (`JohnsonRegime.lean:432-507`) | **proved**: `rs_mcaError_le_in_johnson_range` (`CapacityBounds.lean:235`) | proved `Cb.BCHKS46At` from adapted ArkLib; all 341 closeness rounds rest on it |
| FRI | multiplicative FRI (`Proximity.lean`, `HalfThresholdFri*`), additive FRI with real UD bound (`AdditiveFriQuery`) | `Fri/Spec/Soundness.lean:81`, error parametric in worst-case MCA error, numeric via BCGM25 Thm 8.2 (1.5-Johnson) | WHIR/STIR-like code switching (CFW ePrint 2026/391), ZK RS, rate 0.104 |
| WHIR / STIR | CA for WHIR Lemma 4.10 (domain-general, with errata repairs) | STIR components only; **no WHIR protocol** | own |
| BCS / FS | **proved general compiler** + state restoration + BCS at deployed alphabet | **absent** (stub; SR game in interaction layer, no bridge) | proved for its system, in the ROM with a query-count error |
| commitment binding | `PositionBinding` **perfect** (`Commitment.lean:113`), inhabited by the identity root (`:220-228`) | no Merkle in ArkLib (VCVio claims shared-ROM Merkle extraction [CLAIM]) | ROM, birthday term `(t+n+2^23+2)²/2^256` |
| binary fields | additive FRI tower, `AdditiveBaseFold`, `CharTwoWall`; **no ring switching** | Binary BaseFold + ring switching **composed**, sorry-free | none |
| end-to-end | none deployed: **0 of 153 modules reached by the Host** (`ASSURANCE-CENSUS-2026-10-27.md:36`) | none (library) | `sound_of_verify_at` about an executable-equivalent Lean verifier, `q/2^124 + 2^-101` |
| audit / sampling | `AuditSampling.sequential_bound` `E[C] ≤ 1/q`, `leakage_bound` `b/q` | none | none: every request fully proved |
| executes | Rust: degree-1/3 sumcheck, binary tower, additive NTT, MLE kernels (`prover/src`, 5.8k lines); **no PCS, no Merkle, no transcript** | CompPoly computable prover pieces | C++/CUDA prover and verifier (unverified), plus a Lean verifier (24 min, 9-15 GB) |

---

## 2. Stronger, weaker, incomparable

### 2.1 Where Selvage is stronger
- **The compiler.** The general RBR→FS theorem, state restoration, accumulation depth (including
  the machine-checked corner refutation of a published theorem) and BCS at the deployed
  alphabet. Neither comparator has a reusable compiler. ArkLib's absence is explicit
  (`00-current-status.md:435`: "no Fiat–Shamir or BCS bridge from state restoration").
- **Commit-then-audit.** It is unique, and the only formal object that prices *not proving*.
  FlashProve proves every request; its "amortization" is a shared weight opening per batch.
- **Domain-generality.** `ReedSolomon.lean:87` uses an abstract `dom : ι ↪ F`, so 13 of 18
  keystones transfer to char 2 unchanged (`binaryspartan-position.md` §6.1). ArkLib's FRI is
  multiplicative; its binary stack is a separate cone.

### 2.2 Where Selvage is weaker
- **Johnson regime.** Ours is a hypothesis; ArkLib and FlashProve prove it. Our JBR 73 is
  therefore conditional in our own Lean.
- **The UD band.** Ours is `δ < (1−ρ)/3` with `d < (1−3δ)n`. ArkLib has full UDR. Codex §A4:
  our "UD" label outruns the one-third event we actually prove.
- **Binding.** Perfect position binding cannot be inhabited by any compressing scheme
  (pigeonhole). The only inhabitant is the identity commitment. `AccRbrBcs.lean:752` and
  `AdditiveFriQuery.lean:410` consume it. FlashProve carries an explicit ROM birthday term; we
  carry none. Codex §A2.
- **Closure.** FlashProve's theorem reaches a verifier that runs. Ours reach nothing deployed.
- **Ring switching.** ArkLib has it composed; we hold both endpoints and no connector.

### 2.3 Incomparable
- **FlashProve vs Selvage on soundness shape.** FlashProve has concrete accounting for one
  frozen configuration, with vacuity risk outside it (THEOREM.md:312-321: at other in-scope
  files `verify` may reject everything). Its system-of-record has a constant honest side (GAPS
  gap 55). Its exact-match policy is a hypothesis `verify` does not test. Its kernel is
  pre-4.32.1 (LIMITS:2769-2775), and it is AI-authored with no human check (paper l.91-93).
  Selvage is parametric and reusable, with no instance. Neither certifies a native verifier
  (codex §A7).
- **ArkLib vs Selvage frameworks.** VCVio `OracleComp` against finite uniform sums. Importing
  ArkLib *theorems about codes* (pure coding theory: `mcaError`, RS, Johnson) is cheap.
  Importing ArkLib *protocol* theorems means adopting its `Reduction` type, which our compiler
  does not consume.

---

## 3. Weaknesses, each with its repair or settling experiment

**W1. Deployed soundness is 34 UD bits.** [READ VERDICTS §2; corroborated by
`TwoRegimeQueryBudget.lean` §7b per blowup-drop.md]
*Repair:* adopt "provable UD only" as the reporting rule, as Setty does. At `lb=6` (ρ=1/64) a UD
query buys `−log₂((1+ρ)/2) = 0.977` bits, so 100 bits needs 86 queries at pow 16 (VERDICTS) or
103 at pow 0 [INFERRED]. Measured price on the prover: about +5 permutations per +38 queries
(blowup-drop.md §4). On the verifier: about ×4.5 query-phase hashing. In the tower the
verifier's hashes are the wrap's trace (`VERDICTS.md` §4c identity), so the real price is in
the wrap. *Settling experiment (counts, hbox):* re-run `recursion_tower_profile` at `(6, 86, 16)`
and report wrap cells against `(6, 19, 16)`. This is the decision number, and it does not exist
yet. **Also required:** an `ε_C` column at UD over BabyBear⁴. The commit-phase term at a
`2^27`-point domain over a 124-bit field is about `n/|F| ≈ 2^-97` per round [INFERRED]. That may
cap UD at below 100 bits regardless of queries, and Ext5 (`VERDICTS.md` §1) would fix it.

**W2. Johnson MCA is a hypothesis we no longer need to carry.**
*Repair:* import. `require ArkLib` at `4d9d67b` and add `Selvage/ArkLibMcaBridge.lean`. It
proves Selvage's `mutualCAFailure` probability for `(affineGenerator, reedSolomonCode dom d)`
equals or is bounded by ArkLib's `mcaError` at the same code. It then instantiates
`whirConjecture412_rs_of_haboeck`'s consumer with ArkLib's `rs_mcaError_le_in_johnson_range`
instead of `hHab`. *Settling experiment:* `lake build Selvage.ArkLibMcaBridge` on the Mac (one
file plus deps; ArkLib's dependency build should run on hbox under `swarm-build`). *Falsifier
of the bridge:* the bound must be `< 1` at a concrete toy RS code (`ZMod 17`, n=16, d=4), or
the bridge proved a vacuous inequality. **Mismatch risk to check first:** ArkLib's rate
convention `(k−1)/n` vs `k/n`. Our `JohnsonMcaBridge.lean:16-27` already documents the
Haböck/Selvage rounding (`ρ_H = (d−1)/n` vs `ρ_J = d/n`), and ArkLib's
`JohnsonComparison.lean` reconciles `(D+1)/n` with `D/n`.

**W3. The UD band is one-third.** *Repair:* import `rs_mcaError_le_of_le_relUDR` the same way.
This retires `ProximityGapUD*` as the reported UD theorem; keep them as the independent
cross-check.

**W4. Perfect position binding.** *Repair:* replace `BindingCommitment.binding : PositionBinding`
with an advantage-carrying structure (`docs/CERTIFICATES.md` P1). Thread `bindAdv` additively
through `AccRbrBcs` and `AdditiveFriQuery`, the way FlashProve's error carries
`(t+n+2^23+2)²/2^256`. *Falsifier:* the toy compressing scheme of CERTIFICATES P1 must refute
`PositionBinding`. That exhibits why the current field is uninhabitable at any short root.

**W5. Stale ledger text.** `breadstuffs/.../Circuit/FriLedger.lean:270` says "Neither is
public". Both are (2025/2055, 2025/2110; 2026/532). Codex §A5 adds that BCSS25 improves Johnson
exceptional slopes from `O(n²)` to `O(n)`. *Repair:* a second `ε_C` column, not an edit of the
first. Codex's warning is right: do not transplant circle-FRI numbers (2026/532 Thm 19 is for
circle FRI over M31) into classic FRI.

**W6. The CorrelatedAgreement errata repairs: mostly moot, not entirely.**
`CorrelatedAgreement.lean:15-22` repairs WHIR Lemma 4.10 (`max` not `min`, `1−B*`, arbitrary
generator, `herr_mono`). That route goes from CA to MCA. **For RS codes over affine lines and
polynomial generators it is now superseded**: ArkLib proves MCA directly up to Johnson, and
BCGM25 ("All polynomial generators preserve distance with MCA", 2025/2051) covers polynomial
generators. The repairs stay ahead in two places: (a) **non-RS codes** (constrained RS for WHIR,
interleaved and additive codes for Ligerito, where Diamond-Gruen 2024/1351 Thm 3.1 is the
missing object, `binaryspartan-position.md` §12.2 item 3); and (b) **non-polynomial
generators**. *Decision:* keep the file as the general lemma, stop citing it as our Johnson
story, and send the `max`/`1−B*` errata upstream to the WHIR authors and ArkLib (whose
`Folding/ListDecodability.lean` takes MCA of `Gen(2;α)` as a hypothesis, i.e. the same seam).

**W7. "Prover" is the wrong noun.** 0/153 modules are reached. Rust has no PCS, no Merkle and no
transcript (codex §A1: challenges are caller-supplied, `prover/src/sumcheck.rs:31`).
*Repair:* decide F1 (PROGRAM §3) explicitly. Selvage is a **verifier-side composition and
certificate layer** until a PCS executes. Its first deployment target is the audit theorem
instantiated over FlashProve's `Sound` (W8). *Settling experiment:* codex's. Trace one real
acceptance from a Host entry point through transcript, openings and terminal checks, and name
the theorem that covers each function.

**W8. The audit theorem's checker leg is abstract, and its honest parameters are vacuous at the
beacon.** `AuditSampling.lean:882` `grind_honest_q_eq_zero` (honest, but it means the
grindable-beacon instance says nothing), and `:933` (fail-open checking has no positive rate).
*Repair:* instantiate `ε_chk` with FlashProve's `soundnessErrorInQueries t 1`, `ε_beacon` with a
drand/pqvrf model, and `ε_bind` with the Blake3 MMR. *Settling experiment* (codex §A3): let the
producer choose among beacon candidates after a forced checker timeout, and measure the
conditional alarm rate against the definition of corruption.

**W9. Vacuity carriers still read as results.** `Assurance/Tower256AdditiveFri*` bind
`{pcs : MerklePcs ell}`, which `merklePcs_empty_of_positive` proves empty at positive height
(`binaryspartan-position.md` §12.5; `scripts/CarrierCensus.lean` knows). *Repair:* rename or
delete, and make `CarrierCensus` a CI gate rather than a script.

**W10. Strategy docs are wrong about ArkLib.** *Repair:* correct `SELVAGE.md` §1 and
`binaryspartan-position.md` §11.1/§12.3(c) with dated retractions (done below as
recommendations; I did not edit those files in this lane because other agents own them).

---

## 4. Import / mirror / diverge, per component

| component | verdict | reason |
|---|---|---|
| RS MCA, UD and Johnson (coding theory) | **IMPORT** from ArkLib | proved there, unproved here, identical toolchain; pure math with no framework coupling |
| BCIKS20 CA lines/curves/affine spaces | **IMPORT** | same |
| FRI protocol soundness | **MIRROR** (keep ours; cross-check the numeric bound against ArkLib's `Fri/ErrorBounds.lean`) | ArkLib's FRI lives in its `Reduction` framework, which our compiler cannot consume; its numeric bound is 1.5-Johnson, not full Johnson (the full-Johnson MCA is not wired into its FRI) |
| sumcheck RBR | **MIRROR** | ours feeds our compiler; equate error terms in a bridge lemma |
| RBR→FS, BCS, state restoration, depth | **DIVERGE** (ours is ahead), and offer upstream | ArkLib's own status file names this as missing |
| ring switching, Binary BaseFold | **IMPORT** the statements; mirror inside our compiler | the #1 structural gap in our binary cone, proved there |
| commitment binding | **DIVERGE** from both: computational advantage, as FlashProve does it, but generic | neither ArkLib (no Merkle) nor our perfect binding is right |
| end-to-end inference soundness | **COMPOSE** with FlashProve (take `Sound` as a hypothesis object), do not re-prove | they have it for one model, and we are the surround (PROGRAM §0) |
| audit theorem | **KEEP** (unique) | instantiate over FlashProve |
| WHIR | **WAIT**; neither library has it | ArkLib lists it under directions |

---

## 5. What this does to the roadmap

- **First Lean task:** W2 + W3, the ArkLib MCA import. It converts JBR 73 from conditional to
  proved and replaces our one-third UD band. One bridge file.
- **First counts task:** W1's wrap measurement at `(6, 86, 16)`. Until it exists, "adopt UD-100"
  has no price on the axis that matters (the tower).
- **Retire:** "ArkLib's composition theorems are sorry" and "FRI-Binius has no soundness
  statement". Both are false as of today.
- **Do not:** chase Ligerito's interleaved proximity (W6a) before BaseFold-additive plus imported
  ring switching. Setty's BinarySpartan shows UD-only Ligerito is competitive, but the formal
  object we lack for it is new mathematics (Diamond-Gruen). Importing ring switching is not.
