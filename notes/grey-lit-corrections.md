# Grey literature: five of our verdicts were wrong, and one is a security item

2026-08-13. The lane ember mandated. The eprint-only corpus cost us more than
the math sweep did. **Act on §1 first.**

## 1. ⚑ SECURITY — audit our Poseidon2 instance
> **AUDITED 2026-08-13, VERDICT: no action needed, and TWO PREMISES BELOW ARE
> WRONG.** The 2^106 figure and the post-disclosure round increase are both
> **Poseidon2b, the BINARY-field variant** — we deploy none. The Plonky3
> call-out is (64,16) = **Goldilocks**, which we do not instantiate. Our
> BabyBear t=16/t=24 instances carry a **+286-bit margin**, and the attack
> cannot reach our bar even if every skippable round were free. Full verdict
> and the KoalaBear counterfactual (α=3 roughly HALVES the margin — an input
> to the field decision) in `notes/poseidon2-audit-verdict.md`.

**The Ethereum Foundation moved OFF Poseidon2** (Khovratovich, slide titled
*"Why We Moved from Poseidon2: Round Skipping Attack"*). Mechanism, eprint
2026/306, read at source: the linear layer `M_ε = P_{t/4} ⊗ M_4` has
low-weight eigenvectors giving **invariant low-weight subspaces under BOTH the
linear layer and the S-box**. First case where preimages beat CICO; **2^106
improvement on a recommended 128-bit set.**

**No parameter set is broken** — the paper says so. But: external round counts
were *increased after disclosure to the Poseidon initiative*, so **post-
disclosure sets exist and we may be on the old ones**. ⚠ The paper **names
Plonky3 specifically**: its (n,t)=(64,16) round numbers *"were not considered
by the designers … more susceptible to improved round skips"* — **and our
parameters descend from Plonky3.**

**The fix is free**: reverse the tensor order to `M̄_ε = M_4 ⊗ P_{t/4}` —
*"none of our attacks apply,"* same fast matmul up to index permutation. (The
EF instead went to Poseidon1/MDS at up to 90% more multiplications.)
⚠ Interacts with the Poseidon2-perm reduction-bomb memory: any permutation
change invalidates every `rfl`/`native_decide` fact pinned to current
constants. Also self-reported as unexplored by the initiative: **Poseidon's
Fiat–Shamir and quantum security** — precisely our use.

## 2. ⚑ "Multilinear/GKR substrate absent everywhere" — FALSE, and this was
   the headline of yesterday's convergence note

Our measurement (zero `gkr` in Plonky3-at-our-pin) was right; the
generalization was wrong. **It is the mainstream 2026 architecture and it is
proving Ethereum mainnet blocks**: SP1 Hypercube (LogUp-GKR + Jagged +
BaseFold/WHIR, KoalaBear⁴, **mainnet Feb 2026**), SWIRL/OpenVM2 (GKR +
LogUp-GKR + ZeroCheck over WHIR), **leanVM/leanMultisig — the EF's own PQ
stack** (WHIR, KoalaBear⁵), Ceno, Expander, Binius64. There is an open
library: **SLOP** (MIT/Apache-2.0) with original sumcheck/basefold/whir/
spartan/jagged/multilinear implementations.

**Correct statement: absent from Plonky3, shipped by six systems.** This
changes risk, not doctrine — we still build ours in Lean, but **the pitfalls
and parameters are public**, which is a gift. Documented pitfalls worth
having: Binius64 §1.2 abandoned bit-granularity for 64-bit words because
*"the large field infects what ought to be a bit-level computation"*;
Expander needs **63 GB for 4000 Keccaks** — sumcheck/GKR prover memory is the
sharp edge. ⚠ And one member of our one-hot law is orphaned: **Irreducible
shut down 2025-11-12.**

## 3. ⚑ Ext4 is under the bar — but Ext5 ALONE IS NOT THE FIX

The EF publishes `ethereum/soundcalc`, per-zkVM bit security:
Pico KB⁴ **53** · Airbender M31⁴ **67** · OpenVM BB⁴ **100** · SP1 KB⁴ **100**
· ZisK Goldilocks³ **128** · zkDTVM KB⁵ **128**. **Nothing on a degree-4
31-bit field reaches 128.**

**Two independent 100-bit walls, and extension degree moves only one:**
- **(a) LogUp**: `ε ≤ K·H·R/|F|` — field-size-bound. Ext5 fixes it (100→136).
- **(b) FRI/WHIR query phase** — **query-count-bound; extension degree does
  NOTHING.** OpenVM2 itemizes: gkr_sumcheck 122, whir_sumcheck 127,
  **whir_query 100**.

zkDTVM reaches 128 by fixing both: **Ext5 + rate 1/2 + 261 queries + 20
grinding bits**, `explicit_regime = "unique"`. A complete public recipe for
proven-regime 128 on a 31-bit field with Poseidon2. **Our own note also
understated the damage: 2^123.6 is just |F|; the realized bound is 100.**

## 4. ⚑ Our "conjectured 130" stands on a WITHDRAWN regime

The EF's calculator **deleted the capacity regime outright** — commit
`ffaeb81`, 2025-11-17, *"Remove CBR (due to DG25 and CS25)."* Only UDR and
JBR remain. A "conjectured 130" is very likely CBR-shaped: not an optimistic
bound but one from a **withdrawn** regime. Re-derive before citing.

**And the proven-regime price is now measured, not estimated**: leanVM
publishes both columns — **proven 327 KiB / 1426 XMSS/s vs conjectured
171 KiB / 1481 XMSS/s = 1.9× proof size for ~4% throughput.** That makes the
three-tree FRI-RBR composition land into a moment that needs it.

## 5. Two narrowings and one deletion

- **"Every FHE-over-SNARK number is a model" — FALSE as stated.** Zama
  eprint 2024/451 (CCS 2025) is **measured**: full TFHE PBS proven in 18 min
  on AWS, 48 min on an M2 MacBook, <200 kB proof. But they swapped the FHE
  modulus to Goldilocks, ran 2-bit plaintext, TFHE not BFV. **Narrow to: no
  measured vFHE number exists for BFV at leveled depth over a deployed
  modulus.**
- **Celer NO-GO confirmed on stronger grounds**: it is **group-based**
  (Dory), its sublinearity is in *group operations*. It does not transfer to
  a hash setting at all.
- ✅ **DELETE "no 20-bit option exists"** — that holds only for GBFV
  cyclotomic primes. **t = 2^20 is p^r (p=2,r=20), which HElib bootstraps
  natively** ("bootstrapping with p^r=2^8 is now almost as efficient as p=2").

## 6. ⚑ Our FHE parameter point may not be PQ-128

**Apple ships production BFV at N=4096 with 83 bits of modulus for
`.quantum128`** — and their one shipped set wanting log t ≈ 20 pays
**N=8192 and 148 bits**. Our (N=4096, log q=109, t=2^20) is a **classical**-
line point nobody ships. If we claim PQ-128 there, that is a gap.
Also: the IND-CPA-D bar moved to **2^-128** at two vendors; the shipped
answer to smudging is **noise-squashing into u128 before decryption**, not a
wider compute modulus; and ⚠ **Lattigo discloses, unfixed**, that *"retrying
any MHE protocol must be considered insecure."*

## 7. The audit-report taxonomy — and our own wound is an industry class

93 audit artifacts + two machine-readable corpora (zkbugs 139 bugs; 0xPARC).
**Under-constrained is 96% of CIRCUIT-layer bugs** — but ⚠ the ubiquitous
"96% of ZK bugs" stat is **not Veridise's**, it reproduces a USENIX SoK table,
and the folk framing is wrong: **the largest root cause is mistranslation
(34), not omission (25)**.

**Class 3 — "verifier accepts a prover-supplied value it should recompute" —
is our E10 wound, verbatim, as a confirmed industry-recurring class**: Jolt
uni-skip (*"checked both sides of the bridge, forgot to check the bridge was
connected"*), Dusk PLONK (forgery costs one field division, ~$60M exposed),
OpenVM CVE-2026-46669. **Class 2** (Fiat–Shamir omission): OtterSec broke
**six zkVMs with one recipe**. **Class 8**: SP1's universal forgery needed
**two bugs composing**.

**The finding that matters most for instruments**: analyzer-catchable bugs
are *syntactic substitutions of a weaker check for a stronger one*
(`assert` for `constrain`, membership for permutation, XNOR for AND).
**Human-only bugs are omissions of things the spec never wrote down** — and
**every 2025–26 break lives in classes 2, 3, 8, where nothing detects.**
Aim our instruments there, not at class 1.

Specimens that are our own memory classes in someone else's repo:
`FpChip::assert_equal` zipped with itself (identity-carrier vacuity);
`StatePath::verify` chaining `.is_equal()` = XNOR = "true if all are false"
(∃-image vacuity); a `debug_assert` standing in for a constraint (our `#guard`
class); a typo introduced **while fixing a previous vulnerability** (our
hardening-commit-disarms-a-guard class).

## 8. Two artifacts to read before writing our own

- **`symbolicsoft/soundcalc-lean`** — *"every report cell is a theorem"*,
  certified rational enclosures proved conservative, no floats, no `sorry`,
  `native_decide` deliberately excluded from the primality path, axiom-guard
  CI. **Our GUARD-DISCIPLINE posture, independently arrived at, applied to
  exactly the quantity we most need to name.** Read before the two-regime
  calculator lane.
- **Clean** (zkSecurity) — a Lean 4 eDSL where the circuit is written in Lean
  and proved in tandem, now with a Channel abstraction lifting gadget-local
  proofs to multi-table ensembles. The closest external analogue to our
  Lean-authored-AIR law, and it has reached multi-table.
⚠ Counter-specimen: Powdr's "formally verified autoprecompiles" — ~500 lines
of human-reviewed spec against **~10,000 lines of AI-generated, unreviewed
proof**, constraint-system semantics out of scope.

## 9. Raised priorities

The **$1M Proximity Prize** (proximityprize.org; Boneh/Fenzi/Arnon judging;
**formal verification explicitly encouraged**) — we hold machine-checked
correlated-agreement material, and this is the rare case where our
formalization *is* the submission format the prize wants.
