# Poseidon2 round-skipping: structurally in scope, quantitatively inert. No change.

2026-08-13. And ⚠ **two premises in my own escalation were wrong at the
source** — I relayed a grey-lit summary of eprint 2026/306 without reading the
paper, which is precisely the "READ THE BLOCKER BEFORE YOU RELAY IT" failure.

## My errors, corrected at source

1. **The 2^106 figure is Poseidon2*b* — the BINARY-FIELD variant** (§5.3,
   from eprint 2025/1893). **We deploy no binary-field Poseidon2.**
2. **The post-disclosure round increase was in Poseidon2b too**, not
   prime-field Poseidon2 and not Plonky3. **There is no post-disclosure
   parameter set we are behind on**; Plonky3's numbers are unchanged.
3. **The Plonky3 call-out is `(n,t) = (64,16)` — a 64-bit prime
   (Goldilocks).** We instantiate no Goldilocks and no KoalaBear Poseidon2
   (verified: only `Poseidon2BabyBear<16>` ×30 and `Poseidon2Bn254<3>` ×26).
4. The paper's own bottom line, which the summary omitted: *"for all Poseidon
   instances we found no parameter set failed to meet its asserted 128-bit
   security level."*

## The structural precondition IS present — this part was right

Our external layer is exactly `M_ε = P_{t/4} ⊗ M_4`, verified in the pinned
source (`p3-poseidon2/src/external.rs:135-159`: chunkwise M_4 then the outer
circulant). So: **affected-but-below-threshold**, not out of scope.

## Margins computed at OUR parameters (bar = 2^123.6, 8 BabyBear limbs)

| instance | attack | cost | margin |
|---|---|---|---|
| BabyBear t=16 (α=7, R_F=8, R_P=13), Merkle compress | Lem 4.5 | **2^409.9** | **+286.2** |
| same, sponge mode | **no round skip exists** (Table 5: "–") | — | n/a |
| same, cico-4 | Tbl 2 | 2^207.7 | +83.7 |
| BabyBear t=24 (the paper's *primary* studied set) | Tbl 5 | **2^409.9** | +286.2 |
| BN254 t=3 | **out of scope structurally** — t∉{12,16,20,24}, and the WIDTH=3 branch uses circ(2,1,1) with no tensor at all | — | — |
| minidregg | no concrete instance (generic `PermSpec`; open residual) | — | — |

**Why the margin is robust rather than merely large**: reaching the bar needs
`8·r_F + r_P > 59.0`, and the maximum available in the paper's own model is
**45**. **The attack cannot reach our bar even if every skippable round were
skipped for free.** (The paper actually achieves 8.)

## ⚑ The input to the FIELD decision

**α=7 is the dominant reason we are safe.** Counterfactual, computed:
**KoalaBear (α=3) roughly HALVES the margin** — t=16 compression 2^253.6
(+130), t=24 collision 2^234.6 (+110.9). Still safe, but **a move to
KoalaBear or any α=3 field is the change that makes this worth re-deriving.**
The field memo's case for KoalaBear was low constraint degree; this is the
cost side of exactly that property, and it belongs in the decision.

## Why the fix was NOT applied (good judgment, recorded)

`M̄_ε = M_4 ⊗ P_{t/4}` is applicable (needs c ≥ t/4; we have c=d=8≥4). The
lane declined **not on cost** but because it would move us off an
externally-audited primitive onto a **bespoke variant with zero third-party
cryptanalysis** — an assurance *decrease* on a different axis, against a
286-bit margin. Correct call.

**Blast radius if ever reconsidered (measured)**: 7 independent hardcoded
constant copies (circuit, sel4 crypto-floor, fhegg, gnark, two Lean modules,
a TS bridge), 688 Lean files referencing Poseidon2, 71 descriptors with
constants inline, the params validator pinning `rc_source`, a VK epoch and
re-genesis — **and we would have to fork `p3-poseidon2`**, since the tensor
order is upstream's.

## The residual that IS real and is not covered by any margin above

**Poseidon's Fiat–Shamir and quantum security are self-reported "largely
unexplored" by the Poseidon initiative — and FS is precisely our use.** Two
open 2026 grants target exactly it, one seeking *"parameters where FS security
is easier to break than standalone CICO, exploiting Poseidon in a
Schnorr/Plonk transcript."* Every number in the table above is a **classical
algebraic** bound. ⚠ Provenance: that deck discloses it was Copilot-generated;
it is the initiative's self-assessment, not a measured result.

## Two side findings worth acting on

- `Dregg2/Circuit/Poseidon2Binding.lean:62-63` cites recursion rev
  `c14b5fc07…` while `Cargo.toml:370` pins `fc3c6df…` — parameters unchanged,
  citation stale.
- **`Poseidon2BabyBearW16.lean` pins the deployed permutation with 9 `#guard`s
  and zero `native_decide`** — the guard-discipline class on the *deployed
  hash's KATs*, and the highest-value place in the tree to have named theorems
  instead. (They fail loudly at elaboration so nothing goes silently stale,
  but they leave no reusable term; re-establishment must stay on the compiled
  evaluator, since `rfl`/`decide` through one permutation is the 47.6 GB bomb.)
