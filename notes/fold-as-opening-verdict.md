# fold_add as one opening: the fact is published, the ratio is one-sided, and item 0 may delete the plan

2026-08-13. `notes/fold-as-opening.md`. Both trees clean, 17/17 green.

## The prior art premise was false twice over — and both were in our corpus

- **Binius64 Blueprint §4.4 "The Zero Reduction"** says it almost verbatim
  (`~/paperbin/binius64-blueprint-spec.pdf`): *"it adds no prover message and
  no sumcheck round… a single evaluation at a point the prover could not
  predict therefore certifies the constraint outright."* Named **"virtual
  polynomial"** in Binius, with a lineage through Jolt Atlas, Powdr, DeepProve.
- ⚑ **Our exact statement is in paperbin, solved the AIR way, by the authors of
  the paper I flagged earlier.** Zama **2024/451** §"Weighted sum" proves
  `ĉ = Σ wᵢcᵢ` over LWE ciphertexts, weights *"assumed to be constants known
  in advance and built in the arithmetic circuit."* **So the AIR route we
  priced against is the published baseline, not a straw man** — and their
  per-input hash chain is exactly the in-circuit binding route the lane had
  dismissed as *"not an option, it spends the entire win."* **Someone is
  spending it.**
- **"Free additions ⟺ no modular reduction" is Rinocchio (2021) p.39** — the
  mechanism written up as *"the whole mechanism, and it should be said that
  way"* was said five years ago in this exact setting.

## ⚑ The correction that matters: the ratio is PROVER-SIDE ONLY

I have been quoting **"ratio = B, 690× at B=512"** without a side qualifier.
**The verifier moves the opposite way**: `B+1` openings against `B+1`
commitments is **O(B) Merkle work**, where the AIR verifier is
**polylogarithmic**.

And the standard fix does not apply: one shared tree over all `B+1`
polynomials **collides head-on with binding condition (c)**, which requires
**B independent per-trader roots produced at different times by different
parties**. Unresolved. Irrelevant at B=4 — **and it decides whether "raise
ORDER_COUNT to reach 715×" is real or a mirage.**

## ⚑ The stub is a shipped-bug class, not a toy caveat

OtterSec on Dusk PLONK, **~$60M exposed**: *"the prover slipped four public
selector evaluations into the proof struct, and the verifier consumed them in
its final equation without ever validating them against the trusted
commitments."* **That is a one-for-one description of the `verify` as it
currently stands.** Relabelled from caveat to defect class.

## ⚑ Item 0, which can delete items 1–4

**Both Zama predecessors choose `q_FHE` = the proof field** — Goldilocks in
2024/451, and **2025/719 uses BabyBear, our field** — and thereby need **no
limb map, no range leg, no lazy accumulation.**

My stated reason for not doing that — *"we do not control the modulus"* — **is
an assumption I never verified, and verifying it is far cheaper than building
the four things that depend on it.** Do item 0 first.

## What survives, narrowly and really

**A batch fold is ALIGNED-POINTWISE, not a contraction** — the batch index is
not summed against the output coordinate — **so even the two sumchecks Zama
2026/027 runs are unnecessary.** Narrow, real, worth building, and partially
spent by the verifier-side finding above.

## Named gap, no absence claimed

The classic **verifiable-HE-for-linear-only** line — Fiore–Gennaro–Pastro
(CCS'14), Fiore–Nitulescu–Pointcheval (PKC'20), Bois–Cascudo–Fiore–Kim
(PKC'21), Chatel et al., Madi et al., Boneh–Drake–Fisch–Gabizon — **is absent
from paperbin entirely and is the most likely place for a further hit.**
