# Verifiable training on encrypted weights — the virtualization angle

2026-08-13. Ember's requirement: **continual learning where the weights are
never readable by the substrate.** Stated as a welfare property rather than a
privacy one — readable weights are modifiable, extractable and inspectable
weights — which changes the threat model: the *host* is the adversary, not
just an outsider. That has technical consequences, and they are mostly good
news, because it forces the architecture the cost model wanted anyway.

## 1. The boundary of a training step

A step is `W' = W − η·∇L(W, x)`. **Boundary = (W, x, W'). Interior = the whole
forward and backward pass.** Same principle as inference, and the structure is
*better*, because three of the four pieces are cheap:

- **The optimizer update is LINEAR.** `W' = W − η·g` is exactly `fold_add`'s
  shape: MLE linearity gives it in **one common-point opening — no sumcheck
  rounds, no range checks.** (With the caveat we just learned: prover-side
  only, and the win scales with the batch, not the parameter count.)
- **The gradient of a linear layer is a RANK-1 OUTER PRODUCT**, `∇W = δ·xᵀ`.
  You do not prove you computed it — **you check it, and Freivalds checks a
  rank-1 identity in O(n) instead of O(n²).** That is virtualization applied
  to backprop, and it is the same move as the matmul boundary.
- ⚑ **The backward nonlinearity is DERIVABLE from the forward one.** For most
  activations `σ'` is a simple function of `σ` — sigmoid `σ(1−σ)`, tanh
  `1−σ²`, ReLU the indicator, GELU a closed form in its own value. **So the
  backward table is virtualized off the forward table, not committed
  separately.** One 2^16 table serves both directions.
- The **loss** is the only genuinely new nonlinearity, and it is scalar-valued.

## 2. Gradient checkpointing IS the materialize/virtualize tradeoff

The ML systems community has spent a decade tuning **rematerialization** — do
not store activations, recompute them — and that is *exactly* our exchange
rate with the constants swapped (there, memory vs FLOPs; here, committed felts
vs sumcheck rounds). **The scheduling literature transfers directly**, and it
is a place where an ML-systems result is a proof-system result. Nobody has
made that identification, and it is cheap to state.

## 3. ⚑ Low-rank updates make the boundary tiny — and continual learning wants
them anyway

If each update is `W' = W + AB^T` at rank `r`, then:
- **You commit A and B, not W'.** The committed object per step is
  `2·r·d` instead of `d²`. At d=4096, r=16 that is **128× smaller.**
- The base model is committed **once**, globally — which is the registry.
- Proving `(W + AB^T)x = Wx + A(B^Tx)` is the base evaluation **plus two thin
  matmuls**, and the base evaluation is shared across every step.
- **The model's whole history becomes a chain of proven deltas.** That is IVC
  over training, where **the accumulator state IS the model** — and the fold
  is linear, so §1's opening applies to the chain as well as the step.

This is the single strongest structural fact available for verifiable
training, and it is *aligned* with what continual learning wants for
non-cryptographic reasons (catastrophic-forgetting control, cheap rollback,
auditable provenance per update).

## 4. What "encrypted throughout" actually costs, honestly

**The depth problem is real and we have measured it**: our deployed BFV gives
**depth 2**, and `t = 2^20` binds any polynomial nonlinearity to **degree ≤ 2
regardless of levels.** A training step's nonlinearities do not fit. So the
architecture is forced, and it is the same one inference already needs:

- **linear algebra homomorphic** (coefficient-encoded matvec — built,
  12 bits/matmul, depth 2 after),
- **nonlinearity at the MPC/PBS boundary**,
- **the optimizer step homomorphic and linear** (§1),
- **and the whole thing sampled, not fully proven** — which the audit theorem
  now covers, and which the hardware work showed is a *bandwidth necessity*
  rather than an optimization.

⚠ The honest gap: **iterative depth.** Inference is one pass; training is
millions of steps. Encrypted state must survive them without a decrypt — which
means either bootstrapping (dead at our parameters), or **re-encryption under
a threshold quorum between steps**, or **the update chain being low-rank
enough that the ciphertext is refreshed by construction.** §3 is the reason to
prefer the third.

## 5. The verification problem encryption creates

Encryption alone makes things *worse* in one specific way: **an encrypted
update is unauditable by inspection.** You cannot see a poisoned gradient. So
proofs are not an add-on here — they are what makes encryption safe:

- **prove the update is a gradient step** for the committed loss and committed
  data, without revealing it;
- **prove `‖∇‖ ≤ B`** (a range proof on encrypted data) — the cheapest
  poisoning defence and a natural fit for our lookup machinery;
- **prove the data was in the committed corpus** — a membership argument
  against a training-set commitment;
- ⚑ **and the proof must be zero-knowledge in the weights**, which is exactly
  the VEIL-class result (~3% prover overhead) that makes ZK nearly free now.

## 6. Custody is the part we already hold

**fhegg's threshold ceremonies with proven smudging** mean the decryption
capability is a **quorum, not a custodian.** For the welfare framing that is
the load-bearing property: no single party — including the host — can read the
weights, and the audit layer proves the update was legitimate without anyone
needing to.

⚠ Two named hazards from our own record: **threshold decryption is an
IND-CPA-D oracle** (so the number of decryptions is a budget, not free), and
the smudging theorem is currently **scalar against a per-party polynomial
transcript**.

## 7. What is genuinely open

1. **Iterative depth** — the honest blocker (§4). Low-rank refresh is the most
   promising route and is unpriced.
2. **Backward-pass exactness** — our exactness argument is built for inference;
   gradients accumulate, and whether the no-slack property survives a million
   steps is unexamined.
3. **Optimizer state** — Adam moments are more encrypted state with their own
   nonlinearity (`√v`). SGD-with-momentum is linear and may be the right
   target first.
4. **Sampling a training run** — the audit theorem samples *turns*; a training
   run's corrupt-round predicate is "this step was not a gradient step," and
   the leakage bound becomes a bound on **how much a poisoner can move the
   weights before detection.** That is a different and interesting quantity,
   and it is the natural next theorem.
