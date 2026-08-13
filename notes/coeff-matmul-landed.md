# The rotation-free coefficient matmul: built, measured, and it corrected the theory

2026-08-13. `fhegg-fhe/src/bfv_coeff_matmul.rs` + oracle tests, commit
`08f0df18b`. 13 unit + 10 oracle tests green; full fhegg-fhe suite 207/0.
No `vendor/` changes. **`Encoding::poly()` is now used by something.**

## Measured (N=4096, log₂q=109, t=1032193)

- **Noise per matmul: 12 bits** with split-sign (vs 25 direct/SIMD).
  Headroom after: ~84 bits.
- **Depth after: 2 further ct×ct multiplies** — established by *consuming*
  them and checking decryption, not estimated.
- **Wall-clock, 512×31 int8, release: 466 µs** evaluate per input; 955 µs
  one-time weight encode.
- **Packing is the real blocked layout**, not one-result-per-multiply:
  `n_o` rows packed into one polynomial under `n_i·n_o ≤ N` ⇒ **132
  results/multiply at inner dim 31**, 8 at 504. Ragged blocking both
  directions.

## ⚑ The correction to our own theory note

The note's second structural reason — *"coefficient-encoded plaintext norm is
the weight magnitude (2^7) instead of ~t/2 — a flat 12-bit gift"* — **does not
hold as stated.** fhe.rs lifts `Z_t → R_q` with residues in `[0,t)`, so every
**negative** weight becomes a coefficient of size ~t, and int8 weights are
half negative. Same weights, same ciphertext, fresh noise 12 bits:

| lift | noise after ct×pt |
|---|---|
| SIMD | +25 |
| **coefficient, direct** | **+25 — advantage ZERO, not 12** |
| coefficient, **split-sign** | **+12 — 13-bit saving** |

Recovery is `WeightLift::SplitSign` (`W = W⁺ − W⁻`, disjoint support so **no**
capacity cost, one extra ct×pt per block) and it is the default. The gift is
real and it is bought by the sign split, not by the encoding alone.

## ⚑ The finding I asked for rather than papered over

**Inner dim ≤ 31 at full int8×int8 is not a useful layer width.** The binding
constraint is the deployed **20-bit t**, not the technique. Nothing silently
downgrades — the caller states bit widths and the plan refuses or doesn't.

And our note's "inner dim 512 exactly ⇒ 4-bit × 8-bit" is **off by the
boundary**: 512 > 504, so the plan **refuses** it. There is a shipped test
asserting exactly that.

**Practical consequence**: the rotation-free route is real, but at useful layer
widths it needs 4-bit weights (≤504) or 4×4 (≤8064). Anyone wanting int8×int8
at width 512 must change `t`, not the encoding.

## Honest scoping of the comparison

The lane measured **only the plaintext-norm term** (13 bits in our favour).
It did **not** estimate the full slot/BSGS route — that needs rotation keys
this tree has no material for, so BSGS's key-switch term is unmeasured. **The
honest claim is "wins by at least 13 bits," not a full comparison.**

Also corrected: the technique is Cheetah **§3.1** (`HomFC`, Prop. 1 + Fig. 2),
not §4.1 (which is the millionaires' protocol).

## Named-and-deferred

LWE `Extract` (so the whole RLWE ciphertext is returned — **sound when the
decryptor owns the vector, unsound if routed elsewhere**), Cheetah's 2PC
re-masking, LZ/Bae PC-MM. All in the module ledger.

Noise here is **measured, not proven** — no theorem claimed; the ring-lift
work in `metatheory/Bfv/Ring.lean` is the proof side.
