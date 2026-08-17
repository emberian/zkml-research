# Batching the reduced opening — the obstruction the decision doc did not name, and the lever that survives it

2026-08-16. BUILD lane. Target: the `×2.13`-on-the-wrap lever named in
`breadstuffs/docs/deos/WRAP-NATIVE-HASH-DECISION.md` lever 3(b) and
`notes/leaf-vs-recursion.md` §3d — *"GKR-batch the reduced openings (one sumcheck replaces
~14,300 per-column ExtMuls)"*.

Status: **in progress**, written incrementally.

---

## 0. Where the idea is named, and what each place says about why it was not taken

| place | what it says | obstruction named? |
|---|---|---|
| `docs/deos/WRAP-NATIVE-HASH-DECISION.md:134` | lever 3(b) of a three-lever plan; *"one sumcheck replaces ~14,300 per-column ExtMuls → the ~3.2M residual toward ~0.3M"* | **no** — it is listed as pure upside |
| `docs/deos/APEX-VERIFIER-AIR-REDUCTION.md:157` (Lever D) | *"**COORDINATION-REQUIRED** … changing them to a sumcheck is a **recursion-backend rewrite in the `plonky3-recursion` fork**, not an `apex_shrink.rs` change"* | **yes, but only an ownership one** — "it is in someone else's crate" |
| `HORIZONLOG.md:18343-18345` (2026-07-13, gnark) | after the `S_z − S_x` algebraic hoist landed in `chain/gnark/stark_open_input.go`: *"**GKR-batching the alpha-combination itself is now MARGINAL** (S_x arithmetic ≈ 0.32M total) — the algebraic hoist obsoleted most of that ask."* | **yes, and it retires the lever — on the gnark side only** |
| `notes/leaf-vs-recursion.md` §3d | `×2.13` on the wrap, `×2.05` per turn, *"already named in this repo, undated and untaken"* | no |

So the record holds **three different verdicts on the same phrase**, and nobody had noticed that
the third one (gnark, "marginal") is about a **different circuit** from the first, second and
fourth (the BabyBear in-circuit recursion verifier). The gnark hoist did not touch
`plonky3-recursion`; `HornerAcc = 390,716` is still there.

### 0a. ⚑ The obstruction none of them names, and it is a real one

A sumcheck that batches `Σ_k α^k v_k` over the `q · Σw ≈ 390,716` opened values terminates in a
single claim about the **multilinear extension of those values at a random point**, `Ṽ(r)`. The
verifier must discharge that claim. It has exactly two ways:

1. **Recompute `Ṽ(r)` from the values** — Θ(N) again. No saving. The sumcheck was free only if
   someone else answers the final claim.
2. **Open it from a commitment to `V`** — but the only commitment the opened values have is the
   **Merkle leaf** of the child's MMCS, and a Merkle root supports **no evaluation opening**.

⚑ And the verifier *already holds every one of those values in the clear*: it must, because it
hashes them into the per-query leaf sponge (`64.9%` of in-circuit permutations, §2c of
`leaf-vs-recursion.md`). So the values are not hidden behind a commitment that could be opened —
they are plaintext circuit witnesses that are separately hashed.

> ### ⚑⚑ Batching the reduced opening with a sumcheck requires an **evaluation-binding commitment on the opened values**. Two-adic FRI gives **univariate** openings only. So lever 3(b), *as stated*, is not a prover-side rearrangement — it is a **PCS replacement**, and its cost is a new commitment scheme, not a backend rewrite.
>
> That is exactly why SP1 6.4 went Jagged → Stacked → **BaseFold** and OpenVM 2.0 went Stacked →
> **WHIR** (`leaf-vs-recursion.md` §5): both are multilinear PCSs whose openings *are* MLE
> evaluations, so the sumcheck's terminal claim is answerable. Our stack cannot answer it.

The `×2.13` in `leaf-vs-recursion.md` §3d is therefore **derived against an assumption that the
sumcheck's terminal claim is free**, and it is not free. The lever is not wrong; it is
mispriced and mis-scoped — it is a PCS migration wearing a backend-rewrite's clothes.

---

## 1. The lever that *does* survive, and it is pure algebra

(see §2 below — implementation and measurement in progress)
