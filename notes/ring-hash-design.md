# Ring-hash candidate: the design note

2026-08-13. **Status: IN PROGRESS — written incrementally by the revival lane.**
The predecessor design lane died on credits after writing three scripts and no
prose. This file is the prose. Every number below was produced by re-running the
scripts in this session; the run outputs are quoted, not remembered.

**Scripts (all in `~/src/ring-ro-hash/`, all run in seconds on a laptop):**

| script | what it settles | runtime |
|---|---|---|
| `design_branch_frontier.py` | branch numbers, exact; the τ=4 closure | 6.8s |
| `design_mds_interleave.py` | schedule/cost table for σ-density | 3.4s |
| `design_gadget_feistel.py` | the second candidate, full-scale | 58.2s |
| `costmodel.py` | the 716.8 rows/elt baseline (2026/1127 App C.3) | — |
| `sigma_poseidon.py` | the C1–C5 design conditions + validator | — |
| `density_repricing.py` | why support-3, not support-1 (Chaghri) | — |

Prior context: `two-rocks.md` §Rock 2 (the survey and the enabling theorem),
`ring-hash-cryptanalysis.md` (the attack-side verdict this note answers).

---

## 1. The branch-number weakness is CLOSED at τ=4

`ring-hash-cryptanalysis.md` §1 prices the branch deficit as the design's **#1
weakness**: branch ≤9 against an MDS 65, "~7.2× weaker", independent of d. That
pricing is correct **at τ=1** and **for the support-3 layer**. It is not a
property of the design.

### 1.1 What τ is, and why it moves the answer

τ is the degree of the irreducible factors of X^d+1 mod q. The deployed Frog ring
of 2026/1127 has d=16, τ=4: X^16+1 splits into **four quartics**, so there are
ℓ = d/τ = **4 slots**, each a copy of F_{q^4}. At τ=1 (q ≡ 1 mod 32) there are 16
slots, each F_q.

The σ-layer's job is to mix slots. **Slot-MDS means branch ℓ+1.** At τ=1 that is
17 and needs the full dense layer; at τ=4 it is **5**, and the slot-permutation
group has order 4 — so a layer supported on the whole group is small.

### 1.2 Measured (`design_branch_frontier.py` Part D)

Model: p=89 (chosen because ord_32(89) = 4 = τ, reproducing the Frog splitting
structure at a toy size), ℓ=4 slots over F_{p^4}, branch computed exactly by
enumerating support pairs with ranks over F_{p^4} taken via the blown-up regular
representation.

```
  {1,5,-1}   (1 row)              slot-support 3   branch = 4  (max 5)
  {1,5,-1,-5} = G/<q> (2 rows)    slot-support 4   branch = 5  (max 5)   SLOT-MDS
```

**The automorphism set {1, 5, −1, −5} at 2 rows per element per round reaches
branch 5 = slot-MDS.** That is **one extra row** over the support-3 layer the
prior lane costed (which reaches branch 4). The #1 weakness closes for +1
row/element/round — *provided* we go to τ=4, which is a real cost, adjudicated in
§4.

⚠ **Caveat carried from the script, do not drop it.** The Part-D model omits the
Frobenius twist that σ_k carries into the moved slot at τ>1. The script's stated
justification: a twist is a fixed invertible F_p-block, and composed with the
generic multiplication block D it is again a generic invertible block on the same
support pattern, so it cannot change a rank statistic. That argument is sound for
*these* measurements (which are all ranks of support submatrices) and is NOT
sound for anything that depends on the twist's field-theoretic content — which
is exactly where the extension-field risk of §4 lives. The branch measurement is
clean; do not reuse the "twist doesn't matter" line outside it.

### 1.3 The τ=1 picture, exactly (Parts A and C)

At d=8 (exact enumeration to full weight), both q=257 and q=65537:

```
  layer                                 cost  support  branch   law |K|+1
  Sigma {1,5,-1}              (1 row)      1        3       4   MATCHES
  Sigma {1,5,25,-1,-5}       (2 rows)      2        5       6   MATCHES
  Sigma G (dense, generic)   (4 rows)      4        8   8@q=257 / 9@q=65537
  Sigma G, CAUCHY-programmed (4 rows)      4        8       9   MATCHES (both q)
  Prod (I+c1 s5)(I+c2 s-1)   (2 rows)      2        4       5   MATCHES
  Prod ... 3 factors         (3 rows)      3        6       6   6 vs law 7
  Prod ... 4 factors         (4 rows)      4        8       6   6 vs law 9
```

Three things fall out, and two of them are design decisions:

1. **branch(Σ-layer) = |K| + 1 exactly**, for generic coefficients. Certified
   exactly to weight 5 at d=16 (Part C: 229,056 support pairs checked, no
   singular pair), with the upper bound |K|+1 constructive (one active slot
   activates exactly |K| outputs). So at d=16 the 4-row layer's branch is in
   [6,10] with law 10 — the law is not fully certified at proposal size, and
   saying "branch 10 at d=16" would be overclaiming.
2. **Program the dense layer as a Cauchy matrix, don't sample it.** The generic
   dense layer misses MDS at q=257 (branch 8, not 9) — that is birthday, not
   structure (~50 expected singular square submatrices at q=257, ~0.2 at
   q=65537, ~2^-34 at q~2^64). But the σ-basis has d² free coefficients, so the
   slot matrix can be *chosen*: M[i][j] = 1/(x_i+y_j) is MDS at every q by
   theorem, every Cauchy minor being nonzero. **This removes the genericity
   caveat entirely and costs nothing.** Do this.
3. **The product form Π(I + c_i σ_{k_i}) is strictly dominated.** At 4 rows it
   reaches branch 6 against a support law of 9, at *both* moduli — so the
   correlated coefficients are structurally deficient, not birthday-deficient.
   Equal cost, worse branch, no compensating property. **Use the Σ-form.**

### 1.4 A measured law that contradicts the naive bound

Part B composes the free R_q-MDS across t elements with the per-element σ-layer
and measures the full-state branch exactly (t=2, d=4, q=65537, n=8):

```
  sigma support K      |K|   t   branch (exact)   law t+|K|
  [1, 5]                 2   2                4           4   MATCHES
  [1, 5, 7]              3   2                5           5   MATCHES
  [1, 3, 5, 7]           4   2                6           6   MATCHES
```

**Single-round composite branch is t + |K|, not the naive t·|K| + 1.** The free
R_q-MDS *adds* t−1 to the slot branch; it does not multiply it. The attaining
construction (script's own): put a difference on one slot across all t elements,
chosen in the element-MDS's preimage so that t−1 elements cancel after the MDS;
the survivor pays only the σ-layer — weight t in, weight |K| out.

⚠ **Two corrections to how this result has been relayed.** (a) "Certified
exactly to weight 5 at d=16" belongs to the *single-element* law |K|+1 (Part C),
**not** to the composite law t+|K| (Part B). They are different measurements.
(b) Part B as written measures **only t=2**, three data points. See §1.5.

**What the law does and does not mean.** At q~2^64 with DP(x^7) ≤ 6/q, even the
one-round t+|K| bound puts differential trails far below 2^-128 within two
rounds. **The branch gap was never about statistical trails.** It is about
*structured* attacks — invariant subspaces, §D-style slot-locality — which live
at slot granularity. Cross-granularity multiplication ((t+1)(|K|+1) active
S-boxes) only appears over 4 rounds via the AES superbox argument, which is a
standard wide-trail *inference*, not a measurement, and must be labelled that
way.

### 1.5 Extending the t+|K| law past t=2

*(pending — see `design_branch_law_check.py`)*

---

## 2. The schedule cost table

*(pending)*

## 3. The second candidate: gadget-Feistel

*(pending)*

## 4. The fork: τ=1 vs τ=4

*(pending — cryptanalysis lane input outstanding)*

## 5. Delegation vs. a new hash

*(pending — literature lane input outstanding)*
