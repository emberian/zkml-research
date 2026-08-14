# The KoalaBear migration — the lb question, the composed total, the soundness, the flag day

2026-08-13. **Written incrementally while measuring.** Status of each claim is tagged
`[derived]`, `[measured-here]`, `[measured-elsewhere, cited]`, `[open]`.

---

## 0. The verdict

> ## ⚑⚑⚑ **The `lb = 2` question does not need KoalaBear. The blowup floor is a one-line bit-reversal bug in `p3-fri`, and `lb = 2` runs at BabyBear with α = 7 once it is fixed.**
>
> **Measured, end to end** (§1.4c): plonky3's `get_evaluations_on_domain` extrapolation path
> applies `bit_reverse_rows()` once too many, so when the quotient domain exceeds the committed
> LDE the prover gets **the right values in the wrong row order**, computes a wrong quotient,
> and emits a well-formed proof the verifier rejects with `OodEvaluationMismatch`. One inserted
> call fixes it; with the fix a degree-7 AIR verifies `Ok` at `log_blowup = 2`, and a corrupted
> trace still rejects. The bug is on upstream `main` today, was introduced by the same commit
> that deleted the guarding `assert!`, and the test written to cover the branch **takes the
> other branch**. ⚑ **Our own gate asserts the refusal must happen, so it goes red when the bug
> is fixed — we have frozen a bug as a law.**
>
> ### And the rest of the migration's case does not survive contact either:
>
> | the brief's factor | what it actually is |
> |---|---|
> | hash rate **1.33×** | a **counted-multiplication** ratio; measured native wall clock is **~1.02×** (§3.1) |
> | blowup **2×** | already inside `prover-floor`'s 3.4×, **and** it belongs to the descriptor degree budget + a `p3-fri` bug, not the field (§3.2, §1.4c) |
> | narrowing **2.83/2.24** | ⚑ the ratio grew because the **baseline** grew. Absolute committed felts/perm go **157 → 164, i.e. 4.5% WORSE**, and both published ratios reproduce exactly from `R_P = 13 → 20` alone (§10) |
>
> **Composed honestly, KoalaBear is ≈1.05× on the leaf prover.** What it genuinely buys is one
> thing: the chip's constraint degree `7 → 3`, hence its quotient chunks `8 → 2`. And **it
> cannot spend that on blowup**, because KoalaBear's two-adicity is 24 against a `2^21` wrap,
> which pins `log_blowup = 3` exactly (§4).
>
> **Meanwhile, at BabyBear, changing nothing:** dropping `(6,19) → (2,57)` is **13.13× faster
> to prove on a 4096-row descriptor, measured today** (§6.3), **raises** the binding soundness
> column (§2.2), and is **nearly free on the wire at the proven bar** (§2.3b). And our
> commit-phase bound is BCIKS20 (2020) where plonky3 already uses BCHKS25 (2025) — worth
> **+17 to +21 real bits** on the column that binds (a raw gap of +19 to +25, less 2.78 bits of
> round-accounting difference), verified against ten Lean-proved values (§12).

### Reading order

**This was written incrementally while measuring, so the sections are in the order they were
learned, not in order of importance.** The three that carry the verdict landed last:

> **§1.4c** — the blowup floor is a `p3-fri` row-order bug, settled by construction.
> **§10** — both narrowing ratios are `R_P` in disguise and the absolute inverts (157 → 164).
> **§12** — our commit bound is BCIKS20 (2020); the 2025 one is worth +17–21 bits.
>
> Then **§6** (twelve real descriptors, measured today), **§4** (two-adicity pins `lb = 3`),
> **§11** (the flag-day census — §7 is the Rust-side sketch, §11 supersedes it),
> **§13** (corrections owed to other files), **§8** (the ordered action list).

---

## 0b. The lb question in detail, before the derivation

> ⚠ **§0b was written before §1.4c** and treats the `⌈log₂(d−1)⌉` floor as real. It is kept
> as-is because the degree analysis in it is still exactly right about *plonky3's behaviour*
> and about which table binds; only the conclusion that the floor is unavoidable is
> superseded. Read it as "what the floor costs while the bug is unfixed."

**`lb = 2` is legal at α = 3 — and it was never the field's fault.** The blowup floor is
`log_blowup ≥ ⌈log₂(d−1)⌉` where `d` is the batch's max constraint degree. At BabyBear the
Poseidon2 chip's inline `x⁷` S-box sets `d = 7 ⇒ floor 3`; α = 3 drops the chip to `d = 3`.
**But the chip is not the only thing at the ceiling**: `setFieldDynVmDescriptor2`'s `main`
table is pinned at `d = 8` and `map_ops`/`map_absent` at `d = 4`, and the blowup knob is
**global**. So α = 3 alone moves the floor `3 → 3` (blocked by the degree-8 main), and
`3 → 2` only if that one table also comes down. **The α = 3 lever is real but it is second
in line behind a descriptor-level degree, not a field-level one.**

**And the bigger finding is that the lb lever is not KoalaBear's to sell.** The deployed
IR-v2 blowup is **6**, four rungs above its own BabyBear floor of 3. Moving `6 → 3` is legal
today, changes no field, and is measured in-tree at **6.4× faster wrap** and **35% smaller** —
*and it raises the binding soundness column by 10 bits.* Every "α = 3 halves the blowup"
sentence is pricing the last rung of a ladder whose first four rungs are unclimbed.

**Measured here, today** (§6): the `⌈log₂(d−1)⌉` floor predicts all twelve real descriptors
correctly; **43 of 132** goldens are chip-bearing (not 38 of 91), so **89 of them can run at
`lb = 2` at BabyBear right now**; and dropping `(6,19) → (2,57)` at JBR-73 parity is
**13.13× faster to prove on a 4096-row descriptor** — against 1.74× on the *same descriptor*
at 64 rows. **The lb lever's value grows with trace height, and zkML traces are 2^16–2^20.**

⚑ **The composed total is not `1.33 × 2 × (2.83/2.24) = 3.36×`. Measured, it is `1.02 × 1.00
× 1.029 ≈ 1.05×` on the leaf prover** (~1.5× on the recursion engine). All three factors
survive as facts and none survives as a factor: one is a counted-multiplication ratio quoted
as wall clock, one belongs to the descriptor degree budget rather than the field, and one is
a chip-only ratio applied to a batch in which the chip is 13.35% of committed cells. §3.

⚑ **And the constraint nobody had in the product runs the other way** (§4): KoalaBear's
two-adicity is **24**, not 27, so `max rows = 2^(24 − lb)`. The wrap pads to `2^21`.
**KoalaBear at `lb = 6` does not fit — `lb ≤ 3` is a REQUIREMENT of the migration, not
something it unlocks.** Combined with the floor of 3, **KoalaBear pins `log_blowup = 3`
exactly: the knob has one legal position.**

---

## 1. The `log_blowup` floor, derived

### 1.1 The derivation

Let the trace domain `H` have size `n = 2^k`, and let the AIR's maximum constraint degree in
the trace polynomials be `d`. The constraint composition polynomial

    C(x) = Σ_i λ_i · c_i(trace(x), trace(gx), …)

has `deg C ≤ d·(n−1)`. The vanishing polynomial `Z_H` has degree `n`, so the quotient

    Q(x) = C(x) / Z_H(x)      has      deg Q ≤ d·(n−1) − n = (d−1)·n − d  <  (d−1)·n .

A degree-`<(d−1)n` polynomial cannot be committed as one degree-`<n` codeword, so plonky3
**splits `Q` into `2^lqd` chunks each of degree `< n`**, with

    log_quotient_degree  lqd = ⌈log₂(d − 1)⌉        [derived]

which is the smallest power of two ≥ `d−1`. To produce those chunks the prover evaluates the
composition on a **quotient domain of size `n · 2^lqd`**, and it obtains the trace values on
that domain from the *already-committed trace LDE*, whose size is `n · 2^log_blowup`. In
plonky3 the quotient domain must fit inside the committed LDE:

> **`log_blowup ≥ log_quotient_degree = ⌈log₂(d − 1)⌉`.**

Confirmed verbatim at source. `uni-stark/src/symbolic.rs:44-80` in the pinned rev `82cfad7`
(the function is called **`get_log_num_quotient_chunks`** now, not `get_log_quotient_degree`):

```rust
let constraint_degree = (degree_hint + is_zk).max(2);
let result = log2_ceil_usize(constraint_degree - 1);
```

and `uni-stark/src/prover.rs:200-201`
`create_disjoint_domain(1 << (log_ext_degree + log_num_quotient_chunks))`.

⚑ **But read §1.4 before treating this as a law of nature.** It is a property of *this
implementation*, and I believe I have located the exact line that makes it one.

### 1.2 The floor as a function of `d`

| max constraint degree `d` | `d − 1` | `lqd = ⌈log₂(d−1)⌉` | **minimum legal `log_blowup`** |
|---:|---:|---:|---:|
| 2, 3 | 1, 2 | 1 | **1** |
| 4, 5 | 3, 4 | 2 | **2** |
| 6, 7, 8, 9 | 5–8 | 3 | **3** |
| 10–17 | 9–16 | 4 | **4** |

So `d = 7` (BabyBear α = 7) ⇒ floor 3; `d = 3` (KoalaBear α = 3) ⇒ floor **1**;
`d = 5` ⇒ floor 2. The often-quoted "degree 7 forces `lb ≥ 6`"
(`notes/prover-floor.md`, "Three things to act on" #3) **is wrong by three rungs** — it
is `⌈log₂ 6⌉ = 3`, and I believe it is a transcription of the *deployed* 6 rather than
a derivation. ⚑ Flagged for correction in that note.

### 1.3 The tree agrees, in a comment, and enforces nothing

`circuit/src/plonky3_prover.rs:125-127` states the relation verbatim:

```rust
// log_blowup must be >= log2_ceil(max_constraint_degree - 1).
// For Poseidon2 S-box (degree 7): log2_ceil(6) = 3, so log_blowup >= 3.
```

Two more copies: `circuit/src/stark_zk.rs:139-140`, `recursion-verify/src/config.rs:49-51`.
**All three are comments beside a hand-set constant. Nothing checks the relation.**
`create_config_with_fri` / `_full` (`circuit/src/plonky3_prover.rs:174-237`) contain zero
`assert!`, zero `debug_assert!`, no `Result` — every argument is moved into a
`FriParameters` struct literal (`vendor/plonky3-fri-82cfad73/src/config.rs:9-21`, a bare
`pub` struct with no constructor and no invariant) and handed to `TwoAdicFriPcs::new`. The
config constructor **never sees an AIR**, so it cannot know a constraint degree even in
principle.

### 1.4 ⚑ The failure mode is worse than "fails self-verify 60 ms later"

The pinned `p3-fri`'s `get_evaluations_on_domain` has a **re-interpolation fallback**
(`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:464-484`), so the prover does not assert
out. It runs to completion and emits a **complete, well-formed, unverifiable proof**:

```
lb=2 q=19: IR v2 batch self-verify failed: OodEvaluationMismatch { index: Some(1) }
```

(index 1 = the Poseidon2 chip table.) The brief's "60 ms later" is optimistic: the latency is
one full **prove**, which is 29–58 ms on the 8-row measurement fixture
(`docs/reference/FRI-PARAM-FRONTIER.md:337`) and **~18 minutes at the apex fold**
(`docs/reference/PROVEN-120-CONFIG.md:367`). And `circuit-prove/tests/fri_hundred_bit_cutover.rs:222`
names the class exactly:

> **`NO FriParams carries a constraint degree. A ledger cannot see this. Only a proof can.`**

This is the *documented-wound-is-not-a-detected-one* class: the relation is written down
three times, derived correctly, and guarded by nothing. **A one-line refusal in
`create_config_with_fri_full` cannot be written** (no AIR in scope), but a refusal in the
per-descriptor prove entry point **can** — `instance_degrees(desc)` already exists
(`circuit/src/descriptor_ir2.rs:8505-8553`) and is called by a test.

**And upstream had the guard and removed it.** Both older checkouts
(`~/.cargo/git/checkouts/plonky3-6913fcc9a09bb94f/{0861b62,cf7bd91}/fri/src/two_adic_pcs.rs:177`)
carried a hard `assert!(lde.height() >= domain.size());` under a `// todo: handle
extrapolation for LDEs we don't have`. The pinned rev replaced that assert with the
extrapolation branch. **A loud panic became a silently invalid proof** — the
hardening-commit-disarms-a-guard class, upstream, and the reason our lb=2 failure is a
verifier rejection instead of a crash.

The one place in the whole pinned plonky3 tree that states the relation as a check is
`uni-stark/src/security.rs:244-249`:

```rust
debug_assert!(
    params.air_max_constraint_degree <= blowup_factor + 1,
    "AIR max constraint degree {} exceeds blowup+1 ({}); the prover cannot commit a quotient",
    ...
```

`d ≤ 2^lb + 1` and `lb ≥ ⌈log₂(d−1)⌉` are the same condition, so the intent is exactly right.
It is (i) a `debug_assert!`, compiled out in release; (ii) inside `ProvenSecurity::compute`,
which **`prove` and `verify` never call** — the only callers are the opt-in reporters
`Proof::conjectured_security` / `Proof::proven_security`; and (iii) carrying a message
("the prover cannot commit a quotient") that is now false, since the prover demonstrably does.
**The check exists, in a calculator nobody on the proving path runs.**

### 1.4b ⚑⚑ The floor may not be real at all — a located candidate bug

`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:457-484`, verbatim (byte-identical to the
registry copy):

```rust
let lde = self.mmcs.get_matrices(prover_data)[idx];
if domain.shift() == Val::GENERATOR && lde.height() >= domain.size() {
    return lde.split_rows(domain.size()).0.as_cow().bit_reverse_rows();
}
// The committed LDE contains bit-reversed evaluations over `gH`. …
let poly_height = lde.height() >> self.fri.log_blowup;
let lde_mat = lde.as_view().bit_reverse_rows().to_row_major_matrix();
let mut coeffs = self.dft.coset_idft_batch(lde_mat, Val::GENERATOR);
let width = coeffs.width();
coeffs.values.truncate(poly_height * width);
coeffs.values.resize(domain.size() * width, Val::ZERO);
let result = self.dft.coset_dft_batch(coeffs, domain.shift()).to_row_major_matrix();
let result_width = result.width();
RowMajorMatrixCow::new(Cow::Owned(result.values), result_width).bit_reverse_rows()
```

**The arithmetic of the slow path is exact.** The trace polynomial has degree `< n`;
`poly_height = lde.height() >> log_blowup = n`; truncating to `n` coefficients is lossless;
zero-padding and coset-DFT-ing onto the larger coset gives the *correct values*. So the
quotient-domain floor is **not** a mathematical necessity — a correct implementation can
compute the quotient at any blowup, at the price of one iDFT+DFT per matrix.

Which raises the question the measurement forces: **if the fallback is arithmetically exact,
why is the lb=2 proof invalid?** My reading says the two paths disagree in **row order**:

- the committed LDE is stored **bit-reversed**; the fast path takes a prefix of the stored
  matrix and applies `bit_reverse_rows()` → **natural order**;
- the slow path's `coset_dft_batch` produces **natural order** already, and then applies
  `bit_reverse_rows()` → **bit-reversed order**.

One bit-reversal too many on the slow path. The consumer would then evaluate the constraints
on permuted trace rows, build a wrong quotient, and emit a proof rejected at exactly the AIR
that triggered the slow path. That is a per-matrix condition (`2^lb ≥ 2^lqd_i` depends only on
AIR *i*'s own degree), which predicts precisely the observed
`OodEvaluationMismatch { index: Some(1) }` — the chip, and only the chip, at lb=2 while the
degree-≤5 tables around it stay on the fast path and verify.

### 1.4c ⚑⚑⚑ CONFIRMED BY CONSTRUCTION. The floor is a bug. `[measured, 2026-08-13]`

Built standalone against the pinned rev and compared both paths against an independent
`coset_dft_batch` of the interpolated polynomial:

| path | matches natural order | matches bit-reversed | same value multiset |
|---|---|---|---|
| **fast**, target size 2^6 (fits) | **true** | false | true |
| **slow**, target size 2^7 (does not fit) | false | **true** | true |

**Correct values, wrong row order.** And end-to-end on a degree-7 AIR (`b = a⁷`) under
uni-stark:

```
log_blowup=2: lde.height=1024, quotient_domain.size=2048 => SLOW  verify: Err(OodEvaluationMismatch)
log_blowup=3: lde.height=2048, quotient_domain.size=2048 => FAST  verify: Ok
```

**Our measured symptom, reproduced from first principles.** `bit_reverse_rows` is an
**involution** (`matrix/src/bitrev.rs:84-100`), so only the *count* of applications matters;
the LDE is stored bit-reversed (`two_adic_pcs.rs:407-409`, *"We bit reverse as this is
required by our implementation of the FRI protocol"*); the fast path's prefix-then-reverse
cancels to natural order and the slow path's DFT-then-reverse does not. **One reversal too
many.** The fix is one inserted call at `two_adic_pcs.rs:479-480`:

```rust
    .coset_dft_batch(coeffs, domain.shift())
    .bit_reverse_rows()          // <-- add
    .to_row_major_matrix();
```

free for `Radix2DitParallel` (its `Evaluations` is already a `BitReversedMatrixView`, so the
added call just unwraps). **With the fix, `log_blowup = 2` verifies `Ok` — and a corrupted
trace still REJECTS on both paths**, so it restores correctness without weakening the check.

> ### **THE BLOWUP FLOOR IS NOT REAL.**
>
> `lb ≥ ⌈log₂(d−1)⌉` is not a soundness bound, not a mathematical necessity, and not a
> property of FRI. It is **one missing `.bit_reverse_rows()` in a crate we already vendor and
> already patch twice.** `lb = 2` and `lb = 1` are reachable **at BabyBear, at α = 7, today**,
> and **KoalaBear's entire claim on the blowup lever is void.**

### 1.4d Provenance, and three method findings that come with it

- **Upstream is still broken.** Present on `main` at `f5b7977e` (2026-08-13) and in **every
  published `p3-fri` through 0.6.3**. Introduced by **PR #1352 / `b9863b6b` (2026-03-02)** —
  the same commit that removed the old hard `assert!`. Untouched by the 7 commits to that file
  since our pin.
- **The fix is live and contested.** **PR #1982**, opened by an outside contributor ~6 hours
  before this measurement, is this exact one-line change, CI-green, and marked
  CHANGES_REQUESTED by maintainer `Nashtare`: *"you need a sufficiently large blowup factor
  for your constraint polynomial."* ⚑ That objection restates the symptom as the requirement —
  which is precisely the reading our own tree adopted.
- ⚑ **The test that was supposed to cover this takes the fast path.** PR #1352 added a test
  literally named **`extrapolation`**; its `create_disjoint_domain` yields `shift == GENERATOR`
  and `32 >= 16`, so **it never enters the branch it was written to cover.** A falsifier that
  never fired — the exact class in `minted-a-falsifier-that-stopped-falsifying`.
- ⚑⚑ **And we have frozen the symptom as a law.** `descriptor_ir2.rs:7173-7183` writes the bug
  up as a property of the S-box, and
  **`circuit/tests/fri_blowup_global_knob_survey.rs:685-690` ASSERTS that the refusal must
  happen**:
  > `assert!(!chip_refusals.is_empty(), "no chip-bearing descriptor refused at (2,57). Either
  > the chip S-box degree dropped … or no case in this grid pulls in the chip table.")`
  >
  **That assertion goes RED the moment the bug is fixed. Our gate currently locks the bug
  in.** It was written to stop someone claiming lb=2 was free; it now stops someone
  *discovering that it is*. The repair is to change what it asserts — from "the chip refuses"
  to "the chip's `lqd` is 3" — because the degree fact is the real invariant and the refusal
  was only ever its buggy shadow.

### 1.5 The floor is per-descriptor; the knob is global

`ir2_degree_budget` (`circuit/src/descriptor_ir2.rs:8566-8605`) freezes the per-table degrees.
Turning each into its floor:

| table | frozen degree | **its own lb floor** | moves at α = 3? |
|---|---:|---:|---|
| `main` @ `setFieldDynVmDescriptor2` | **8** | **3** | ✗ no — a Lean-emitted dynamic-slot gate, field-independent |
| `chip` (Poseidon2, inline `x⁷`) | **7** | **3** | ✅ **7 → 3, floor 3 → 1** |
| `map_ops` | 4 | 2 | ✗ no — in-tuple dir-mix lookup legs |
| `map_absent` | 4 | 2 | ✗ no |
| `main` (all others) | 3 | 1 | — |
| `byte`/`memory`/`boundary`/`umemory`/`umem_boundary`/`umem_boundary_cohort` | 3 | 1 | — |

`ir2_config()` is a `thread_local` built from six file-scope `const`s **with no
per-descriptor input** (`circuit/src/descriptor_ir2.rs:7211-7231`); a per-descriptor knob
does not exist and its own prerequisite (pinning `num_queries` in the recursion verifier) is
unbuilt. So the effective floor is the **max over the whole registry**:

> **BabyBear today: `max(3, 3, 2, 2, 1, …) = 3`.
> KoalaBear α = 3, everything else unchanged: `max(3, 1, 2, 2, 1, …) = 3` — UNCHANGED.
> KoalaBear α = 3 **plus** narrowing `setFieldDynVmDescriptor2`'s `main` from 8 to ≤ 5: **2**.
> Floor **1** additionally needs `map_ops`/`map_absent` from 4 down to 3.**

⚑ **This is the finding the brief asked for and it is not the expected one.** α = 3 does not
by itself make `lb = 2` legal for the deployed batch. It removes the *hash's* claim on the
floor, which is necessary and not sufficient. **The binding constraint after the field
change is a single Lean-emitted descriptor's slot gate.** That is good news — it is one
descriptor's constraint polynomial, authored in Lean, and lowering `d = 8 → 5` is a
constraint-authoring task, not a field flag day. But it must be sequenced *first*, or the
field migration buys zero blowup.

### 1.6 By construction

The tree already contains the sweep, and it uses **Lean-emitted descriptors, not
hand-written Rust AIRs** — so it confirms the derivation without touching the substrate law.

- `circuit/tests/pasta_sbox_program_proves.rs:638` `the_blowup_is_swept_at_parity_on_this_machine`
  — a 2^10-row chip-free machine, **max degree 3**, swept at
  `FRI_PARITY = [(6,19), (3,39), (2,57), (1,114)]`. Its docblock states the prediction
  (`max degree 3`, so `lb = 1` should be legal) and then *runs* it rather than arguing it.
  **Predicted floor 1 ⇒ all four points legal.**
- `circuit/tests/fri_blowup_global_knob_survey.rs` — the same ladder across the by-name
  registry, asserting that **at least one chip-bearing descriptor REFUSES at `lb = 2`**
  (`:680-695`). **Predicted floor 3 for `d ∈ {7,8}` ⇒ refusal at 2 and at 1, legality at 3.**
- `circuit-prove/tests/fri_hundred_bit_cutover.rs` measured the recursion leaf directly
  (2026-07-28): `lb3 arity8 q19` **RUNS**; `lb2 arity8 q19` and `lb2 arity8 q110`
  **UNRUNNABLE — `OodEvaluationMismatch { index: 1 }`**.

The three together span `d ∈ {3, 7, 8}` × `lb ∈ {1, 2, 3, 6}` and the outcomes match the
`⌈log₂(d−1)⌉` table in every cell. **The derivation is confirmed by construction on real
Lean-emitted descriptors; no new AIR was authored to test it.**

⚠ Two corrections to the in-tree record, found while checking:
- **"38 of 91 by-name goldens pull in the chip"** (`descriptor_ir2.rs:7179`) — the
  denominator is stale. The registry holds **132** goldens today. The census computes both
  numbers at run time and only `println!`s them; the only *asserted* form is existential
  ("at least one refuses"), and its guard is `files.len() >= 80`, which still passes at 132.
  **The registry grew by 45% invisibly.**
- No golden records a constraint degree. The four that contain the string `degree` carry
  `"sbox_degree":7` inside an embedded Poseidon2 *parameter* blob — a hash spec, not an AIR
  degree. Degrees are recovered at test time from p3 symbolic analysis.

---

## 2. The soundness, re-derived at the new blowup — and it moves the OTHER way

### 2.1 The calculator, reconstructed and validated against its own published table

`minidregg/Assurance/TwoRegimeQueryBudget.lean` puts the regime in the type. Its three
per-query error terms, written out so they can be evaluated by hand at any `(lb, q, pow)`.
With rate `ρ = 2^{−lb}`:

| regime | proximity `δ` | per-query error `1 − δ` | **bits per query** |
|---|---|---|---|
| **UDR** (proven, unique decoding) | `(1−ρ)/2` | `(1+ρ)/2` | **`1 − log₂(1+ρ)`** |
| **JBR** (idealised Johnson, BCIKS20 at `m→∞`) | `1 − √ρ` | `√ρ` | **`lb/2`** |
| CBR (**withdrawn**) | `1 − ρ` | `ρ` | `lb` |

and `bits = ⌊q · (bits per query) + pow⌋`.

**Validation — all five published rows reproduce EXACTLY, no fit, no fudge**
`[measured-here, scratchpad/kbmig_regimes.py]`:

| config | knobs | UDR | JBR | CBR |
|---|---|---|---|---|
| IR-v2 deployed | lb 6, q 19, pow 16 | 34 ✓ | 73 ✓ | 130 ✓ |
| recursion default | lb 3, q 38, pow 14 | 45 ✓ | 71 ✓ | 128 ✓ |
| v1 prod / ZK / BN254 outer | lb 3, q 38, pow 16 | 47 ✓ | 73 ✓ | 130 ✓ |
| IR-v2, child mints q=1 | lb 6, q 1, pow 16 | 16 ✓ | 19 ✓ | 22 ✓ |
| zkDTVM v0.8.0 | lb 1, q 261, pow 20 | **128 ✓** | 150 ✓ | 281 ✓ |

Two things fall straight out and neither was in the record:

- **The deployed security-parity ladder is a JBR-73 ladder.** `q = ⌈(73−16)/(lb/2)⌉` for
  `lb = 3..8` gives **38, 29, 23, 19, 17, 15** — exactly `FRI-PARAM-FRONTIER`'s ladder, and
  `(2,57)` and `(1,114)` are its next two rungs. The in-tree ladder was never labelled with
  its regime; it has one.
- **UDR bits/query saturates fast.** `1 − log₂(1+ρ)` is 0.415 at ρ=1/2, 0.678 at 1/4, 0.830
  at 1/8, and **0.978 at 1/64**. Above `lb ≈ 4` extra blowup buys essentially nothing in the
  proven regime — 0.913 → 0.994 across four rungs. **This is why the proven bar makes the
  blowup knob nearly free**, §2.3.

### 2.2 ⚑ The query column is not the binding column, and it moves the opposite way

`ir2_config`'s own docblock (`circuit/src/descriptor_ir2.rs:7188-7191`) already says this and
it has not been carried into any composition:

> `(6,19) → (2,57)`: capacity `130 → 130` and Johnson `73 → 73`, but per-fold `109 → 118` and
> commit-phase `ε_C` `71 → 77`. **At the deployed wrap `ε_C` binds BELOW Johnson**, so on the
> column that actually binds, the low-blowup rung is the STRONGER one. Reading "parity" as
> "identical security" is therefore wrong in both directions.

`λ ≥ min{−log₂ ε_C , query column} − 1` (ethSTARK 2021/582 eq. 20, as transcribed in
`PROVEN-120-CONFIG.md:112-127`). `ε_C` carries `1/(2ρ^{3/2}) = 2^{3·lb/2 − 1}` and `|D⁰|²`,
with `|D⁰| = max_height · 2^lb`. So **lowering the blowup buys commit bits at two slopes**:

    d(commitBits)/d(−lb)  =  3/2      at fixed |D⁰|        [derived, matches 71 → 77 over 4 rungs]
    d(commitBits)/d(−lb)  =  3/2 + 2  at fixed trace height [derived, matches 58 → 68 over 3 rungs]

Both anchors are in-tree measurements of the *same* formula under different `|D⁰|`
conventions, and both reproduce from `ε_C ∝ ρ^{−3/2}·|D⁰|²`. ⚠ The absolute anchor is
contested across documents — 51 / 57 / 58 / 71 appear for "the commit column" in
`PROVEN-120-CONFIG.md:196`, `:66-72`, `fri_hundred_bit_cutover.rs`, and
`descriptor_ir2.rs:7189` respectively, at different `m` and different `|D⁰|`. **The slope is
what this section uses and the slope is consistent; do not quote an absolute from here.**

Consequence, stated plainly — **and it is a `min`, so the gain caps**:

> **The deployed `lb = 6` is the WORST rung on the binding column.** At JBR-73 parity, moving
> the blowup down holds both query columns fixed by construction and **adds `ε_C`**. But
> `λ = min{ε_C, query} − 1`, so once `ε_C` climbs past the query column the query column takes
> over and further blowup drops buy nothing:
>
> | anchor | `lb = 6` | `lb = 3` | `lb = 2` |
> |---|---|---|---|
> | `ε_C` at the IR-v2 leaf (`dregg_fri_ledger`, fixed `|D⁰|`) | 71 | 75.5 | **77** |
> | `ε_C` at the wrap (fixed trace height, `|D⁰| = h·2^lb`) | 58 | **68** | 71.5 |
> | query column (JBR, held at parity) | 73 | 73 | 73 |
> | **composite `min`, leaf** | **71** | 73 | **73 (capped)** |
> | **composite `min`, wrap** | **58** | **68** | **71.5** |
>
> **The composite `λ` goes UP in every case** — by **+2 bits** at the leaf (where it saturates
> against the query column at `lb = 3`) and by **+10 to +13.5** at the wrap. **There is no rung
> at which lowering the blowup costs proven soundness.** ⚑ Anyone who has been reading the
> blowup drop as "trading security for speed" has the sign backwards; the trade is against
> **wire bytes and verifier time**, and only those.

### 2.3 The whole trade, computed

Prover model: per-phase from `notes/phase-profile.md` §2 (RAYON_NUM_THREADS=1, min of 21,
`pow=0`), fit as `cost = A + B·2^b` over the measured `b = 3..8` and extrapolated to `b = 1,2`;
the "naive" column instead halves the four `Θ(2^b)` phases per rung. **The band between them
is the honest uncertainty of the extrapolation.** Verifier model: `perms(q,b) = q·(176.6 + 6b)`,
calibrated on the measured permutation counts (4,040 at `(6,19)` — exact) at the measured
scalar rate 938 ns. Proof bytes: `q·(4408 + 468·b)`, fit to the two measured endpoints
220,874 B at `(3,38)` and 122,298 B at `(8,15)`.

**Independent validation of the cost model**: `descriptor_ir2.rs:7192-7196` reports that
`(6,19)` beats `(2,57)` "on EVERY measured descriptor by **2.0–2.4×** on both [wire bytes and
verify ms]". The model predicts **2.22× bytes and 2.66× verify** for that pair, from
parameters fit to entirely different measurements. `[measured-here]`

#### (a) At the deployed posture (JBR-73 parity)

| lb | q | prove ms (band) | speedup vs deployed | verify perms | verify ms (scalar) | proof KiB |
|---:|---:|---|---|---:|---:|---:|
| 1 | 114 | 3.9 – 9.5 | 7.3× – 18.1× | 20,820 | 19.5 | 543 |
| **2** | **57** | **6.0 – 11.4** | **6.2× – 11.8×** | 10,752 | 10.1 | 298 |
| **3** | **38** | **10.1 – 15.0** | **4.7× – 6.9×** | 7,396 | 6.9 | 216 |
| 4 | 29 | 18.2 – 22.3 | 3.1× – 3.9× | 5,818 | 5.5 | 178 |
| 5 | 23 | 36.8 – 37.1 | 1.9× | 4,753 | 4.5 | 152 |
| **6** | **19** | **65.9 – 70.0** | **1.0× (deployed)** | **4,040** | **3.8** | **134** |
| 8 | 15 | 234.7 – 240.6 | 0.30× | 3,369 | 3.2 | 119 |

This reproduces the in-tree verdict: at JBR-73 the wire really does get 2.2× worse at `lb=2`,
and **"6 stays" was a defensible call on the wire axis** — made, however, against an
*unmeasured* prover. The prover column now says that choice costs **6–12×**.

#### (b) ⚑ At the proven bar (UDR-100) the wire argument EVAPORATES

| lb | q | prove ms (band) | speedup vs deployed | verify perms | verify ms (scalar) | proof KiB |
|---:|---:|---|---|---:|---:|---:|
| 1 | 203 | 3.9 – 9.5 | 7.3× – 18.1× | 37,074 | 34.8 | 967 |
| **2** | **124** | **6.0 – 11.4** | **6.2× – 11.8×** | 23,390 | 21.9 | **647** |
| 3 | 102 | 10.1 – 15.0 | 4.7× – 6.9× | 19,852 | 18.6 | 579 |
| **4** | **93** | 18.2 – 22.3 | 3.1× – 3.9× | **18,659** | 17.5 | **570 ← min** |
| 5 | 88 | 36.8 – 37.1 | 1.9× | **18,184 ← min** | 17.1 | 580 |
| 6 | 86 | 65.9 – 70.0 | 1.0× | 18,286 | 17.2 | 606 |
| 8 | 85 | 234.7 – 240.6 | 0.30× | 19,094 | 17.9 | 677 |

**Read the two right-hand columns.** Across `lb = 2…8` at a fixed *proven* 100-bit bar, proof
size varies by **1.13×** (647 vs 570 KiB) and verifier hashing by **1.29×** (23.4k vs 18.2k
perms) — with shallow interior minima at lb=4 and lb=5 — while **prove time varies by 39×**.

> **At the proven bar the blowup knob is a prover knob and almost nothing else.** The
> mechanism is §2.1's saturation: a proven query is worth 0.68 bits at ρ=1/4 and 0.98 bits at
> ρ=1/64, so buying the same 84 bits costs 124 queries instead of 86 — 1.44× more queries,
> each carrying 4 fewer path nodes. The two effects nearly cancel on the wire. They do not
> cancel on the prover, where the LDE and the Merkle build are both `Θ(2^b)`.

**The whole "is lb=2 worth its soundness cost" question therefore has a different answer in
each regime**, and the repo's own doctrine (`VERDICTS` §2: *never quote 130*) puts us in the
regime where the answer is **yes, overwhelmingly**:

| move | prove | proof bytes | verify (scalar) | composite `λ = min{ε_C, query}` |
|---|---|---|---|---|
| deployed `(6,19)` → `(3,38)`, JBR-73 held | **4.7–6.9× (modelled)** | 1.6× bigger | 1.8× slower | **+2 (leaf) / +10 (wrap)** |
| deployed `(6,19)` → `(2,57)`, JBR-73 held | **1.7–13.1× MEASURED, §6.3** | 2.2× bigger | 2.7× slower | **+2 (leaf) / +13.5 (wrap)** |
| `(6,86)` → `(2,124)`, **UDR-100 held** | same as above | **1.07× bigger** | 1.28× slower | same |

⚑ **Reconciliation with the measurements in §6.3, which landed after this model was built.**
The model's `6.2–11.8×` band for `(6,19) → (2,57)` was fit to `phase-profile`'s IR-v2 batch,
whose committed tables are **2^3–2^6 rows**. Measured on real descriptors the spread is
**0.55× to 13.13×**, and it is *ordered by trace height*: 0.55× at 24 columns, 1.74× at 64
rows, 4.05× at 1024, **13.13× at 4096**. **The model brackets the middle and understates the
tall end**, because at small `h` the blowup-independent phases (quotient eval, lookup
permutation, residual — 1.8 ms of a 10 ms prove at `lb=3`) still dominate. Use §6.3's measured
numbers, not this band, for anything at 2^10 rows or above.

⚠ Named inadequacies of this table. (i) `lb = 1,2` prove times are **extrapolated**, not
measured — the band is the two extrapolation methods, and `prover-floor.md` warns its own
model over-predicts below lb=4. (ii) Prover query cost is held flat in `q`; measured it is
0.05–0.07 ms at q=19 (`open_batch` copies stored digests and hashes nothing), so it is small,
but the one q-varying pair in the profile — `(3,19)` at 10.3 ms vs `(3,38)` at 14.9 ms — is
larger than that and unexplained. **At q = 124 this is the term most likely to be wrong.**
(iii) The verifier column is scalar; the profile's §8 5× lane-batching headroom applies to
every row equally and would take the UDR-100 lb=2 verify from 21.9 ms to ~4.4 ms.

---

## 3. The composed total — and every factor in the brief's product is wrong in a different way

The brief proposes `hash rate 1.33× × blowup 2× × narrowing 2.83/2.24`. **All three factors
survive as facts and none of them survives as a factor in that product.** Taken in order.

### 3.1 The hash rate is 1.33× in COUNTED MULTIPLICATIONS and ~1.02× in WALL CLOCK

`0.301 vs 0.227` bits/op is a ratio of **op counts**, and the op count moves for a reason we
can reconstruct exactly. From the pinned plonky3 constants
(`baby-bear/src/poseidon2.rs:37,47`; `koala-bear/src/poseidon2.rs:37,52`):

| | BabyBear w16 | KoalaBear w16 |
|---|---:|---:|
| α (S-box degree) | **7** | **3** |
| full rounds `R_F` | 8 | 8 |
| **partial rounds `R_P`** | **13** | **20** |
| S-box multiplies (`x⁷` = 4 mults, `x³` = 2) | (8·16 + 13)·4 = **564** | (8·16 + 20)·2 = **296** |
| internal diagonal multiplies | 13·16 = 208 | 20·16 = 320 |
| **total ≈** | **772** | **616** |

`772/616 = 1.25×`, in the right neighbourhood of the quoted 1.33× and of `prover-floor`'s
independently derived 1.69×. **And the measured native wall-clock ratio is ~1.02×**
(`notes/field-choice-verdict.md`: *"measured at our pin, KoalaBear's Poseidon2 is only ~2%
faster natively"*).

> ⚑ **This is `VERDICTS` §4's wrong-unit error, a second time, on the other dominant term.**
> There, 78–308× was a counted-multiplication exchange rate whose wall-clock conversion had
> never been taken, and taking it moved the threshold by 8×. Here, 1.33× is a counted-mult
> hash ratio whose wall-clock conversion **was** taken — by the field memo, to ~1.02× — and
> the counted number kept being carried anyway. Native Poseidon2 throughput is bound by the
> linear layers, the Montgomery reductions and memory, not by the S-box multiply count, so
> halving the S-box multiplies buys ~2%.
>
> **The prover is hash-bound in NATIVE Poseidon2 (the Merkle commit, `phase-profile` §2).
> The multiplier that applies to that term is ~1.02×.**

⚠ And a cross-check in `notes/prover-floor.md` needs withdrawing: *"derived native
BabyBear/KoalaBear permutation ratio 1.69× vs the in-circuit measurement 1.82× — two
instruments, 4% apart."* **Those are not two instruments on one object.** 1.69× is native
multiplies per permutation; 1.82× is *committed AIR columns* per permutation (298 → 164).
They measure two different engines and their agreeing to 4% is a coincidence, not a
corroboration.

### 3.2 The blowup 2× is double-counted, and it is not KoalaBear's anyway

`prover-floor.md` states the composition in one sentence: *"the only figure of merit a hash
has is bits/op — 0.301 vs 0.227 — **and** α=3 makes lb=2 legal … **So the migration is ~3.4×
on the dominant term, not ~1.5×**."* **The ~3.4× IS `hash-rate × blowup`.** Multiplying it by
a further 2× for the blowup double-counts the blowup leg **by construction, in the source's
own sentence.** The brief's suspicion is confirmed at source.

Three further problems with that 3.4×, beyond the double-count:

1. **Its 1.5× half is an in-circuit number applied to a native term.** The 1.5× is
   `notes/hash-verdict.md` §5: `298 → 164 cols/perm = 1.82×`, *"~1.51× total at the 75%
   hashing share"* — that is the **recursion circuit's** committed-column cost. The
   "dominant term" it then multiplies is the **native Merkle build**. Two engines, one
   product.
2. **Its blowup half is not the field's** (§1.5): with the global knob and today's degree
   budget, α = 3 moves the registry floor `3 → 3`. The degree-8 `setFieldDynVmDescriptor2`
   main is what binds after the chip drops out.
3. **And it may not be anyone's** (§1.4b): if the floor is a row-order bug in the vendored
   `p3-fri`, `lb = 2` is a BabyBear config today.

### 3.3 The narrowing ratio is real, is 1.26× not 2.83×, and lands on a fraction of the row

`2.24× at BabyBear (α=7) → 2.83× at KoalaBear w16 (α=3)` is the in-AIR virtualization ratio
for the Poseidon2 chip's committed felts. **The 2.24× is available today at BabyBear**
(`VERDICTS` §4: *"strictly Pareto, no trade to price"*), so the KoalaBear-specific increment
is `2.83/2.24 = ` **1.263×**, which the brief has right.

What the brief does not say is where it lands. It is a **committed-width** ratio on **one
table**, and the mechanism that turns committed width into prover time is
`phase-profile` §6: the Merkle **leaf** is a `PaddingFreeSponge` over the whole committed
row, costing `⌈w/8⌉` permutations per row and scaling as `w·h·2^b`. So narrowing a table's
row buys native hash time **proportionally to that table's share of total committed width**.

**I measured that share** `[measured-here, 2026-08-13]`. `ir2_phase_profile::phase_profile_raw_spans`
at the deployed point prints the `dims` of every committed matrix in the IR-v2 transfer batch:

| committed matrix `w × h` | cells | cell % | leaf perms `⌈w/8⌉·h` | **leaf %** |
|---|---:|---:|---:|---:|
| **386 × 8** | 3,088 | 13.4% | 392 | **13.4%** |
| 236 × 64 | 15,104 | 65.7% | 1,920 | 65.4% |
| 72 × 64 | 4,608 | 20.0% | 576 | 19.6% |
| 12 × 8, 4 × 16, 2 × 16 | 192 | 0.8% | 48 | 1.5% |
| **total** | **22,992** | | **2,936** | |

**The `386 × 8` table is the Poseidon2 chip**, identified without ambiguity: its quotient is
split into **8 chunks** (`compute quotient>coset_lde_batch_with_transform[dims=4x8]`, 8
calls ⇒ `lqd = 3` ⇒ `d ∈ 6…9`), and `ir2_degree_budget` allows only `chip = 7` above degree 4
on a non-`setFieldDyn` descriptor. Every other table splits into 2 chunks (`lqd = 1`,
`d = 3`). Width 386 is also the right size for ~352 committed felts/permutation ×8
permutations plus overhead.

> **`s = 13.35%`.** So on the deployed batch:
>
> | lever | ratio on the chip | **factor on the whole batch's leaf hashing** |
> |---|---:|---:|
> | in-AIR virtualization at α = 7 (BabyBear, available today) | 2.24× | **1.080×** |
> | in-AIR virtualization at α = 3 (KoalaBear) | 2.83× | 1.094× |
> | **the KoalaBear-specific increment** | 1.263× | **1.029×** |

⚑ **1.029×, not 1.26×.** And the same measurement re-scopes a number already in `VERDICTS`:
the in-AIR virtualization result's **"2.11× prove"** is the *chip's own* prove, not the
batch's. On the deployed transfer batch the chip is an eighth of the committed cells, so the
whole-batch win is **~1.08×**. Both numbers are true; only one of them is about the deployed
prover.

⚠ **Scope, stated:** `s = 13.35%` is one descriptor — the deployed transfer batch, the one
`phase-profile` measured. Chip-heavy goldens (`poseidon2-hash-arity2`,
`merkle-membership-4ary-d4`) will run `s` far higher, and the **recursion engine** is ~75%
in-circuit Poseidon2, which is where the 1.82× actually bites. **The claim is not "the chip
is small"; it is "the chip is small in the workload that was profiled, and every whole-prover
multiplier quoted from a chip-only measurement needs its `s`."**

### 3.4 α = 3 also COSTS, and one of the costs is unresolved upstream

- **+7 partial rounds** (13 → 20). Priced into every number in §3.1 and §3.3 already; the
  net is still favourable because a degree-3 S-box evaluates inline where degree 7 needs a
  committed intermediate register.
- **Round-skipping margin roughly halves**, +286 bits → ~+143 (`VERDICTS` §1). Still far
  above any bar. Not a blocker.
- ⚑ **The KoalaBear-16 round count carries a discrepancy in upstream's own docblock, and
  BabyBear-16 does not.** `koala-bear/src/poseidon2.rs:39-52` derives the interpolation bound
  (Poseidon Eq. 3) as `R_interp ≥ ⌈128/log₂3⌉ + ⌈log₃16⌉ − 5 = 79`, adds the +7.5% margin to
  ~85 — and then ships **20**, with the note *"However, the official round number script
  yields `R_P = 20` for this configuration (matching the Grain LFSR parameters used to
  generate the round constants below)."* BabyBear-16's derivation
  (`R_GB ≥ 9 + 0.3562·min{7.53, 15.5} = 11.682`, `⌈1.075 × 11.682⌉ = 13`) closes cleanly.
  **We would be adopting a parameter set whose own upstream docblock records an unreconciled
  4× gap between one cited bound and the shipped value.** If 20 is right the note is stale;
  if 85 is right, every cost number above inverts and KoalaBear loses outright.
  **This must be settled before any migration, and it is exactly the place the brief already
  identifies as the highest-value site for named theorems instead of `#guard`s.**

### 3.5 The composition, done honestly — three engines, three ledgers

The single biggest error in the existing composition is treating one number as "the prover".
There are three engines and KoalaBear pays differently in each.

| | **A — native leaf prover** | **B — recursion / in-circuit verifier** | **C — the blowup ladder** |
|---|---|---|---|
| what it is | the object `phase-profile` measured: LDE + Merkle at `h = 2^3…2^12` | the wrap / leaf-wrap tower, `h = 2^16…2^20`, ~75% in-circuit Poseidon2 | the `lb` knob itself |
| KoalaBear hash factor | **~1.02×** (measured native wall clock) | **1.82×** hashing → **~1.51×** total | — |
| KoalaBear narrowing factor | **1.029×** (§3.3, at the measured `s = 13.35%`) | inside the 1.82× | — |
| KoalaBear blowup factor | **1.0×** (§1.5: floor unchanged at 3) | **1.0×** | — |
| **KoalaBear-specific total** | **≈ 1.05×** | **≈ 1.5×** | **1.0×** |
| field-independent lever sitting in the same place | in-AIR virtualization **1.08×** on this batch (2.11× on the chip alone) | same | `6 → 3` = **4.7–6.9×**, `6 → 2` = **13.1× measured at 2^12 rows**, legal today |

> **The composed KoalaBear total on the engine the profiling lane measured is ≈ 1.05×** —
> `1.02 × 1.029` — **not ~3.4× and not ~7×.** On the recursion engine it is ~1.5×. **And
> sitting beside it, in the same tree, requiring no field change, is a measured 13.1×** (§6.3).
>
> The brief's product `1.33 × 2 × 1.263 = 3.36×` and the measured composition `1.02 × 1.00 ×
> 1.029 = 1.05×` differ by **3.2×**, and every bit of the difference is one of the three
> errors: a counted-mult ratio quoted as wall clock, a blowup lever that belongs to the
> descriptor budget and not the field, and a chip-only ratio quoted as a batch multiplier.
>
> ⚑ **The field migration is the smallest of the three levers, and it is the only one that
> costs a flag day.** That is the inversion this lane was sent to check for, and it is real.

---

## 4. ⚑ The constraint nobody put in the product: KoalaBear does not ENABLE the blowup drop, it MANDATES one

`fri_blowup_global_knob_survey::the_row_ceiling_is_two_adicity_minus_log_blowup`, run here
`[measured-here, 2026-08-13]`:

```
═══ §3  THE ROW CEILING (BabyBear two-adicity = 27) ═══
 lb    q  max log_rows          max rows
  6   19            21           2097152
  4   29            23           8388608
  3   39            24          16777216
  2   57            25          33554432
```

    max trace rows  =  2^(TWO_ADICITY − log_blowup)                            [derived, enforced]

and it *is* enforced, unlike the degree floor — `monty-31/src/monty_31.rs:681`
`assert!(bits <= Self::TWO_ADICITY)` panics loudly.

**BabyBear's two-adicity is 27. KoalaBear's is 24.** (`15·2²⁷+1` vs `127·2²⁴+1`.) So the same
table, transposed to the migration target:

| `log_blowup` | max rows @ BabyBear (2-adicity 27) | max rows @ **KoalaBear (2-adicity 24)** |
|---:|---:|---:|
| 6 | 2^21 | **2^18** |
| 4 | 2^23 | 2^20 |
| **3** | 2^24 | **2^21** |
| 2 | 2^25 | 2^22 |

The in-AIR Kimchi/Wrap verifier **pads to exactly 2^21 rows**
(`notes/field-choice-verdict.md`, "Hard prerequisite"). Therefore:

> **KoalaBear at `lb = 6` cannot hold the deployed wrap. It is short by 3 bits of trace
> height. `lb ≤ 3` is a HARD REQUIREMENT of the migration, not an option it unlocks.**

Combine with §1.5's floor (`lb ≥ 3`, set by `setFieldDynVmDescriptor2`'s degree-8 main, which
α = 3 does not move):

> **At KoalaBear, with today's degree budget, `log_blowup = 3` is the ONLY legal value.
> Floor 3 from the quotient degree, ceiling 3 from the two-adicity. The knob has exactly one
> position.**

Two consequences, and they point opposite ways.

1. **The whole measured KoalaBear speedup is the blowup drop, and the blowup drop is
   BabyBear's to take.** The migration's headline "~3.4×" is dominated by `6 → 3`
   (4.7–6.9× measured on the leaf, 6.4× on the wrap) — a move that is legal at BabyBear
   today, changes no field, rotates no VK, and *raises* the binding soundness column. Attribute
   it correctly and KoalaBear's own contribution is §3.5's 1.0–1.3× on the leaf, ~1.5× on the
   wrap.
2. **But it also means the migration is not optional-in-parts.** You cannot migrate the field
   and leave `lb = 6`; the wrap will not fit. So a KoalaBear flag day *forces* a blowup flag
   day — which means it forces every re-emit in §6 to happen at once, and it forfeits the
   `lb = 2` rung permanently unless the degree-8 main comes down first.

⚑ **Sequencing falls straight out of this and it is the opposite of the brief's ordering:**

> **1. Drop `lb 6 → 3` at BabyBear.** Legal today; 4.7–6.9× measured; +4.5 to +10 bits on the
>    binding column; costs 1.6× wire at JBR-73 and ~nothing at UDR-100.
> **2. Land in-AIR virtualization of the Poseidon2 chip at α = 7.** 2.11× prove, strictly
>    Pareto, no field change (`VERDICTS` §4).
> **3. Bring `setFieldDynVmDescriptor2`'s `main` from `d = 8` to `d ≤ 5`** — one Lean-emitted
>    constraint polynomial. This is what actually buys `lb = 2`, at either field.
> **4. Settle §1.4b** (is the floor a row-order bug?). If yes, steps 1–3 all get cheaper and
>    `lb = 1` comes into range at α = 7.
> **5. Then, and only then, KoalaBear** — for its ~1.5× on the recursion engine, in a tree
>    that has already taken the free 5–7×, at an `lb` the migration will pin to 3 anyway.

---

## 5. The `d = 5` tension — RESOLVED, and the first correction is to the letter `d`

`VERDICTS` §7.9: *"Plonky3's `p3-security` says d=5 reaches 128 with KoalaBear; our
`PROVEN-120-CONFIG.md` says d=5 cannot reach 120. Probably a scope difference (RS proximity
leg vs whole apex composite) — check, do not guess."* Checked. **Not a contradiction, and the
brief's guessed reason is not the reason.**

### 5.1 `d` is the EXTENSION degree on both sides. Neither is a constraint degree.

- **PROVEN-120-CONFIG**: `d = 8` is its recommendation and *"the deployed `d = 4` stands"* —
  BabyBear quartic, `4 × 30.907 = 123.63` bits. `d = 5` is **Ext5**, `154.5` bits. The
  mechanism it gives is `ε_C ∝ 1/p^extDeg`, and *"only the extension degree moves the
  ceiling, at `log₂ p = 30.91` bits/degree."*
- **Plonky3**: the KoalaBear/128 line is `whir/src/parameters/soundness.rs:600-605`:
  ```rust
  /// Equals `5 * ceil(log_2(p_KoalaBear))` with `p_KoalaBear = 2^31 - 2^24 + 1`,
  /// i.e. a degree-5 extension of the KoalaBear prime field.
  const KOALABEAR_QUINTIC_BITS: usize = 155;
  ```

**Both are quintic extension fields at ~155 bits.** The constraint-degree reading that the
`VERDICTS` phrasing invites — and that this lane's brief carried forward as "α=3 / d=5 /
lb=2" — is a **name collision**, the `A Display Name Is Not A Key` class in a soundness
document. ⚑ `VERDICTS` §7.9 should read **"Ext5"**, not "d=5".

### 5.2 There is no `p3-security` crate

`https://crates.io/api/v1/crates/p3-security` → **404**; no `security` member in the pinned
workspace. What exists is a **module**, `uni-stark/src/security.rs` (647 lines, added between
`cf7bd91` and `82cfad7`). Its `ConjecturedSecurity` is FRI-query-only (2025/2010 §1.5 "random
words"); its `ProvenSecurity` is a round-by-round composite over ALI + DEEP + FRI commit +
FRI query in two regimes. **Neither is reachable from `prove` or `verify`** — the only callers
are `Proof::conjectured_security` / `Proof::proven_security` and an example reporter.

### 5.3 The four real differences

| | **PROVEN-120-CONFIG (ours)** | **plonky3 WHIR test** |
|---|---|---|
| protocol | **FRI**, DEEP-ALI | **WHIR**, constrained-RS |
| commit-phase theorem | **BCIKS20 (2020/654) Thm 8.3** | **BCSS25 (2025/2055)**, `O(n²/η⁷) → O(n/η⁵)` |
| Johnson parameter `m` | **3** | **10** (`η = √ρ/20`) |
| rate | `lb = 3…6`, ρ = 1/8…1/64 | `log_inv_rate = 2`, **ρ = 1/4** |
| trace | `T = 2^6 … 2^16` | `log_degree = 20` |
| may PoW top up the commit leg? | **NO** — `query_and_pow_cannot_pass_epsC` is a theorem; `ε_C` contains neither `q` nor `pow` | **YES** on 3 of 5 legs (`prox_gap`, `sumcheck`, `combination` need only ≥ 98 with `MAX_POW_BITS = 30`); `ood` and `query` must self-sustain at 128 |
| result at Ext5 | ceiling **98** at the apex, **118** at its best corner | **128** |

**Both statements are true of what they are about.** The gap is not "one leg vs the whole
composite" — both are composites. It is: **a different protocol, analysed with a
five-year-newer proximity theorem, at three times the `m`, at a rate sixteen times looser,
with grinding admitted on three legs we prove grinding cannot reach.**

### 5.4 ⚑ The finding that survives the resolution: our commit bound is from 2020

The one comparable, actionable item is the theorem vintage. Plonky3's own `ProvenSecurity`
list-decoding regime uses the 2025 bound for **FRI**, not just WHIR
(`uni-stark/src/security.rs:427-511`, citing 2025/2055 Thm 4.2 and 2024/1553 Thms 2 & 3):

```rust
let num = (2.0 * pow(m_shifted, 5.0) + 3.0 * m_shifted * pp * rho) * n;
let den = 3.0 * rho * sqrt_rho;
let epsilon_linear = num / den + m_shifted / sqrt_rho;
```

Ours (`FriLedger.friCommitLedger`) transcribes **BCIKS20 Thm 8.3**. The improvement plonky3
credits — `O(n²/η⁷)` → `O(n/η⁵)` exceptional points — is worth `≈ log₂(n) + 5.78` bits
(`whir/src/parameters/soundness.rs:580-590`), i.e. **~28 bits at our apex `|D⁰| = 2^22`**.

> **`ε_C` is the column that BINDS at our deployed wrap** (§2.2, and `descriptor_ir2.rs:7190`
> says so outright). It reads 51–58 bits. If the 2025 bound transfers to our FRI ledger the
> way plonky3 has already transferred it, **the binding column moves by roughly the size of
> the entire gap `PROVEN-120-CONFIG` was trying to close with an extension-degree flag day.**
>
> **`PROVEN-120-CONFIG`'s conclusion — "`d = 8` is the only answer" — is a verdict priced
> against a 2020 bound, and the resource it prices may have moved.** That is the
> *a-cost-verdict-outlives-its-premise* class, and it is the single most valuable thing this
> lane found that is not about blowup: **re-derive `friCommitLedger` on 2025/2055 BEFORE
> anyone buys an Ext5/Ext8 flag day.**

⚠ `[derived from source-reading, numeric comparison in flight]`. Two named risks: (i) the
2025 improvement is stated for WHIR's constrained-RS setting and its transfer to the FRI
commit phase is exactly the kind of step that must be checked and not assumed — though
plonky3 has already made that transfer in `ProvenSecurity`, which is evidence it holds; (ii)
our ledger is a machine-checked Lean object and swapping its bound is real proof work, not a
constant edit.

---

## 6. ⚑ MEASURED HERE, on twelve real descriptors: the floor predicts every cell, and the blowup lever grows with the trace

`circuit/tests/fri_blowup_global_knob_survey.rs::every_provable_descriptor_at_every_parity_point`,
release, `--ignored`, this box, load 29, 2026-08-13. Real proofs, real verifies, real
serialization at every rung of the JBR-73 parity ladder. **No AIR was authored to run this —
every case is a Lean-emitted descriptor from the by-name registry.**

### 6.1 The floor, by construction — 12/12 cells match `⌈log₂(d−1)⌉`

| descriptor | chip (`d = 7`)? | **measured floor** | predicted `⌈log₂(d−1)⌉` |
|---|---|---:|---:|
| `poseidon2-hash-arity2`, `turn-chain-binding`, `blinded-membership`, `merkle-membership-binary-d4`, `attested-fact-membership`, `merkle-membership-4ary-d4` | **yes** | **3** | `⌈log₂6⌉ = 3` ✓ |
| `presentation-freshness`, `delegate-scope-v2`, `pasta-fpadd-sound@64`, `pasta-rcb-windowed@1024`, `pasta-fpmul-sound@{64,4096}` | no (`d ≤ 4`) | **≤ 2** | `⌈log₂3⌉ = 2` ✓ |

Every chip-bearing descriptor refuses at `(2,57)` with
`OodEvaluationMismatch { index: Some(1) }`; every chip-free one proves and verifies there.
**The derivation is confirmed on real objects, and the chip's degree 7 is the only thing
separating the two groups.** ⚠ "≤ 2" because the ladder's lowest rung is 2; the true floor for
the `d ≤ 3` members is 1, which `pasta_sbox_program_proves.rs` reaches separately.

### 6.2 The census, re-measured: **43 of 132**, not 38 of 91

```
43 of 132 goldens pull in the Poseidon2 chip table … Predicted total extra wire
across the 89 chip-FREE goldens: 144.8 MiB per proof-set.
```

**Two thirds of the by-name registry (89/132) can run at `lb = 2` TODAY, at BabyBear,
at α = 7.** The in-tree docblock's "38 of 91" is stale in both numbers, and nothing asserts
either (the census `println!`s them behind a `files.len() >= 80` floor that still passes at
132).

### 6.3 ⚑ The measured trade — and the lever GROWS with trace height

`(6,19) → (2,57)`, both at JBR-73:

| descriptor | rows | committed cols | prove @ (6,19) | prove @ (2,57) | **prove speedup** | bytes ratio | verify ratio |
|---|---:|---:|---:|---:|---:|---:|---:|
| `delegate-scope-v2` | — | 24 | | | **0.55× (SLOWER)** | 1.46× | 2.23× |
| `pasta-fpmul-sound@64` | 64 | 694 | 363.5 ms | 208.5 ms | **1.74×** | 2.33× | 0.71× |
| `pasta-fpadd-sound@64` | 64 | 384 | 299.7 ms | 108.8 ms | **2.75×** | 2.27× | 2.37× |
| `pasta-rcb-windowed@1024` | 1024 | 525 | 617.2 ms | 152.5 ms | **4.05×** | 2.26× | 2.29× |
| `presentation-freshness` | — | 43 | | | **5.01×** | 1.95× | 2.05× |
| **`pasta-fpmul-sound@4096`** | **4096** | 694 | **10,592.8 ms** | **807.0 ms** | **13.13×** | 2.36× | 1.98× |

The same descriptor at two heights: **1.74× at 64 rows, 13.13× at 4096 rows.** And its full
ladder is monotone — `10,592.8 / 1,662.6 / 1,064.5 / 807.0 ms` at `lb = 6/4/3/2` — even at
`pow = 16`, where the grind's exponential draw (mean ~12 ms, tail past 40) is swamped.

> ⚑ **This settles why `lb = 6` ever looked right, and why it stops being right.**
> `PROOF-ECONOMICS.md` §2c justified it on the premise *"IR-v2's committed tables are TINY
> (2³–2⁸ rows), so the prover-side LDE cost of high blowup is milliseconds."* **At 2³–2⁸ rows
> that premise is TRUE — measured, 0.55–2.75×, and `delegate-scope-v2` is genuinely slower at
> `lb = 2`.** At 2^12 rows it is false by 13×. The deployed knob is correct for the registry
> we have and wrong by an order of magnitude for the one this research programme is heading
> toward: **zkML traces are 2^16–2^20, four to eight rungs past the point where the trade
> already flipped.**
>
> This is also the clean confirmation of `phase-profile` §6's mechanism from the other side:
> the Merkle leaf is a sponge over the whole committed row, so hash work scales `w·h·2^b` and
> the blowup lever is worth `Θ(2^b)` *only once `h` is large enough to leave the flat phases
> behind*.

**And this re-prices the whole KoalaBear question one more time.** §3.5 put the migration's
own contribution at 1.0–1.3× on the leaf prover. The lever sitting beside it, at BabyBear, on
the workload class we are building for, is **13× measured and rising with height.**

---

## 7. The flag day, if it happens

Written as `CLAUDE.md` requires: **what re-emits, what rotates, what refuses to load.** Nothing
here is a reason to defer — a rebuild is the answer and we re-genesis constantly. It is a
reason to do the whole thing at once, because §4 shows the parts are not separable.

### 7.1 The field constants — everything below moves together or not at all

| site | today | after |
|---|---|---|
| `circuit/src/field.rs:3` | `2013265921 = 15·2²⁷+1` | `2130706433 = 127·2²⁴+1` |
| `minidregg/prover/src/babybear.rs:4` | same, 2-adicity **27** | 2-adicity **24** |
| `minidregg/prover/src/field6.rs` | `BabyBear[u]/(u⁶−31)` | **new irreducible required** — `u⁶−31` is a BabyBear fact |
| `Selvage/SmallField.lean:6` | *"DEPLOYED base field is BabyBear"* | rewrite |
| `MixedFieldBudget.lean:97` | `babyBear := 2013265921` | new constant + every budget theorem re-checked |
| Ext4 binomial non-residue | BabyBear's | KoalaBear's — different element, different `Ext4` arithmetic |

Field size: `log₂ p` goes **30.9069 → 30.9887**, so `Ext4` goes `123.63 → 123.96` bits
(**+0.33**) and the LogUp wall `96 → 96.3`. **The extension-degree walls do not move.**
Anyone hoping the field change buys soundness should read that row twice: it buys a third of
a bit.

### 7.2 What ROTATES

- **Every VK.** The recursion VK fingerprint hashes circuit *shape*; the shape changes (α, R_P,
  the S-box register). Apex VK, wrap VK, leaf-wrap VK, the gnark outer wrap, the Mina config.
- **`CANONICAL_STATE_SCHEMA_EPOCH`**, and `PersistentStore`'s re-genesis gate. The devnet is
  wiped; that costs nothing and has been done twice in a day.
- **The nullifier / VK-epoch flip** rides this (`project-vk-epoch-nullifier-flip`).

### 7.3 What RE-EMITS

- **All 132 by-name descriptor goldens** (`circuit/descriptors/by-name/`) — measured here, §6.2.
  Their constraint polynomials are field-generic in shape but their *fixtures* and fingerprints
  are not.
- **The registry commitment.** `VERDICTS` §5: *"the registry commitment as shipped is a checksum
  no prover can open"* — the re-emit is the moment to make it Poseidon2 over the field-element
  encoding at an openable leaf granularity, because it has to be rebuilt anyway.
- **Every checked-in trace fixture** (`circuit/tests/fixtures/*.txt` — field elements as
  decimal `u32`; values ≥ 2013265921 are legal BabyBear-canonical only by accident).
- **Every proof on the wire.** Proofs are already not interchangeable across configs
  (`descriptor_ir2.rs`: *"FRI shape + Fiat–Shamir differ"*); this makes them not
  interchangeable across fields either.

### 7.4 What must REFUSE TO LOAD

Per doctrine, the old shape refuses rather than reinterprets:

- A BabyBear-canonical field element ≥ `2130706433` is **not representable** and must be a
  parse refusal, not a reduction. (The 117 million-value window between the two primes is
  exactly where a silent `%` would corrupt.) ⚑ This is the sharpest one: **the two primes are
  close enough that most values round-trip and a reduction bug would be almost invisible.**
- Any descriptor, VK, proof, or fixture carrying the old fingerprint.
- Any `log_blowup > 3` config (§4 — the two-adicity ceiling makes it unprovable at the wrap,
  and the failure mode is a *panic* there, `monty_31.rs:681`, which is the good case).

### 7.5 What rides along for free, and should

- **The Poseidon2 2026/306 transpose fix.** Our deployed internal linear layer is the attacked
  non-MDS shape; the fix is `M̄_ε = M₄ ⊗ P_{t/4}`, same fast matmul, **not shipped in any
  Plonky3** (`notes/hash-verdict.md` §3). Free *if* a permutation flag day happens anyway; it
  does not justify one.
- **A refusal for the degree/blowup relation** (§1.3). `instance_degrees(desc)` already exists;
  wiring it into the prove entry point turns a silently invalid proof into a named error.
- **Lane-batching the verifier's query paths** (`phase-profile` §8) — a 5×, no wire change,
  independent of field. Not part of the flag day; listed so it is not forgotten.

### 7.6 What does NOT move

- **BAT / CROSS's `K = 4`.** Both primes are 31-bit, so `⌈31/8⌉ = 4` is unchanged and the
  basis-aligned transform transfers with zero modification (`VERDICTS` §4b).
- **The BFV limb legality.** Both `2013265921` and `2130706433` are `≡ 1 mod 8192`
  (`notes/koalabear-limb-verdict.md`), so the RNS tower stays legal — and a KoalaBear limb
  under a KoalaBear prover is the *aligned* configuration the seam rule wants, which is the
  one place the migration strictly improves a design that is currently forbidden.
- **`SpongeIndiff` and the Merkle mode.** minidregg's sponge indifferentiability is parametric
  over the permutation, so a permutation swap costs **zero formal work** (`hash-verdict` §6).
- **The three query-regime formulas** (§2.1). They take `ρ`, `q`, `pow` — no field.

---

## 8. What this decides

1. **`lb = 2` is legal at α = 3 — and that is not what unblocks it.** The floor is
   `⌈log₂(d−1)⌉` over the whole registry under a global knob. α = 3 takes the chip out of the
   ceiling and leaves `setFieldDynVmDescriptor2`'s degree-8 `main` sitting in it, so the
   registry floor stays at **3**. The thing that buys `lb = 2` is **one Lean-authored
   constraint polynomial coming down from degree 8**, at either field.

2. **The blowup ladder is the lever, it is BabyBear's, and it is worth 13× at 2^12 rows.**
   Measured today: `(6,19) → (2,57)` at JBR-73 parity is 13.13× faster to prove on
   `pasta-fpmul-sound@4096`, 4.05× at 1024 rows, 1.74× at 64 rows, 0.55× on a 24-column
   descriptor. **The lever scales with trace height**, and the deployed registry
   (2^3–2^6 rows) is precisely the regime where `lb = 6` was a correct call. zkML is not.

3. **Lowering the blowup does not cost proven soundness — it BUYS it.** `ε_C ∝ ρ^{−3/2}·|D⁰|²`,
   so the composite `min{ε_C, query}` rises by +2 bits at the leaf and +10 to +13.5 at the
   wrap. The cost is entirely wire bytes and verifier hashing. **And at the proven bar
   (UDR-100) even that cost nearly vanishes**: proof size varies 1.13× and verifier hashing
   1.29× across `lb = 2…8`, while prove time varies 39×.

4. **The composed KoalaBear total is ≈1.05× on the leaf prover, ~1.5× on the recursion
   engine — not 3.4×.** Three independent scope errors produced the larger number, and each
   is now located: counted-mults quoted as wall clock (§3.1), a blowup leg double-counted and
   misattributed (§3.2), a chip-only ratio applied to a batch where `s = 13.35%` (§3.3).

5. **KoalaBear MANDATES `lb ≤ 3`** — two-adicity 24 against a `2^21` wrap. With the floor at 3,
   **the migration pins `log_blowup = 3` exactly.** It cannot be done half-way and it forfeits
   `lb = 2` unless the degree-8 main comes down first.

6. **The `d = 5` tension is a name collision, resolved.** Both `d`s are the *extension* degree.
   `p3-security` is not a crate; the KoalaBear/128 line is **WHIR's** quintic extension at
   ρ=1/4, m=10, on the 2025 proximity bound, with grinding admitted on three legs. Ours is
   **FRI** at m=3 on BCIKS20 (2020) with grinding proved unable to touch `ε_C`. Both true.
   ⚑ `VERDICTS` §7.9 should say **"Ext5"**.

7. ⚑ **Our commit-phase bound is five years old and it is the binding column.** plonky3 has
   already transferred BCHKS25/BCSS25 (2025/2055) into its FRI `ProvenSecurity`; our
   `FriLedger.friCommitLedger` is BCIKS20 Thm 8.3. The credited improvement is
   `≈ log₂(n) + 5.78` bits ≈ **28 at our apex**. **Re-derive the ledger before anyone buys an
   extension-degree flag day** — `PROVEN-120-CONFIG`'s "d = 8 is the only answer" is priced
   against the old bound.

8. ⚑ **The degree/blowup relation is stated three times in our tree and four times upstream,
   and checked nowhere on the proving path.** The one real check
   (`uni-stark/src/security.rs:244`) is a `debug_assert!` in a calculator `prove` never calls,
   and upstream *removed* the hard `assert!` that used to catch it — turning a loud panic into
   a silently invalid proof. `instance_degrees(desc)` exists; wiring it into the prove entry
   point is small and turns an 18-minute apex mystery into a named refusal.

9. ⚑⚑⚑ **And items 1–8 were all written before the floor turned out to be a bug** (§1.4c).
   With the one-line `p3-fri` fix, `lb = 2` and `lb = 1` are BabyBear configs at α = 7, the
   degree-8 `main` stops mattering for the blowup, and **the only thing KoalaBear still buys
   is a 4× smaller quotient on a table that is 13.35% of committed width — while making that
   table 4.5% wider (§10) and pinning `lb = 3` by two-adicity (§4).**

### The order to do them in — REVISED after §1.4c and §10

> **1. Fix `two_adic_pcs.rs:479` in the vendored `p3-fri`** — one inserted
>    `.bit_reverse_rows()`, free at `Radix2DitParallel`. Then **repair
>    `fri_blowup_global_knob_survey.rs:685-690`**, which currently asserts the bug's symptom
>    and will go red. Assert the *degree* invariant (`chip`'s `lqd` is 3), not the refusal.
>    ⚑ **Do this first: it is the cheapest item on the list and it unblocks every other one.**
> **2. Re-run the whole parity ladder** — `(2,57)` and `(1,114)` on the 43 chip-bearing
>    goldens, which have never been measurable. §6.3 says to expect the largest wins on the
>    tallest traces.
> **3. Drop the blowup.** `6 → 2` measured at up to 13.13× today on chip-free descriptors;
>    soundness-positive on the binding column; nearly free on the wire at UDR-100.
> **4. Report the bug upstream / support PR #1982**, whose one-line fix is CI-green and
>    currently CHANGES_REQUESTED on the grounds that the symptom is the requirement.
> **5. Consolidate the 50 modulus declarations into one** (§11.1). Field-independent, and it
>    is what makes any future field change a rename instead of a campaign.
> **6. Re-derive `friCommitLedger` on 2025/2055** — +17–21 real bits on the binding column
>    (§12) — *and put the [Sta25]-personal-communication caveat in front of ember, because
>    that is a citation-strength judgement, not arithmetic.*
> **7. Land in-AIR virtualization of the chip at α = 7** (2.11× on the chip, 1.08× on the
>    deployed batch; Pareto).
> **8. Turn `Poseidon2BabyBearW16.lean`'s six `#guard`s into named theorems** —
>    `by native_decide` + `#assert_compiled`, since the perm is a reduction bomb for `decide`.
>    Do it at BabyBear, now, so the *method* is settled before any constant moves.
> **9. KoalaBear: NOT RECOMMENDED on this evidence.** ≈1.05× on the leaf prover, a chip that
>    gets wider, `Ext6` that stops existing, `X⁴−11` that silently becomes reducible, a
>    two-adicity that pins `lb = 3`, and an upstream round-count discrepancy unresolved in its
>    own docblock. **Revisit only if (a) the recursion engine is profiled and the ~1.5× is
>    confirmed on a measurement rather than a citation, and (b) the `R_P = 20` vs 85 question
>    is settled.** Those two are the whole remaining case.

## 9. Named inadequacies

- **§1.4b is derived from source, not measured.** It is the highest-leverage item here and it
  could invert §1 entirely. One named experiment settles it.
- **`lb = 1, 2` prove times in §2.3 are extrapolated**; §6.3 supersedes them with measurements
  and shows the model understates at large `h`.
- **The verifier and proof-size models in §2.3 are fits**, calibrated on 2 and 5 points
  respectively. They reproduce the deployed permutation count exactly (4,040) and the in-tree
  `2.0–2.4×` wire/verify verdict, which is two independent checks, but they are fits.
- **`s = 13.35%` is one descriptor.** Chip-heavy goldens and the recursion tower differ.
- **All prove times were taken on a load-29 shared box.** Ratios are the deliverable.
- **The `m` used by our ledger (3) and by plonky3's LDR (searched 3..1000) differ**, so §5.4's
  bit comparison is not apples-to-apples until it is evaluated at matched `m`. In flight.
- **The recursion engine is not measured anywhere in this note.** Every claim about it
  (~1.5×, 75% hashing, `h = 2^16–2^20`) is cited, not taken. `phase-profile` §0 blind spot 6
  says the same. **That is the engine KoalaBear actually helps, and it is the one nobody has
  profiled.** ⚑ Cheapest high-value next measurement.

---

## 10. ⚑⚑⚑ THE INVERSION: both published narrowing ratios are `R_P` in disguise, and the absolute result goes the WRONG WAY

This landed last and it is the most important thing in the note. `VERDICTS` §4 carries:

> *"352 → 157 felts … 2.11× prove, 2.34× committed cells … **And the ratio GROWS as α falls**
> (2.24× BabyBear → 2.83× KoalaBear w16), so the field question gets a second answer pointing
> the same way."*

The Lean census supplies the missing cell. `Dregg2/Circuit/Emit/Poseidon2RoundGates.lean`
pins `INTERNAL_ROUNDS := 13`, `SBOX_ALPHA := 7`, `#guard POSEIDON2_AUX_COLS == 352` — and at
KoalaBear's `R_P = 20` that same emitter yields **464**. With that, both ratios fall out of one
line of arithmetic `[derived, exact]`:

    un-virtualized:  16 · (1 + R_F + R_P)          — commit the whole state after every round
    virtualized:     16 + 8·16 + R_P               — commit only what a NONLINEARITY consumes

| | `R_P` | un-virtualized | **virtualized** | narrowing ratio |
|---|---:|---:|---:|---:|
| **BabyBear α = 7** | 13 | `16·22 =` **352** ✓ *(Lean `#guard`)* | `16+128+13 =` **157** ✓ *(VERDICTS)* | `352/157 =` **2.242×** ✓ *(published 2.24)* |
| **KoalaBear α = 3** | 20 | `16·29 =` **464** | `16+128+20 =` **164** ✓ *(hash-verdict)* | `464/164 =` **2.829×** ✓ *(published 2.83)* |

**Four in-tree numbers — 352, 157, 164, and the two ratios — reproduce to three digits from
`R_P` alone.** The formula is not fitted; it is the round structure.

And now read the column that matters:

> ### **157 → 164. KoalaBear's Poseidon2 chip is 4.5% WIDER after virtualization, and 31.8% wider before it.**
>
> **The narrowing ratio grew because the BASELINE got worse, not because the RESULT improved.**
> `2.24 → 2.83` is `352 → 464` in the numerator. At *no* virtualization level is KoalaBear's
> committed chip narrower than BabyBear's.

⚑ This is the ratio-vs-absolute error, on the one number that was doing the most work in the
migration's favour. `VERDICTS` §4's *"the field question gets a second answer pointing the
same way"* — **the second answer points the other way.** More partial rounds is a *cost*
(the brief flagged exactly this: *"⚠ Also price what α=3 costs: more partial rounds means more
rows"*), and it does not merely offset the α win, it **exceeds** it: `R_P` grows by 7 while
the per-S-box saving in committed cells is zero, because a degree-7 S-box and a degree-3
S-box both cost **one committed value** in a virtualized AIR and **one 16-wide state snapshot**
in an un-virtualized one.

### 10.1 What this does to `hash-verdict.md` §5

> *"BabyBear→KoalaBear hashing is **298 → 164 cols/perm = 1.82×** (deg-7 forces a committed
> intermediate register; deg-3 evaluates inline), ~1.51× total at the 75% hashing share.
> Both configs already exist in our recursion fork — the migration is a config constant."*

**`298` is not a number this derivation can produce**, and 157 and 164 both are. Two readings,
and they need separating at source before anyone quotes 1.82× again:

1. **298 is a different AIR** (upstream `p3-poseidon2-air`, already partly virtualized), in
   which case comparing it to *our* 164 is apples-to-oranges and the 1.82× is not a
   BabyBear→KoalaBear ratio at all.
2. **298 is our BabyBear chip at a third virtualization level**, in which case 157 or 298 is
   wrong and one of two in-tree numbers has to go.

Either way, its stated *mechanism* — *"deg-7 forces a committed intermediate register; deg-3
evaluates inline"* — **does not hold in an AIR whose max constraint degree budget is 7**:
`y = x⁷` is one degree-7 constraint over one committed value, no intermediate, which is
exactly what `ir2_degree_budget`'s `chip = 7` records and what makes `lqd = 3`. The register
appears only if the degree budget is lower than α. ⚑ **A committed intermediate is what you
pay to KEEP the degree DOWN — so the mechanism describes a system that has already chosen a
low degree budget, i.e. the very thing α = 3 is supposed to make unnecessary.**

### 10.2 The migration's case is `constraint degree`, and only that

`field-choice-verdict.md` opens by saying so: *"The case is **constraint degree, not hashing
speed**."* **That memo was right, and every derived multiplier layered on top of it since has
been wrong** — the hash rate (§3.1, counted mults vs wall clock), the blowup (§3.2/§4, the
descriptor budget's and the two-adicity's, not the field's), and now the narrowing (§10, a
ratio whose absolute inverts). What survives, stated with nothing attached:

| KoalaBear α = 3 vs BabyBear α = 7, like for like | |
|---|---|
| committed felts / permutation, virtualized | **157 → 164 (4.5% WORSE)** |
| committed felts / permutation, un-virtualized | **352 → 464 (31.8% WORSE)** |
| native permutation wall clock | ~1.02× better (measured) |
| **chip max constraint degree** | **7 → 3** |
| **⇒ chip's own `lqd = ⌈log₂(d−1)⌉`** | **3 → 1** |
| quotient chunks for the chip | **8 → 2** (a 4× cut in quotient LDE + commit work for that table) |
| Poseidon2 round-skipping margin | +286 → ~+143 bits (still far above bar) |

**The whole KoalaBear case is the last two rows: the chip stops being the thing that floors
the blowup, and its quotient shrinks 4×.** That is real and it is worth having. It is also
*exactly* the lever §1.5 shows is blocked behind `setFieldDynVmDescriptor2`'s degree-8 `main`,
and §4 shows is capped at `lb = 3` by two-adicity anyway.

> **Net, at the deployed registry: KoalaBear buys a 4× smaller quotient on a table that is
> 13.35% of committed width, pays 4.5% more width on that same table, and cannot lower the
> blowup because another descriptor and the two-adicity both hold it at 3.**

---

## 11. The flag day, MEASURED — and two items make it a redesign, not a rebuild

§7 was written from the Rust side. The Lean census `[measured, 2026-08-13]` is the real bill.

### 11.1 The census

| | metatheory | minidregg |
|---|---:|---:|
| `.lean` files | 3,291 | 540 |
| files containing the literal `2013265921` | **450** | 22 |
| total literal occurrences | **4,216** | 36 |
| ⚑ **independent `def`/`abbrev` declarations of the modulus** | **50** | **1** |
| top-level `#guard`s in prime-bearing files | **3,297** (229 files) | 3 |
| `native_decide` in prime-bearing files | 281 (115 files) | 8 |
| `#assert_axioms` / `#assert_compiled` in prime-bearing files | 6,534 / 67 | — |

⚑ **There is no single source of truth for the modulus in metatheory.** Fifty declarations
spell it eight ways (`babyBearP`, `pBB`, `bbP`, `P`, `BABYBEAR_P`, `BABYBEAR_MODULUS`,
`ledgerP`, `FIELD_MODULUS`), several welded to each other by `rfl`
(`RangeFieldContainment.babybear_modulus`, `FriLedgerSound.ledgerP_eq_babyBearP`,
`DeployedCapTree.feltTrunc_inj` holds two). **minidregg has one anchor and 134 headers follow
it for free** — that is the shape metatheory should be in, and consolidating the 50 into 1 is
worth doing *whether or not* the migration ever happens.

Good news that bounds the bill: **there are no Montgomery constants in Lean** (the tree works
in canonical ℕ-mod-p throughout — `Poseidon2BabyBearW16.lean:20-22`), except one wire-format
`montyRInv := 943718400` at `ProofByteDecoder.lean:455`. And `minidregg/Kernel/`, `Pred/`,
`Effects/` (50+ files) plus `Selvage/`'s whole proximity layer (`JohnsonRegime`,
`RateRegimeSelector`, `Proximity`, `ProximityGapUD*`, `CorrelatedAgreement`) are **fully
field-generic — zero edits.** Only instantiations move. Likewise the bulk of the 450 files is
**one denotation** — `VmConstraint.holdsVm`'s `[ZMOD 2013265921]`
(`Emit/EffectVmEmit.lean:488`, consumed by name in 167 files) — whose mathematics re-proves at
any prime > 3.

### 11.2 ⚑⚑ Two items that are NOT a literal swap

**A. There is no binomial degree-6 extension over KoalaBear. `Ext6` stops existing.**
`p_KB − 1 = 2²⁴·127`, so **`3 ∤ p_KB − 1`**. Consequences, each verified:
`(p−1)/6` and `(p−1)/3` are **not integers**, so `Ext6Conformance.thirty_one_pow_sixth`
(`:51`) and `thirty_one_pow_third` (`:165`) are **ill-formed, not merely false**; cubing is a
**bijection** on `F_KB`, so `thirty_one_not_cube` (`:186`) is **FALSE**; `ext3Polynomial_irreducible`
(`:225`) and `ext6Polynomial_irreducible` (`:230`) are **FALSE** and the `Fact` instance at
`:248` is uninhabitable, so `Ext6Q` stops being a field. **No binomial `Xⁿ − c` with `3 ∣ n`
is ever irreducible over `F_KB`** (Lidl–Niederreiter 3.75: every prime factor of `n` must
divide `ord(c) ∣ p−1`). A degree-6 extension exists, but not as a binomial — it needs a
different construction. **Blast radius: 11 files** (`minidregg/Compiler/{GateFactoredExt6,
GateMleExt6,GateTraceRelationExt6,Ext6GateProof{Controller,Deployment,VersionedDeployment,
PositiveRun}}.lean`, `minidregg/Assurance/{Ext6GateProofControllerAdmission,
Ext6GateProofDeploymentAdmission,Ext6GateProofNonzeroSuiteClosure,
ExtensibleProofCompositionGame}.lean`), plus `Assurance/ErrorBudget120.lean:134`'s
`fieldCard := 2013265921^6` — **the whole 137-bit target presupposes an Ext6 KoalaBear cannot
supply binomially**, and `MixedFieldBudget`'s `unifiedExt6` and `ext6GateExt4Fri` profiles with
it.

**B. `X⁴ − 11` is REDUCIBLE over KoalaBear — and nothing in the tree would notice.**
`X⁴ − 11` is irreducible over BabyBear and **reducible over KoalaBear**; KoalaBear's p3
residue is `W = 3`. Leaving `W = 11` in place makes the "quartic extension field" **a ring
with zero divisors**, silently. Sites: `Dregg2/Circuit/ExtFieldChallenge.lean:214`
(`def W : Nat := 11`, with `extMul_denotes_quartic_babybear` at `:245` proved `by decide` and
~34 `#guard` KATs at `W = 11`), `BabyBearFr.lean:63` (`wExt := 11`),
`Emit/GnarkVerifier/FriFoldEmit.lean:867` (`have hW : wExt = 11 := rfl`),
`Emit/KimchiRootAirEval.lean:326` (`2013265910` = −11), and five more `Emit/*` files. Same
class: `Dregg2/Crypto/SchnorrCurveField.lean` carries `Fact (Irreducible (z^8 − 11))` as a
PARI-verified premise — **`X⁸ − 11` is also reducible over KoalaBear.**

> ⚑ **B is the single most dangerous line item in the whole migration**, and it is exactly
> `CLAUDE.md`'s rule: *make the old shape refuse to load rather than reinterpret.* A residue
> that is a non-residue in one field and a norm in another produces a *ring* where the code
> expects a *field*, every operation succeeds, and every soundness argument that says
> "the challenge space has `p⁴` elements" becomes false without a single error. **`W` must be
> a checked property, not a constant.**

### 11.3 What else genuinely inverts

| declaration | today | after |
|---|---|---|
| `Circuit/BabyBearFriField.lean:60` `babyBear_two_adicity_ge_27` | `2^27 ∣ p−1` | **FALSE**; partner `_lt_28` survives only vacuously |
| `Circuit/BabyBearFriDeployed.lean:296` `omega27 := 440564289` + a **26-step squaring chain**, each rung its own `by decide` | 2^27-th root | **no 2^27-th root exists**; rebuild at 2^23, 23 new constants, generator 3 not 31, cofactor 127 not 15 |
| `Emit/PastaMsmBucketed.lean:1455` `BABYBEAR_TWO_ADICITY := 27`, `rowCeilingAt lb := 2^(27−lb)` | `2^21` at lb=6 | **`2^18`** — ⚑ **independent Lean confirmation of §4**, plus 8 `MAX_ROWS := 2097152` defs and the "past the ceiling by 7.98×" arguments in `PastaMsmLayouts` / `PastaMsmScalarBound` get 8× worse |
| `Circuit/TableAirIR.lean:893-947` `KEY_HI_MAX := 15`, `#guard KEY_HI_MAX*KEY_HI_BASE == p−1` | `p−1 = 15·2²⁷` | **`127·2²⁴`** — `hi` must range over `[0,128)`, which **overflows the 16-row byte table that bounds it**. A circuit-shape change, not a constant. |
| `Emit/Poseidon2RoundGates.lean` `INTERNAL_ROUNDS 13`, `SBOX_ALPHA 7`, `#guard POSEIDON2_AUX_COLS == 352` | | **20 / 3 / 464** — see §10, this is the inversion |
| `Circuit/Poseidon2Binding.lean:134` `babyBearD4W16` + 11 `#guard`s; `params_are_real` (`:191`) admits only it | | needs a `koalaBearD4W16` and every consumer re-points |
| `minidregg/Selvage/SmallField.lean:325` `keystone_bits_babyBear_ext4 : 116 ≤ … < 117` | 116.xx | **117.31 — FALSE**, becomes `117 ≤ … < 118`. ✅ The docstring's point ("the deployed prime loses the 117th bit") **reverses in KoalaBear's favour** |
| `Circuit/LimbTally.lean:792` `max_total_voting_power_exceeds_the_field` | `572e6·p < 2^60−1` | **FALSE** (1.2188e18 vs 1.1529e18); multiplier must drop to ≈541,000,000 |
| `Circuit/CapLeafTargetLanes9.lean:135` / `BytesLanes.lean` `pAlias4 = [1,0,0,120]` | `0x78000001` | `[1,0,0,127]` = `0x7F000001` |
| `Circuit/FieldLanes9.lean:484-512,:747` ~8 `#guard` protocol vectors at the p-boundary | | mostly **FALSE** |

### 11.4 Three margins that survive but go thin — read these before celebrating

1. **`p_KB⁴ = 2^123.9547 < 2^124`** — `FriQueryAdversaryLaunch.lean:116 field_ceiling_vacuous_at_2_124` **survives**, but the margin drops **1.2945× → 1.0319×**. It is now genuinely marginal.
2. ⚑ **The 8-lane pigeonhole survives with 0.091 bits of margin.** `8·log₂ p_KB = 247.909 < 256`, so `FieldLanes9.nine_lanes_is_the_minimum` and `MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8` stay **true** — but the margin to `2^248` narrows from **0.745 bits to 0.091**. `minidregg/Theory/Bignum.lean:342 eight_radix_2013265921_limbs_lt_248_bits` gets razor-thin, and **its name contains the prime**, propagating into a `#guard_msgs` fixture and a consumer in `Compiler/WideDigestAir.lean:57`.
3. The `Emit/EffectVmEmitTransfer.lean` underflow-wrap forgery exhibit **survives** — `(p_KB+1)/2 = 1065353217 < 2^30` is true — but re-instantiates with a new witness.

### 11.5 The one asset

`minidregg/Theory/CyclotomicInertia.lean` (1,184 lines, 51 axiom pins, `decide` throughout, **no
`native_decide`**) **already covers KoalaBear at n = 24 three independent ways**
(`orderOf_koalaBear_three_pow`, `orderOf_koalaBear_mod81`, and as an instance of
`familyP_maximalInertia_iff` — maximal 3-adic inertia iff `n ≡ 0 or 2 (mod 6)`), and it
**already proves `koalaBear − 1 = 2^24 · 127`** (`:134`) with `orderOf_koalaBear_two_pow`
(`:352`). BabyBear appears in it only as a *refutation* (`not_irreducible_cyclotomic_81_babyBear`).

⚑ **Its one gap is exactly the theorem this note needs.** §10's domain-availability results are
instantiated **only at Goldilocks and p61, not at KoalaBear** — there is no
`koalaBear_no_domain_two_pow_25`. The general lemmas (`exists_subgroup_card_eq` `:953`,
`not_exists_subgroup_card_eq` `:967`) are field-generic and `koalaBear_sub_one` is right there.
**Two lines, and §4's trace-height cut stops being a measurement and becomes mathematics.**
That is the cheapest named theorem available anywhere in this note.

### 11.6 The `#guard` bill, and the one place it matters most

`Dregg2/Circuit/Poseidon2BabyBearW16.lean` (212 lines): **every declaration in it is a `def`.
There is not one `theorem`.** The entire Lean-side validation of the deployed hash is
**six** executable `#guard`s (`:190, :196, :203, :208, :209, :210` — the brief's "9" counts
three prose mentions in the header). Compiler-evaluated, unnamed, no reusable term, invisible
to `#assert_axioms`. **22 downstream files consume it, carrying 368 `#guard` KAT pins between
them.**

It is also the *only* BabyBear Poseidon2 round-constant table in the tree, which is the good
news: one file to replace. And per `minted-poseidon2-perm-is-a-reduction-bomb`, `rfl`/`decide`
through the deployed permutation is infeasible (47.6 GB / 68 min for one perm), so the honest
conversion is **`by native_decide` + `#assert_compiled`**, not `decide` — a named theorem with
a recorded compiler dependency, which is strictly more than a `#guard` gives.

⚠ And one upstream discrepancy to settle *before* adopting the constants: plonky3's
KoalaBear-16 docblock (`koala-bear/src/poseidon2.rs:39-52`) derives an interpolation bound of
`R_interp ≥ 79` (→ ~85 with margin) and then ships **`R_P = 20`**, noting only that *"the
official round number script yields 20"*. BabyBear-16's derivation closes cleanly at 13.
**If 85 is right, §10's numbers get four times worse and KoalaBear loses outright.**

---

## 12. The commit-phase bound, quantified `[measured against 10 Lean-proved values]`

`Dregg2/Circuit/FriLedger.lean:322-339` `friCommitLedger`, cited at `:206-218` to **BCIKS20
(2020/654) Lemma 8.2 / Thm 8.3**:

    ε_C = (m+½)⁷·|D⁰|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁰|+1)/√ρ · (Σᵢ l⁽ⁱ⁾)/|F|

versus plonky3's `uni-stark/src/security.rs:427-511`, **BCHKS25 (2025/2055) Thm 4.2**. The
BCIKS20 form was transcribed and **validated against ten Lean-proved values
(71/55/69/81/67/63/61/51/57/51 — all match)** before the comparison was taken.

At `|F| = BabyBear⁴ = 123.628` bits, arity 8, commit_pow 0:

| knobs | `m` | **BCIKS20 (ours)** | **BCHKS25 (plonky3)** | **Δ** |
|---|---:|---:|---:|---:|
| **apex** `lb=6, |D⁰|=2^22` | 3 | **58** | **81.4** | **+23.4** |
| | 7 | 51 | 75.9 | +24.9 |
| `lb=3, |D⁰|=2^19` | 3 | **68** | **88.9** | **+20.9** |
| | 7 | 61 | 83.4 | +22.4 |
| `lb=2, |D⁰|=2^18` | 3 | **72** | **91.4** | **+19.4** |
| | 7 | 65 | 85.9 | +20.9 |

**The mechanism is the paper's headline, isolated:** at `lb=6, m=3`, BCIKS20 loses **2.00 bits
per doubling of `|D⁰|`** (the `|D⁰|²` term) and BCHKS25 loses **1.00** (the `|D⁰|¹` term).
`O(n²) → O(n)` exceptional points. At the apex, BCIKS20's term 1 reads 58.98 and term 2 reads
90.24 — **term 1 dominates, and term 1 is exactly what 2025/2055 replaces. The gap widens with
trace height**, so it costs more the bigger the workload gets.

⚠ **2.78 bits of the gap is not the theorem** — BCIKS20's ε_C is a *total-over-rounds* error
(`Σᵢ l⁽ⁱ⁾ = 48`) where plonky3's is *per-round RbR* (charging `folding_factor − 1 = 7`);
`log₂(48/7) = 2.78`. The remaining **~17–21 bits is real.**

⚠⚠ **And our own tree already records the reason to hesitate** (`FriLedger.lean:262-275`):
*"BCSS25 states no FRI soundness theorem at all"*, and Thm 4.3's proof plugs into **[Sta25], a
personal communication**. So this is 17–21 bits of *citable* improvement resting on a **weaker
citation chain** than the 2020 bound. **That is a judgement call, not an arithmetic one** — and
it is exactly the kind that belongs to the operator, not to a lane. What is *not* a judgement
call: `PROVEN-120-CONFIG`'s "d = 8 is the only answer" was priced against the 2020 bound, and
**+20 bits is more than the gap that verdict was buying an extension-degree flag day to close.**

---

## 13. Corrections this note lands on other files

Listed so the next reader fixes sites instead of hunting them. **None applied here** — this is
a hot shared tree and `--only` is path-granular.

| file | claim | correction |
|---|---|---|
| `docs/VERDICTS.md` §7.9 | *"d=5 at KoalaBear: 128 or not?"* | **`d` is the EXTENSION degree on both sides — write "Ext5".** Resolved: different protocol (WHIR vs FRI), different theorem (2025 vs 2020), m=10 vs 3, ρ=1/4 vs 1/64, PoW admitted on 3 legs vs proved unable to touch `ε_C`. Both true. §5 |
| `docs/VERDICTS.md` §4 | *"the ratio GROWS as α falls (2.24× → 2.83×), so the field question gets a second answer pointing the same way"* | ⚑ **The second answer points the OTHER way.** Absolute committed felts/perm go **157 → 164**. Both ratios are `R_P = 13 → 20` exactly. §10 |
| `docs/VERDICTS.md` §7.1 | *"b=2 does not exist for this circuit"* | **b=2 exists; the floor is a `p3-fri` row-order bug.** §1.4c |
| `docs/VERDICTS.md` §2 | the security-parity ladder `38/29/23/19/17/15` | it is a **JBR-73** ladder — `q = ⌈(73−16)/(lb/2)⌉` reproduces it exactly. Label the regime. §2.1 |
| `notes/prover-floor.md` "Three things to act on" #3 | *"degree 7 forces lb≥6"* | **wrong by three rungs**: `⌈log₂6⌉ = 3`. Reads like a transcription of the deployed 6 |
| `notes/prover-floor.md` cross-check | *"derived native BB/KB permutation ratio 1.69× vs the in-circuit measurement 1.82× — two instruments, 4% apart"* | **not two instruments on one object** — native multiplies vs committed AIR columns. Withdraw the corroboration |
| `notes/prover-floor.md` | *"the migration is ~3.4× on the dominant term"* | contains the blowup leg *in its own sentence*; and mixes an in-circuit 1.5× with a native term. Measured composition is **≈1.05×**. §3 |
| `notes/hash-verdict.md` §5 | *"298 → 164 cols/perm = 1.82×"*, mechanism *"deg-7 forces a committed intermediate register"* | **298 is not reproducible from the round structure; 157 and 164 both are.** And the mechanism does not hold in an AIR whose degree budget is already 7. §10.1 |
| `circuit/src/descriptor_ir2.rs:7179` | *"38 of the 91 by-name goldens pull it in"* | **43 of 132**, measured today. Neither number is asserted by any gate (`files.len() >= 80` still passes at 132). §6.2 |
| `circuit/tests/fri_blowup_global_knob_survey.rs:685-690` | asserts a chip-bearing descriptor MUST refuse at `(2,57)` | ⚑ **goes RED when the p3-fri bug is fixed. It locks the bug in.** Assert the degree invariant instead. §1.4d |
| `docs/reference/FRI-PARAM-FRONTIER.md` | FRONTIER A starts at `lb = 3`, never says why; zero mentions of constraint degree | the floor is undocumented there and `lb ∈ {1,2}` are simply absent |
| `docs/reference/PROVEN-120-CONFIG.md` | *"d = 8 is the only answer"* | priced against **BCIKS20 (2020)**; the 2025 bound is worth **+17–21 real bits** on the same column. Re-derive before buying the flag day. §12 |
| `minidregg/Selvage/SmallField.lean:473` | *"the round 2³¹ estimate's 117th bit is NOT delivered by the deployed prime"* | **KoalaBear delivers it** (117.31). The paragraph inverts — one of the few places the migration is strictly better |

## 14. Reproduce

```bash
cd ~/dev/breadstuffs
cargo test -p dregg-circuit --release --test fri_blowup_global_knob_survey --no-run
B=./target/release/deps/fri_blowup_global_knob_survey-*
$B the_whole_registry_priced_under_the_calibrated_predictor --nocapture --test-threads=1  # §6.2 census
$B the_row_ceiling_is_two_adicity_minus_log_blowup          --nocapture --test-threads=1  # §4
$B every_provable_descriptor_at_every_parity_point --ignored --nocapture --test-threads=1  # §6.1, §6.3 (~40 s)
RAYON_NUM_THREADS=1 ./target/release/deps/ir2_phase_profile-* phase_profile_raw_spans \
    --nocapture --test-threads=1                                                          # §3.3 committed geometry
```
Arithmetic: `scratchpad/kbmig_regimes.py` (§2.1, five-row reproduction),
`scratchpad/kbmig_cost.py` + `kbmig_cost2.py` (§2.3 models).
Release only. Load average was 29 throughout; **the ratios are the deliverable, the absolute
ms are not.**

⚠ **Box condition during this lane**: `/System/Volumes/Data` hit **100% (7.9 GiB free of
7.3 TiB)** mid-run and killed a `cargo test --no-run` with `ENOSPC`. `breadstuffs/target` alone
is 27 G. **Nothing was deleted from any shared tree.** The one by-construction cell I could not
close is `lb = 1` on a `d = 3` descriptor (`pasta_sbox_program_proves::the_blowup_is_swept_at_parity_on_this_machine`,
which sweeps `[(6,19),(3,39),(2,57),(1,114)]`) — its binary would not link. **It is the last
cell of §6.1's table and it should be run when there is disk.**
