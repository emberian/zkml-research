# E5 re-derived at current shares — and the re-opening was arithmetically backwards

2026-08-18. Executes the MEASUREMENT + FEASIBILITY brief against
`docs/VERDICTS.md` §5e (*"E5 RE-OPENS: our own optimizations moved the number
that closed it"*).

Labels: `[MEASURED]` / `[DERIVED]` / `[RECALLED]` / `[ASSUMED]`.

Script: `notes/hash-landscape-scripts/crossover_rederive.py` — same model as
`crossover.py`, every input unchanged, **six committed controls reproduce
exactly** before any new row is printed.

> ⚠ **Mid-lane redirect from ember, recorded because it changed the deliverable:**
> deliverable #3 (*"our Poseidon2 permutations proven/second"*) was **withdrawn**.
> Nobody wants Poseidon2 permutations — that rate is our own Merkle-commitment
> overhead, *internal accounting*, not output. Measuring our tax and calling it a
> benchmark adopts their scoreboard for a race we are not in. §4 below answers the
> replacement question instead: **what does one workload dregg actually exists for
> cost, end to end?**

---

## 0. The answer in five lines

1. ⚑⚑ **E5 is not re-opened. It is STRENGTHENED, and by the very number §5e cites.**
   `R*` — the crossover a candidate hash must beat — is *computed from* `f_circ`,
   the share that moved, and it moves **the other way**: `2.49–4.52× → 1.74–2.75×`.
   Reality (`R = 12.7–24.7×` in binary) goes from **2.8–9.9×** above the bar to
   **4.6–14.2×** above it.
2. ⚑ **The "~×5" is the DERIVED row, not the measured one.** Measured-and-proven is
   ×3.75; **deployed today is ×2.10**. §5e quotes the flattering number of a set of
   four.
3. ⚑⚑ **The optimizations did not open the binary door — they closed the LOOKUP
   door**, which was the one route `hash-landscape.md` identified as crossing `R*`.
   Lookup-arithmetized Blake3 (`R = 3.2`) was a **0.79× wrap win** at the old share
   and is a **1.15× wrap loss** at the new one.
4. **All three premises of the original chain hold unchanged.** The conclusion was
   re-derived, not inherited, and it hardened.
5. **The axis question answers itself from §4**, not from §1.

---

## 1. E5 RE-DERIVED — premises separated from conclusion

### 1a. The three premises: ALL HOLD, none re-litigated

| # | premise | status | why |
|---|---|---|---|
| P1 | Proving converges across characteristics — Grøstl out-proves Vision by **3.56×** | ✅ **HOLDS** `[RECALLED]` | eprint 2025/1893 Table 4. Literature; nothing we did touches it. |
| P2 | Verification does **not** converge — stays **12.7–24.7×** apart in a binary field | ✅ **HOLDS** `[RECALLED]` | Same table, same machine, same arithmetization (Binius v0, Ryzen 9 7900X). Still the only same-system head-to-head that exists. |
| P3 | **Recursion cost IS verifier cost** — our wrap identity, 38,168 ≡ 38,168 | ✅ **HOLDS** `[MEASURED]` | And it survives the retune *by construction*: the op list is **packing-invariant**, and `recursion_tower_profile.rs`'s grid prints `perms 38,168` as its control at every packing point. |

**Nothing in the premise set moved.** What moved is `f_circ`, an input to the
conclusion's arithmetic — exactly as §5e says. The brief's hypothesis (*"premises
unchanged while the conclusion moves, because the conclusion was a share-weighted
average"*) is **correct in form and wrong in sign**.

### 1b. The four share points, with provenance and DEPLOYMENT STATE

⚠ COST-MODEL rule 1: a share without its configuration cannot be composed. §5e
quotes `73.3% / ~81%` with neither.

| `f_circ` | what it is | state |
|---:|---|---|
| **36.45%** | pre-split leaf wrap | `[MEASURED]` — **the point E5 was decided at. SUPERSEDED.** |
| **52.36%** | + reduced-opening split | `[MEASURED]` — ⚑ **DEPLOYED TODAY.** |
| **73.3%** | + `a4/K16/rec4` packing | `[MEASURED]` + **PROVEN** — **NOT deployed**, VK rotation pending. |
| **~81%** | + dedicated chain table | `[DERIVED]` — **a NEW AIR that does not exist**, and must be Lean-authored. |

⚑ **A correction to `docs/LEAF-VS-RECURSION.md:94`**, which says the pin was
"deliberately NOT moved". It has since moved: `834a3f7 perf: group matrices and
reverse-horner chain (#439)` is an **ancestor of the pinned rev `fc3c6df`**
(`breadstuffs/Cargo.toml:370-373`), so the split *is* deployed. Verified in the
pinned checkout's own git log, not inferred. **Deployed `f_circ` is 52.36%, not
36.45%** — E5's original measurement point is two moves stale.

### 1c. ⚑⚑ THE FINDING: `R*` IS COMPUTED FROM `f_circ`, AND FALLS WHEN IT RISES

`crossover.py`'s model, unchanged:

```
m_leaf = (1 − f_nat) + f_nat/ρ_nat        leaf prove multiplier on the swap
c      = (1 − f_circ) + f_circ·R          wrap CELL multiplier on the swap
R*     = (1/m_leaf − 1 + f_circ) / f_circ net win iff R < R*
```

Rewrite the last line and the whole verdict falls out:

> ### `R* = 1 + (1/m_leaf − 1) / f_circ`

The numerator is the **native-side gain** — untouched by `f_circ`. The denominator
is the **in-circuit penalty exposure** — and that is precisely what grew. So `R*` is
**strictly decreasing in `f_circ`**, asymptoting down to 1.

| `f_circ` | free hash (R=0) | **`R*` band, leaf wrap** |
|---:|---:|---:|
| 0.3645 *(E5's point)* | ×1.57 | **2.49× – 4.52×** |
| 0.5236 *(deployed)* | ×2.10 | **2.04× – 3.45×** |
| 0.7330 *(proven)* | ×3.75 | **1.74× – 2.75×** |
| 0.8100 *(derived)* | ×5.26 | **1.67× – 2.58×** |

> ### ⚑⚑ Raising the in-circuit hash share raises the payoff of a **free** hash and raises the penalty of an **expensive** one. It is a LEVERAGE increase, not a direction. §5e read one half of a two-sided quantity.

**Where reality sits** — margin above `R*` (>1 means the swap loses):

| candidate | `R` | @0.3645 | @0.733 | verdict |
|---|---:|---:|---:|---|
| Keccak-f, **binary** | 12.7 | 2.8–5.1× | **4.6–7.3×** | fails **worse** |
| Grøstl-P, **binary** | 24.7 | 5.5–9.9× | **9.0–14.2×** | fails **worse** |
| Blake3, prime | 30.6 | 6.8–12.3× | 11.1–17.6× | fails worse |
| **lookup-arithmetized** | **3.2** | **0.7–1.3×** ✅ | **1.2–1.8×** ❌ | ⚑ **CROSSED THE WRONG WAY** |

### 1d. The mechanism, in absolute cells — no shares, no model

The share rose because we deleted **arithmetic**, not because hashing grew:

| packing | wrap cells | Poseidon2 cells | non-Poseidon2 |
|---|---:|---:|---:|
| `a4/K2` (deployed) | 40,554,496 | **21,250,555** | 19,303,940 |
| `a4/K16/rec4` | 28,971,008 | **21,235,748** | 7,735,259 |

**The Poseidon2 half is constant at ~21.2M.** So a traditional hash adds the *same
absolute cells* either way, while the baseline it is measured against shrank ×1.40:

| hash in the wrap | pre-retune | post-retune | **retune worth** |
|---|---:|---:|---:|
| **Poseidon2** (no swap) | 40.6M | 29.0M | **×1.400** |
| lookup-arithmetized (R=3.2) | 87.3M | 75.7M | ×1.153 |
| Keccak-f binary (R=12.7) | 289.2M | 277.4M | ×1.042 |
| Blake3 (R=30.6) | 669.6M | 657.5M | **×1.018** |

> ### ⚑⚑ THE PACKING RETUNE IS WORTH ×1.400 WITH POSEIDON2 AND ×1.018 WITH A TRADITIONAL HASH. The optimization and the hash swap are **mutually cannibalizing** — each one's value is the other's absence, and we already took the better one.

### 1e. ⚑ The casualty nobody has noticed: the lookup route

`hash-landscape.md` §2's headline was *"the ONE lever that crosses `R*` is the
ARITHMETIZATION"* — `R ≈ 3.2` under a lookup argument, **inside** the band
`2.0–4.5×`, flagged as *"the highest-value open measurement on this axis."*

At `f_circ = 0.733` it is **outside**: wrap multiplier `0.79× → 1.15×`. The win
became a loss **while nobody was looking at that file**, because the optimization
campaign that produced it was aimed somewhere else entirely.

⚠ This is the `a-cost-verdict-outlives-its-premise` class, live: a verdict priced
against a share, and the share moved underneath it. **`hash-landscape.md` §2's
recommendation should be re-read before anyone spends a week on LogUp-Blake3.**

### 1f. Named inadequacies

- **The apex is unmeasured at the new packing.** `f_circ = 53.98%` is the *deployed*
  apex figure; the grid measured the leaf wrap only. The apex's `R*` was the low end
  of the published `2.0–4.5×` band, so the true new band's floor is **below 1.74×**.
  Directionally this makes the verdict *stronger*; it is not quoted as measured.
- **`R* ` assumes wrap arithmetic ∝ cells** (inherited from `crossover.py`; the DFT
  is `cells·log h`). Mildly optimistic for the swap at large `R` — again in the
  direction that flatters the swap.
- **`R = 12.7–24.7×` is a verify-*time* proxy for in-circuit cost**, and 2025/1893's
  own caveat stands: *treat it as a shape, not a calibration.* The verdict does not
  turn on it — it survives at any `R > ~2.8`.
- **This section changes no code and no deployment.** It is arithmetic over
  committed measurements.

### 1g. Verdict on §5e

> **§5e's factual claim is right: the share moved, and the free-hash value moved
> with it. Its implied conclusion — that this is the condition the binary-field case
> needed — is REFUTED by the same model that produced the original number.** A free
> hash is not on offer; `R = 12.7–24.7×` is. The condition the binary case needed was
> *`R` falling below `R*`*, and instead **`R*` fell toward `R`.**
>
> **E5 stands, with a larger margin. `docs/VERDICTS.md` §5e should be amended, not
> cited.**


---

## 2. The char-2 prover, scoped — and the blocker is not the module count

Census: `~/dev/minidregg` (⚠ **not** breadstuffs — a definitive grep over all `*.rs`
excluding vendor/target returns **zero** for `binary_tower|BinaryField|additive_ntt|binius`
there; the only GF(2^k) in breadstuffs is AES-field Shamir sharing in
`federation/src/threshold_decrypt.rs`, which is not a prover field).

### 2a. What EXISTS — and it is more than the routability grep suggested

| layer | files | lines | state |
|---|---:|---:|---|
| **Lean `Theory/`** — field + transform | 8 | 3,554 | proved; `[ANTT-transform]` **CLOSED** (additive NTT is a proved linear bijection) |
| **Lean `Selvage/`** — proof-system | 13 | 5,962 | `AdditiveBaseFold` (856 L), `AdditiveBasisBinding` (483 L, **CLOSED**), `AdditiveFriQuery`, `LigeritoInterleaved` (567 L) |
| **Lean `Compiler/`** — controllers, codecs | 13 | 5,123 | Tower256 controllers + cSHAKE256 |
| **Lean `Assurance/`** | 17 | 5,324 | ⚠ discount ~1,350 L: two modules are **vacuous** on a retracted admission |
| **Rust char-2 core** | 4 | **1,387** | ⚑ **runs + tested**: Fan–Paar tower to GF(2⁶⁴) in one `u64`, GF(2²⁵⁶) in 4×u64, LCH additive NTT at exactly `n·log₂n/2` butterflies |

**0 `sorry` across ~20,000 Lean lines, all rooted in the default build** (`Minidregg.lean`
→ `Theory`/`Compiler`/`Selvage`/`Assurance`; oleans confirmed present). Rust: 14 tests pass.

⚑ **The ordered-basis binding really is CLOSED**, and stronger than the brief implied — both
directions. `table_unique_of_novelPack_eq` (positive) and `no_span_indexed_decoder` (negative:
*no* decoder indexed by `(additiveDomain, codeword)` is correct on honest commitments), plus
the transcript repair `challengeInput_determines_basis` → `transcript_determines_table`, which
**was FALSE before `9679a16`**. Its tooth exhibits two bases whose `additiveDomain`s are
**equal**, so the old domain-binding is provably blind to the reordering.

### 2b. ⚑⚑ THE ACTUAL BLOCKER: the proved verifier CANNOT EXECUTE

The shape is unusual and it is not "some modules are missing":

> **A proved *specification* + a deterministic *verifier* that cannot run, and an executable
> *field* with no protocol. The join between them does not exist.**

Three structural facts, each worth more than a module count:

1. ⚑⚑ **`binaryTower k := GaloisField 2 (2^k)` is Mathlib's, and it is NONCOMPUTABLE.**
   Every controller `def` is `noncomputable`; `Tower256AdditiveFriRawDeployment.lean:15`
   says so in prose. **So the verifier we have proved cannot be run at all** — not slowly,
   not at toy size. This is a *refinement* obligation (Lean carrier ⟶
   `prover/src/binary_tower_256.rs`), and **there is no refinement theorem**
   (`[BTOWER256-RUST-UNVERIFIED]`).
2. ⚑ **The prover is a typed hole.** `OpaqueProofRunner := List UInt8 → Except Error (List UInt8)`
   (`Compiler/Tower256AdditiveFriController.lean:607`). Its **only inhabitant in the tree** is
   a zero-round bootstrap whose word is `0`, labelled in-file as *"a plumbing witness, not a
   soundness claim."*
3. ⚑ **`Compiler/Air.lean` has no trace / row / transition notion at all** — in *either*
   characteristic. So "the char-2 AIR" is not a char-2 port; it is a **general debt that
   char-2 merely surfaces first**. ⚠ And `Compiler/FriQueryVerifierAir.lean` is *worse than
   absent*: it assumes `(2:F)·half = 1` over an unconstrained `[Field F]`, so it is
   **VACUOUS at Tower256** — documented in-file, a live instance of the `CharTwoWall` class.

### 2c. The estimate, per the calibration rule

**Module counts** (using the tree's own granularity, ~250–550 L/module):

| side | modules | what |
|---|---:|---|
| **Rust** | **11–14** (~4,000–6,000 L) | computable sponge/transcript · Merkle commit+open over Tower256 · a *field-generic* sumcheck engine (today's `sumcheck.rs` is 1,500 L pinned to `pub type Fp = u64` mod BabyBear) · quotient/OOD prover · additive-FRI round driver + query answering · AIR trace + witness generation · prover entry + proof codec matching Lean's |
| **Lean** | **5–7** | computable field refinement + conformance vectors · a trace/row/transition AIR + its char-2 instantiation · the `statementBytes` residual |

**Dominant term: NOT the port.** It is (i) the **computable-field refinement**, which is a
verification obligation with no partial artifact, and (ii) the **AIR trace notion**, which is
missing in both characteristics. The 1,387 lines of running Rust field arithmetic — the part
that looks hardest — is the part already done.

**Cheapest falsifiable spike**, and it is genuinely cheap: **one char-2 commit-and-open round
trip** — cSHAKE-Merkle an LCH-encoded word, answer one query, and have Lean's *existing*
`Verifier.check` accept it. That needs the computable-field bridge and nothing else, and it
converts `OpaqueProofRunner` from a hole into an inhabitant. Everything else is downstream of
whether that closes.

⚠ **Two hazards to carry into any such lane**: `prover/` is a **standalone crate, a workspace
member of nothing**, and the only CI workflow (`pages.yml`) **contains no `cargo`** — so the
char-2 Rust is tested only when a human runs it. And a **live convention split**:
`AdditiveFriTower` folds the *reversed* basis while the multilinear layer peels *LSB-first*;
Rust has picked reversed-LCH and declares it unverified. Two conventions that will disagree.

### 2d. ⚑ Priced against its unlock — and §1 has already deleted the unlock

The brief asked to price this against the ~×5 a free hash would buy. **§1 shows that unlock
does not exist:**

- ×5 is the **derived** row (`f_circ = 0.81`, an AIR that does not exist). Measured-and-proven
  is ×3.75; **deployed is ×2.10**.
- It prices `R = 0`. Char-2 does not deliver `R = 0`; it delivers `R = 12.7–24.7×`.
- And the share rise **lowers `R*` to 1.74–2.75×**, so the binary candidates fail by a
  *larger* margin than when E5 was decided.

> ### The verdict: **on the recursion-verifier axis, a char-2 prover is 16–21 modules to buy a number that moved against us.** The correct sequencing is not "build it later" — it is "this axis is settled; if char-2 is built, it must be justified somewhere else."

**Where "somewhere else" might be, stated as a question, not a claim** — see §4. It is the
*leaf*, not the wrap: Stage 0's descriptor is **833 variables of which 768 are bit wires**,
and a bit costs a full field element in BabyBear's commitment and a bit in a tower. ⚠ But that
comparison **cannot be made today**, because our own baseline is un-optimized by two levers we
already hold (§4c).

---

## 3. The three workloads, end to end — and only one of them exists

Answering the redirect. ⚑ **This section's headline is a gap, and the gap is the finding.**

| workload | status | artifact | the missing consumer |
|---|---|---|---|
| **EVM Stage 0** | ⚑ **EXISTS-BUT-UNWIRED — worse than its own note says** | `minidregg/prover/testdata/evm_stage0_add_descriptor.json`, 231,487 B, schema verified by parsing | `minidregg/prover/src/descriptor.rs` — **DELETED** (`d55ef32`), and `prover/src/fri.rs` — **DELETED** (`b297c7d`) |
| **vFHE `ct×pt` matmul** | ⚑ **the 466 µs is NOT a proving number** | `fhegg-fhe/src/bfv_coeff_matmul.rs` — runs | **no Lean AIR exists** to be consumed |
| **one SGD step** | **LEAN-ONLY** | `minidregg/Selvage/Rank1GradientCheck.lean:350` `sgd_step_sound` | no emitted circuit object exists at all |

### 3a. EVM Stage 0 — the reader and the backend were both deleted

The Stage-0 note flags its own seam (*"the JSON artifact has no Rust-side reader test yet"*).
**That is too mild.** It is not a missing test:

```
d55ef32 prover: delete handwritten descriptor and trace semantics
        prover/src/descriptor.rs · prover/src/trace.rs
b297c7d prover: retire the unowned Ext4 FRI GPU island
        prover/src/fri.rs · prover/src/field4.rs · prover/src/gpu.rs
```

And `minidregg/Compiler/Emit.lean:47-49` says it plainly: *"The historical Rust descriptor
reader and BabyBear⁴/FRI/WGPU path were deleted; **no current native module consumes this
descriptor.**"* Four independent greps agree — `evm_stage0`, the schema field names
(`nWires`/`nVars`/`gates`/`zeros`), and `descriptor` across every `*.rs` in both repos return
**zero non-comment hits**. **Time-to-proof today: not obtainable. There is no invocation.**

⚠ The other two emitted descriptors (`zkml_eltwise_add`, `demo`) are **also unread**. This is
not one workload's seam; it is the class.

### 3b. ⚑ The 466 µs is homomorphic EVALUATION, and it contains zero proving

`fhegg-fhe/tests/bfv_coeff_matmul_oracle.rs:465`, `fn measured_wall_clock()`. The timed region
is one call — `plan.apply(&encoded, &cts)` — and the test's own printed label is
**`"HOMOMORPHIC EVALUATE (per input)"`**. No commitment, no transcript, no sumcheck, no FRI.
And there is **no Lean AIR for the coefficient matmul at all**: the only Lean AIR checking a
BFV relation in the tree is `Market/PrivateBookBfvBindingAir.lean`, a *different* object
(private order-book ciphertext binding) — which itself has **no test file** in `circuit/tests/`
or `circuit-prove/tests/`.

⚠ **Anyone quoting "466 µs for a verifiable FHE operation" is quoting an FHE number with the
verifiable part absent.** The lane's own notes said so (`cross-limb-binding.md:360`: *"Nothing
here says the deployed Rust enforces any of it."*); the figure has since been repeated without
that half.

### 3c. SGD — a 4-element F₅ agreement test, not a proof

`prover/tests/rank1_gradient.rs:134` brute-forces all **25** challenge points of a 2×2 layer
over **F₅** and asserts `accepted_honest == 25`, `accepted_tampered == 0`. `prover/src/rank1.rs`
labels itself honestly (*"UNVERIFIED COMPUTE… never called refinement or verification"*).
`sgd_step_accepts` is the **verifier's** arithmetic on openings the test hands it in the clear.
No commitment, no Merkle, no transcript, no FRI. **No emitted circuit exists anywhere.**

### 3d. ⚑ MEASURED — and it refutes the repair I was about to recommend

The obvious reading of "3,298 gates for one u256 ADD" is that it is a **tree** count: `emit`
serializes the term tree, and `Compiler/EmitShare.lean:69` measures the note-spend descriptor
going **2,696,666 → 220 gates** under the proved CSE pass — **≈12,258×**. `evmAddDescriptor`
is built by plain `emit`, not `cse`. So the number looked inflated.

**It is not.** Run against the built tree (`lake env lean`, `Compiler/EvmAddAir` + `EmitShare`,
a lawful `Hashable BabyBear` supplied locally — hash only buckets, dedup is by `DecidableEq`,
so the count is instance-independent):

```
TREE   gates=3298 zeros=850 nVars=833 nWires=4131
CSE    gates=3298 zeros=850 nVars=833 nWires=4131
```

> ### ⚑ **CSE removes NOTHING. `3,298` is the honest DAG count for one u256 ADD.** The u256 adder has no duplicated subterms — every gate is a distinct bit-range check or schoolbook limb equation. The note-spend's 12,258× came from a membership mux re-reading hash state; there is no analogue here.

`emit_ssa` gives SSA for every emitted descriptor, so `holds_of_cse_holds` would have
transported the meaning theorem with **no new proof obligation** — the repair was free and it
buys zero. **Recording the null result so nobody re-proposes it.**

⚠ **Consequence for §2**: the **768 bit wires (92% of the 833 variables)** are real and
**irreducible by sharing**. Only two levers touch them: a LogUp lookup range check (in-house,
deployed, untried here) or a field where a bit costs a bit.

---

## 4. What we CAN measure end to end — two real workloads, on a quiet box

⚑ The three named workloads are unmeasurable (§3), but the premise *"we have zero end-to-end
numbers for anything a person would ask for"* turns out to be **false**. Two Lean-emitted AIRs
do close the loop to the deployed Rust prover today, and both are real tasks.

**Conditions** (rig-captured before *and* after every cell, verdict **CLEAN**): hbox,
i9-12900, `taskset 0-15` = the 8 P-cores, governor `powersave`, `nice 15`, release @
**`44d0dea45`** (detached clone on `/tank`, **zero dirty files**),
`RUSTFLAGS="-C target-cpu=native"`. ⚑ **Packing width 8.18 — the packed Poseidon2 path is
live**, so this box is not repeating the scalar-Poseidon2 defect. Count-arm self-check
`P(b) = 3381·2^b + 766` **reproduces all five rungs to the unit.**

### 4a. One dregg Transfer turn (leaf) — `[MEASURED]`

`transferVmDescriptor2`, 1 Transfer, 64 columns × 188 rows, `q=19`, `pow=0`, N=9, min-of-9:

| lb | T=4 cold caller | T=4 in-pool | T=8 cold caller | **T=8 in-pool** |
|---:|---:|---:|---:|---:|
| 3 | 8.394 | 7.335 | 8.823 | **7.276** |
| **6** *(deployed)* | 21.071 | 16.454 | 19.269 | **15.501** |
| 7 | 35.200 | 26.441 | 37.950 | 25.146 |

**≈15.5 ms to prove one Transfer turn's leaf** at the deployed blowup. Spreads **1.01–1.11×**
— the first genuinely clean clock series this project has taken. ⚠ `pow=0`: grind is
**excluded**, and at `pow=16` it adds a *mean* 65,536 perms against 217,150 grind-free at b=6,
with a **measured 6.00× spread** across draws. It must be composed at its mean or named as
excluded; a one-sample grind column may never be differenced.

### 4b. One Ethereum finalized sync-committee update — `[MEASURED]`

`circuit/tests/eth_lightclient_proves.rs`, an honest 400-of-512 update, **prove *and* verify**,
through `metatheory/EmitByName.lean` → `dregg-eth-lightclient-verify-v1.json` →
`prove_vm_descriptor2`. Deployed defaults (`pow=16` — grind **included**).

| state | samples | min |
|---|---|---:|
| **warm** (15 sibling tests first) | 13.298 · 13.452 · 15.044 | **13.30 ms** |
| **cold** (single test, fresh process) | 84.315 · 82.983 | **82.98 ms** |

> ### ⚠ **6.24× on warm-up alone.** Twiddle tables, page faults, and hbox's `powersave` climb from 800 MHz to 5 GHz. **Any single-shot end-to-end number that does not say warm or cold is meaningless** — and the naive way to measure this (run the one test you care about) returns the 83 ms.

### 4c. ⚑⚑ THE FINDING: proof time is almost all FIXED COST, and that is what decides the axis

| workload | logical trace | **padded** at lb=6 | time |
|---|---|---|---:|
| ETH light-client update | **8 rows × 21 cols** | **128 × 21** | 13.30 ms *(incl. grind)* |
| dregg Transfer turn | 188 rows × 64 cols | 256 × 64 | 15.50 ms *(excl. grind)* |

**A 6.1× difference in padded cells — 71× in logical ones — buys 1.2× in time.** The mechanism
is not mysterious: `TablePacking::min_trace_height` enforces
`min_trace_height ≥ 2^(log_final_poly_len + log_blowup + 1)`, so at `lb=6` **every trace is
padded up to 128 rows.** An 8-row program pays for 128.

> ### ⚑⚑ This is `LEAF-VS-RECURSION`'s *"our problem is that THE LEAF IS TOO SMALL"* — measured for the first time as a wall-clock, on a real task. And it **inverts the decompilation pitch.**
>
> The EVM-decompilation advantage is that killing the machine makes the circuit **tiny**
> (635 machine steps → 15–20 semantic ops). **But tiny is exactly the regime where our cost is
> fixed overhead and tininess buys nothing.** Decompilation's win does not convert into proof
> time at this scale — it converts only after the fixed cost is amortized, i.e. **many programs
> per proof**, which is precisely the shape Stage 0 explicitly does not do
> (`evm-stage0.md` gap #5).

### 4d. The program-level comparison in ONE unit — why it cannot be done, structurally

The brief asked for it. **It is not an arithmetic problem and it will not yield to care:**

- **"3,298 gates for five opcodes" is a misreading** that should be corrected before it spreads.
  The five opcode *kinds* are `{PUSH1, CALLDATALOAD, ADD, MSTORE, RETURN}`, and **four of the
  five residualize to zero.** 3,298 is **one u256 ADD** with bit-decomposition range checks —
  and §3d measured that it is the honest DAG count, not a tree artifact.
- **"Gates" here = binary `add`/`mul` nodes** of minidregg's flattening. **Not** AIR cells, **not**
  R1CS constraints. The 3–4K it was compared against is **Nebula's R1CS unit with 2-element
  words** — the Stage-0 note already retracted that comparison.
- ⚑ **No measured conversion exists between minidregg's flat gates and breadstuffs' AIR cells.**
  Different repos, different schemas (`EffectVmDescriptor2` with a `defs`+`shr` sharing list vs
  a flat gate list), **no bridge**. And the corpus's own warning on why unit conversion is not a
  detail: *the same Poseidon2 is 16,837 R1CS emulated and 187 R1CS native — **90×**, and nothing
  about the hash changed.*

> **The missing bridge is the SAME missing artifact as §3a.** One descriptor reader closes the
> units question and the time-to-proof question together. Until it exists, any single-unit
> program comparison is manufactured.

**What can honestly be said today**: a *small* Lean-emitted AIR proves in **~13–16 ms warm** on
one 8-P-core box. A decompiled ERC20 transfer would be a larger AIR than the light client's and
smaller than the fixed-cost floor makes worthwhile alone — and **that estimate cannot be
sharpened without routing Stage 0 to a prover.**

---

## 5. Which axis to measure on — earned, not asserted

**Three axes were on the table. Two are now closed by numbers in this note.**

| axis | verdict | the number that decides it |
|---|---|---|
| **Hash throughput** (219k SHA-256/s, 82k BLAKE3/s per core) | ❌ **Not ours, and not close to the point** | Poseidon2 perms/s is our **Merkle-commitment tax**, not output. Racing it adopts a scoreboard for a race we do not run — and the redirect that withdrew it was right. |
| **Char-2 substrate** | ❌ **Closed, and hardened** | `R*` falls 2.49–4.52× → **1.74–2.75×**; binary candidates fail by **4.6–14.2×**. **16–21 modules to buy a number that moved against us.** |
| ⚑ **Time-to-proof for a real, semantically-specified program** | ✅ **This one** | ~**13–16 ms warm** for a Lean-emitted AIR — of which **almost all is fixed cost**: 6.1× more padded cells buys 1.2× more time. |

### 5a. The plain statement

> ### Our binding constraint is **fixed cost per proof**, not hash throughput — and our differentiator (a program with no machine left) makes programs *small*, which is the regime where fixed cost dominates completely.
>
> **So the two halves of our own pitch are currently working against each other**, and no amount
> of prover-speed work fixes that. The lever is **amortization** — many programs per proof —
> and it is the one thing Stage 0 explicitly does not do.

A hash-rate race concedes a three-year head start on a metric that is not our product. But the
honest half is sharper than that: **we cannot currently answer the question on our own axis
either**, because the one program we have decompiled with a machine-checked meaning theorem
**cannot be handed to a prover** (§3a). We have exact permutation counts for a substrate, two
clean end-to-end numbers for workloads that were already wired, and **no path at all for the
workload the whole decompilation programme exists to produce.**

### 5b. What follows, in order

1. ⚑⚑ **Write the descriptor reader.** One Rust module — a `minidregg` `ConstraintDescriptor`
   JSON → a prove call. It closes **three** open questions at once: routability (§3a), the
   units question (§4d), and time-to-proof for Stage 0. Everything else in this note is
   downstream of it. ⚠ Note it is a *rewrite*, not a revival: `descriptor.rs` **and** `fri.rs`
   were both deleted, so the cheap route is re-targeting the emission at breadstuffs'
   **live** `EmitByName` → `prove_vm_descriptor2` chain rather than rebuilding a second backend.
2. **Then measure amortization, not speed.** The `min_trace_height ≥ 2^(lb+1)` floor is the
   whole story for small programs; batching N fragments into one trace is the only thing that
   moves it. **Measure the curve, do not assume it is linear.**
3. **Amend `docs/VERDICTS.md` §5e** — it currently reads as a re-opening and cites the derived
   ~×5. Both should change.
4. **Re-read `hash-landscape.md` §2 before anyone spends a week on LogUp-Blake3** (§1e). Its
   *"highest-value open measurement"* was priced at a share that has since moved, and the route
   crossed out of the band.
5. **Do NOT build the char-2 prover for verifier cost.** If it is built, it must be justified on
   the *leaf* — Stage 0's **768 irreducible bit wires** (§3d) — and even that comparison needs
   the in-house LogUp range check measured first, because it is free and attacks the same term.

### 5c. What this note did not settle

- **The apex share at the new packing is unmeasured** (§1f), so the new `R*` band's floor is
  below the quoted 1.74×.
- **Neither end-to-end number includes the wrap.** Both are *leaf* proofs. `K = wrap/leaf = 26.9`
  is on the books, so a recursed turn is `[DERIVED]` ≈ 26.9× these figures — **not measured here,
  and not quoted as if it were.**
- **The ×1.400 packing retune is proven but not deployed**, and the `~81%` row needs an AIR that
  does not exist. Deployed today is `f_circ = 52.36%`.
