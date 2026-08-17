# TwistContinuity × Nebula Lemma 2 — the memory-soundness keystone (LEAN BUILD lane)

Status: **COMPLETE 2026-08-17.** All three modules land zero-error/zero-warning with axiom
pins `[propext, Classical.choice, Quot.sound]` verified by `#guard_msgs`; full `lake build`
green (9004 jobs); `check-import-boundary.sh` green. No `sorry`, no new axioms, no `#guard`s.

Repo: `~/dev/minidregg`, landed as **`820f0cb`** ("memory: Nebula's Lemma 2 lands, and
TwistContinuity's adversarial direction is priced" — 5 files, 1291 insertions). Session date
2026-08-17. Sibling lane note: the same session's `bc29222` (AccRbrFold) is the SAME Nebula
read's transfer item #2 — items 1 and 2 of `nebula-vega-lessons.md` §7 both closed today.

**Deliverable summary (the brief's four items):**
1. Relation to Lemma 2: `TwistContinuity` is Lemma 2's LEFT side on richer carriers (§1–2);
   the right side (multiset invariant) did not exist in the tree — no keystone implied either
   direction (checked, §2).
2. Lemma 2 formalized BOTH directions + packaged iff: `Compiler/TwistMultisetInvariant.lean`.
   Corollary 1 at the sharp `max·(k+1)/|F|` bound: `Selvage/MultisetFingerprint.lean`
   (SZ cited from `LogupStar`, roots-before-challenge as quantifier order, per brief).
3. Residual DISCHARGED at the semantic level (the adversarial direction now a theorem) and
   NARROWED to one named obligation `[TWIST-FP-BIND]` (six cryptographic legs, each naming
   its supplier — `Assurance/TwistMemoryFingerprintJoin.lean` header). The `free` gap is NOT
   an obligation: absorbed by `Option`-valued cells, no case split (§4).
4. Teeth: all landed (§5). Consumer wired across module boundaries (Compiler bridge →
   invariant → Assurance join; Selvage fingerprint → Assurance join).

## 1. The target, as it actually stands in the tree — DONE (read, binders quoted)

`TwistContinuity` lives in `Compiler/SparseAuthenticatedStateLogupBridge.lean:90` (the brief
said `Kernel/`; the Kernel memory model is `Kernel/SparseAuthenticatedState.lean` and the
bridge that names the residual is one directory over). Verbatim:

```lean
/-- The row-only state-continuity statement targeted by a Twist-style memory
argument.  Each next row consumes exactly the state produced by its predecessor;
there is no prover-selected intermediate state or final state. -/
inductive TwistContinuity {L : Layout.{u, v, w}} :
    Store L -> List (BusRow L) -> Store L -> Prop
  | nil (store : Store L) : TwistContinuity store [] store
  | cons {pre middle post : Store L} {row : BusRow L} {rows : List (BusRow L)}
      (discipline : DisciplineRowValid row)
      (transition : CellTransition pre middle row)
      (tail : TwistContinuity middle rows post) :
      TwistContinuity pre (row :: rows) post
```

Binders read closely:
- It is **state-threaded by list position**, not by the `clock` column — `row.clock` is
  semantically inert in `TwistContinuity` (it is constrained only by `BusRelation`, the honest
  projection). Any adversarial-direction argument must therefore *supply* the time structure.
- `CellTransition` carries before-exactness, after-exactness AND a per-step frame over every
  other typed address — so each intermediate store is fully determined:
  `middle = pre.set row.space row.key row.after`.
- `DisciplineRowValid` is a row-local shape check (ROM read-only, appendOnly fresh-alloc-only,
  RAM write/alloc/free), independent of the threading.

**What is proved today (honest direction only):** `TwistContinuity.of_busRelation`
(line 188) — an accepted semantic execution's derived bus satisfies the relation; consumed by
`ExactBusClaim.twistContinuity` and carried as the `continuity` field of
`AcceptedSparseBusLookup` (line 442). **The adversarial direction is the named residual**: the
module header calls the relation "the semantic statement a Twist-style argument must prove",
i.e. nothing yet forces a *committed* bus (prover-supplied rows) into continuity.

## 2. Relation to Nebula Lemma 2 — the verdict

Nebula Lemma 2 (offline checking, per Spice eprint 2018/907 Lemma C.1): with the timestamp
discipline, *every read returns the last write* ⟺ *∃ FS with IS ⊎ WS = RS ⊎ FS (multisets)*.

Relation: **different carrier, same content, ours strictly richer — and neither statement
subsumes the other as written.**
- `TwistContinuity` IS "every read returns the last write", stated *inductively over threaded
  stores* rather than as a multiset equation. It is the LEFT side of Lemma 2's biconditional,
  transplanted to typed sparse stores.
- Lemma 2's RIGHT side (the multiset invariant) **does not exist in our tree at all** — checked:
  no `Multiset`-valued statement about `BusRow` lists anywhere under `Compiler/` or `Kernel/`
  (the tree's multiset machinery appears only in Mathlib usage inside `Selvage/`). So no
  existing LogUp keystone "already implies a direction" — what exists nearby:
  - `Selvage/LogupStar.lean` — the pushforward/log-derivative kernel + the exact SZ lemma
    `uniformProb_poly_eval_eq_zero_le` (line 257). This is *fingerprint machinery*, reusable
    for Corollary 1, but says nothing about memory threading.
  - `TwistContinuity.of_busRelation` — exactly Lemma 2's completeness PREMISE feeder (honest
    trace ⇒ threading), not either direction of the biconditional itself.
- Carrier deltas that the formalization must respect:
  1. **Typed namespaces + disciplines** (ROM/RAM/appendOnly) vs their one flat space —
     handled by keeping `DisciplineRowValid` a separate conjunct (it is row-local; the
     multiset argument never needs it).
  2. **Sparse `Option`-valued cells** (absence is a value) vs their total initialized memory.
  3. **`free` exists here and not in Nebula.** Resolution (see §4): in the sparse carrier a
     `free` is *a write whose after-value is `none`* — the invariant is UNCHANGED; `free`
     adds nothing to the multiset equation, only to `DisciplineRowValid`. The flagged hazard
     ("a freed cell's stale tuple must not re-enter RS") is killed by the same stamp
     discipline that kills every stale read; tooth planned.
  4. **Timestamps**: Nebula's global counter = our list position. Our rows carry no
     "previous-write timestamp" column, so read stamps enter the statement as a
     prover-supplied function `stamp : Nat → Nat` with discipline `stamp i ≤ base + i` —
     exactly the prover-supplied `t < ts` of Spice.

## 3. The formalization — files as they land

1. `Compiler/TwistMultisetInvariant.lean` — **LANDED, compiles zero-error, axiom pins
   [propext, Classical.choice, Quot.sound] verified by `#guard_msgs`.** The combinatorial
   keystone (no crypto, no field):
   - `MemTuple` (typed address, `Option` value, stamp); `auditTuples` (IS/FS), `writeTuples`
     (WS, position-stamped `base+i+1` — the verifier's counter), `readTuples` (RS,
     prover-supplied stamp function); `MemoryGrandEquation` = `IS + WS = RS + FS` verbatim.
   - **`twistContinuity_of_grandEquation`** (adversarial direction, the residual's semantic
     half): equation + stamp discipline (`stamp i ≤ base+i`) + row shapes + frame outside the
     audit domain ⇒ `TwistContinuity`. One list induction, Spice C.1's argument: the head
     read stamp `≤ base` vs write stamps `≥ base+1` pigeonholes the head read onto the audit
     tuple at its own address, pinning `row.before`; cancel, absorb the write tuple into the
     updated audit (`Function.update` of the stamp map), recurse. **No `free` case split
     anywhere** — the §4 claim is now theorem-shaped.
   - **`grandEquation_of_twistContinuity`** (honest direction): existential stamps built from
     the actual last-write positions.
   - **`twistContinuity_iff_grandEquation`** — the packaged biconditional = Lemma 2.
   - `grandEquation_refuted_of_not_twistContinuity` — the contrapositive in the shape the
     fingerprint layer consumes (∀ prover stamps, multisets genuinely differ).
   - Consumer: `ExactBusClaim.grandEquation` (declared into the bridge's namespace) — every
     accepted execution's exact bus passes the offline check.
   - Teeth, all landed: `stampless_accounting_fooled` (the write-cycle `1→2, 2→1` over a cell
     holding `0` SATISFIES value-only accounting) vs `cycle_refused_with_stamps` (the same
     trace refused for every stamp choice — stamps are load-bearing);
     `stale_read_after_free_refused` (allocate→free→read-stale refused ∀ stamps — the Nebula
     `free` gap exhibited closed); `honest_trace_accepted` (allocate→write→read→free accepted
     with explicit stamps — satisfiability).
2. `Selvage/MultisetFingerprint.lean` — **LANDED, zero-error, axiom pins verified.**
   Corollary 1, generic (import boundary green: needs only Mathlib + Selvage.LogupStar):
   tuples encoded as polynomials (`vec : T → F[X]`, degree ≤ k — the wide-value/lane-safe
   generalization of Nebula's `a + γ₁v + γ₁²t`, which is the k=2 instance), grand products
   over `γ = (γ₁, γ₂)`.
   - `fingerprint_multiset_sound`: wrong pair accepted w.p. ≤ **`max(|A|,|B|)·(k+1)/|F|`** —
     the SHARP Nebula-shaped bound, not the crude `|A|·|B|` pairwise-collision bound. Proof
     prices BOTH challenges with the ONE existing SZ citation
     (`uniformProb_poly_eval_eq_zero_le`, Selvage/LogupStar.lean) via the bivariate trick:
     work in `(F[X])[Y]`, unique factorization (`roots_multiset_prod_X_sub_C`, cited) makes
     the difference `P` nonzero, a nonzero Y-coefficient of `P` (degree ≤ max·k — a fresh
     elementary-symmetric coefficient-degree lemma, `natDegree_coeff_linFactors_le`) prices
     γ₁, the specialized difference (Y-degree ≤ max) prices γ₂. Product space sliced with the
     landed `uniformProb_prod_le`/`uniformProb_equiv`/`uniformProb_or_le` — no new
     probability toolkit, as the brief demanded.
   - `map_ne_map_of_injOn` + `fingerprint_multiset_sound_of_injOn`: the member-injectivity
     form. ⚠ honest hypothesis note: GLOBAL injectivity of `vec` is **uninhabitable**
     (Nat-stamped tuples cannot inject into bounded-degree polynomials over a finite field),
     so the statement is `Set.InjOn` on the run's members — realized in deployment by range
     checks; stated, not assumed.
   - `fingerprint_forged_after_challenge`: **∀ γ ∃ distinct singletons with equal
     fingerprints** — the prover choosing values after γ wins w.p. 1 vs the theorem's 2/|F|
     committed-first price. The quantifier-order contrast pair IS the γ-ordering exhibit the
     brief asked for.
3. `Assurance/TwistMemoryFingerprintJoin.lean` — **LANDED, zero-error, axiom pins verified.**
   The cross-boundary join (Assurance is the tree's one lawful home):
   - `nonContinuous_fingerprint_accept_le`: ¬`TwistContinuity` ⇒ fingerprint check passes
     w.p. ≤ `(|dom|+|rows|)·(k+1)/|F|`, for ANY prover stamps — the adversarial direction of
     the bridge's named residual, discharged down to the named floor.
   - `exactBusClaim_fingerprint_accepted`: honest `ExactBusClaim` accepted at EVERY γ
     (consumer wired across the Compiler→Assurance module boundary, as briefed).
   - **Residual `[TWIST-FP-BIND]`, named not absorbed** (the ONE remaining obligation, five
     legs): (1) commitment binding over the committed row/stamp columns
     (`CommitmentBindingCR` of `AcceptedLogupRun`); (2) γ drawn after those roots (the
     roots-before-challenge schedule, `TerminalAttestation`); (3) range checks realizing
     `Set.InjOn vec`; (4) row-shape checks realizing `DisciplineRowValid`; (5) the audit
     domain/frame realized against `bus.preRoot`/`bus.postRoot`.
   - Umbrella wiring: `Selvage.lean` + `Assurance.lean` import lines added (both clean of
     the sibling lane's work); `Compiler/TwistMultisetInvariant.lean` is rooted through the
     Assurance join, NOT by editing the dirty `Compiler.lean`.

**Bonus finding while wiring:** `Assurance.lean`'s SpartanR1CS entry records
`[SPARTAN-sparse]` (Spartan's SPARK sparse-commitment layer) as absent — "zero timestamp
vectors, zero multiset check". The engine landed here IS that combinatorial core (offline
memory checking = timestamped multiset invariant + fingerprint); [SPARTAN-sparse] still needs
the sparse-matrix instantiation, but its hardest ingredient now exists in the tree. Noted in
the Assurance import line.

Wiring note: `Compiler.lean` is dirty with codex's uncommitted work (UwueavePreoProjectionV2 +
zkml import hunks), so the Compiler-side file is rooted through the Assurance join
(reachability from the `Assurance`/`Minidregg` targets — the PREFLIGHT-recorded pattern of
rooting from a different library), NOT by editing `Compiler.lean`. Selvage.lean and
Assurance.lean are clean and get the import lines.

## 4. What `free` adds to the invariant — the precise statement

**Nothing, in this carrier.** Nebula's memory cells hold total values; deallocation does not
exist, and Spice's "insert" needs a double-insert guard. Our `Store` is `Π₀ a, Option (Value a)`
— absence is first-class. Under the tuple reading `(address, Option value, stamp)`:
- `allocate` = a write consuming `(a, none, t)` and producing `(a, some v, ts)`;
- `free` = a write consuming `(a, some v, t)` and producing `(a, none, ts)`;
- a later re-`allocate` consumes `(a, none, t_free)` — the freed cell's OLD tuple
  `(a, some v_old, ·)` was already consumed by the `free` itself and cannot re-enter RS
  without breaking the multiset equation; a *stale read* of the freed value is refused by
  exactly the mechanism that refuses every stale read (tooth: `stale_read_after_free_refused`).

So the model difference is entirely absorbed by `Option`-valued cell contents; the invariant
is Nebula's verbatim, and `free`'s residence is `DisciplineRowValid` (which namespaces may
free), not the equation. This is a THEOREM-SHAPED claim and lands as such (the soundness
induction has no `free` case split — `free` is not special anywhere in the proof).

## 5. Teeth ledger — ALL LANDED

| tooth | theorem | file |
|---|---|---|
| value-swap cycle: stampless accounting FOOLED | `Teeth.stampless_accounting_fooled` | invariant |
| same cycle refused with stamps, ∀ prover stamps | `Teeth.cycle_refused_with_stamps` | invariant |
| stale read after `free` refused ∀ stamps (Nebula gap closed) | `Teeth.stale_read_after_free_refused` | invariant |
| honest RAM lifetime incl. `free` accepted, explicit stamps | `Teeth.honest_trace_accepted` | invariant |
| after-γ forgery: ∀γ ∃ distinct pair passing (ordering load-bearing) | `fingerprint_forged_after_challenge` | fingerprint |
| fixed distinct pair refused at a concrete γ (F₅) | `fixed_pair_refused_at_challenge` | fingerprint |
| SZ event NONEMPTY: fixed distinct pair accepted at γ₁=1 | `false_accept_event_nonempty` | fingerprint |
| full adversarial join premise-row inhabited; stale read priced 4/5 | `Teeth.bad_read_priced` | join |
| the concrete bound constrains: 4/5 < 1 | `Teeth.bad_read_bound_nontrivial` | join |

## 6. What a follow-up lane picks up

- `[TWIST-FP-BIND]` (join header): wire the fingerprint check into the deployed
  `AcceptedLogupRun`/`Tower256` controller — binding + schedule legs are the accepted-run
  object's existing premises; the new work is the constraint families (range checks → InjOn,
  row shapes → `DisciplineRowValid`, position-derived write stamps).
- `[SPARTAN-sparse]`: the SPARK sparse-commitment layer's multiset/timestamp core now exists;
  the sparse-matrix (row/col/val) instantiation over it does not.
- Nebula Theorem 2 (two-layer IVC, space `O(|F|+M)`) was NOT touched — it is folding-side
  and sits behind the `[COMPOSE-*]` obligations, not behind this lane.
