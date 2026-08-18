# Lane brief template — the shape that works

Distilled from ~50 lanes (2026-08-11..13). Every section earned its place by a
failure. Fill all of them; deleting a section is a decision, not an omission.

## 1. ROLE + ONE-SENTENCE GOAL
Research / red-team / implementation / experiment / writing. One sentence of
what done looks like.

## 2. SPEC POINTERS (ground truth first)
The note/doc that IS the specification, read-first order. Lanes that reconstruct
the interface from prose build a mirror and verify against their own
reconstruction — paste REAL signatures, REAL paths, REAL theorem names.

## 3. CORRECTIONS BAKED IN
Every claim near this lane's territory that has been narrowed/refuted, stated
inline. A lane must not be able to re-derive a dead claim from a stale note.
(The audit-scaffold lane succeeded because the ε_beacon and "attained"
corrections were IN the brief.)

## 4. WHAT YOU MUST NOT ASSUME
The specific over-claims this lane is most likely to make, named. ("The
grinding theorem is NOT an ε_beacon statement.")

## 5. HAZARDS + PREFLIGHT
Point at swarm/PREFLIGHT.md. Name the shared-tree state (who is dirty, which
files are untouchable), the tooling landmines, the evidence-corrupting races.

## 6. GATES
What "done" must survive: build command + host, detached-clone HEAD
verification for anything committed, axiom pins for anything proved,
boundary/hygiene scripts. "Green in your worktree" is not a gate.

## 7. DELIVERABLE SCHEMA
The exact sections the report must have. Always include:
- claim tags: PROVED / MEASURED / COMPUTED / SOURCED / INFERRED-BY-ME
- what was NOT done, as its own section (absence ≠ negative finding)
- for multi-thread lanes: per-thread return status — a thread that never
  returned must be REPORTED as such, never silently absorbed

## 7b. SUBSTRATE LAW (state in every brief that touches proving)
**We are abandoning Plonky3 and every third-party prover stack as fast as we
can.** The trust path is Lean-authored and formally verified — ours. Upstream
crates may be READ for API shapes and may serve as throwaway differential
oracles in tests; they never enter the trust path, they are never a
"foundation," and **"it already exists upstream, unwired" is not a reason to
wire anything.** A lane that proposes adopting an upstream engine has
misunderstood the project. If a capability is missing, the answer is that we
build it in Lean, in Selvage.

## 7c. A CONFESSION'S LOCATION LIST NEEDS THE SAME GREP AS A CLAIM
Found 2026-08-13, and it cost a cleanup lane real time. A lane self-corrected
with *"I cited this wrongly, including in file Y."* That location list was
**recalled, not grepped** — file Y had cited it correctly all along. I put the
false accusation into a brief, and the next lane had to disprove it.
**When a lane confesses, the WHERE is a claim too: grep it before propagating.**

## 7d. HASH/LINEAR-LAYER DESIGN GATE (2026-08-17, paid for by Weft — **AMENDED the same day, paid for by re-opening it**)

⚑ **The first draft of this gate said "compute the branch number FIRST." That
was the wrong half of Weft.** `notes/weft2.md` re-opened the kill and measured
it: **branch 6 was NOT disqualifying** (at GF(2³²) one active `x⁻¹` S-box is
worth 30 bits on *both* sides ⇒ 180 bits per 2 rounds against a 128-bit bar —
and **Poseidon2's own internal layer is branch 2 and ships**). What killed Weft
was a **fixed lane** — `output lane 0 = input lane 0` — that **no branch number
can see**: the whole 23-rotation family changes the structure completely while
`B_d` and `B_l` do not move at all (a permutation preserves Hamming weight).

**Branch number is a ONE-ROUND quantity. Everything that kills these designs is
MULTI-ROUND.** So, in this order:

1. **STRUCTURE FIRST — the invariant-subspace / subspace-trail search.** For a
   lane-wise 0-fixing S-box the invariant coordinate subspaces are *exactly* the
   closed sets of the support digraph (`i → j ⟺ L[j][i] ≠ 0`) — so enumerate the
   **whole lattice** by closure, on **`M` and `Mᵀ` both**, and ⚠ **index from
   b = 0**: the kill's own script looped `range(1, 5)` and the level it skipped
   was the fatal one. `∞` diffusion depth is a hard fail.
2. **A QUOTIENT IS NOT A SUBSPACE.** "Broken by round constants" is the standard
   escape for an invariant *subspace*. It is **false** for an invariant
   *quotient* — the constant just becomes the small map's own round constant.
   State which one you found.
3. **The subfield test, entry-level AND twisted.** Do the entries lie in a proper
   subfield (`x⁻¹` preserves every subfield)? Does any two-sided diagonal twist
   put them there — i.e. what subfield do the **cross ratios** generate? ⚑ **MDS
   does not answer this**: the systematic-RS repair is MDS by theorem and *still*
   a GF(2⁸) matrix at the natural point set. Then test the round **constants** the
   same way — a small-integer transcript tag lives in GF(2⁸).
4. **`deg(minpoly)` + per-lane observability**, if any partial/internal round is
   contemplated. Poseidon2's internal condition is **observability of `(eⱼᵀ, M_I)`**,
   not a branch number. ⚑ An involutory MDS layer (`A² = I`) passes every branch
   test and leaves a 22-lane subspace on which partial rounds are linear.
5. **THEN the branch number — on BOTH sides.** `B_d(M)` *and*
   `B_l(M) = B_d(Mᵀ)`; they are different quantities off MDS, and the kill
   computed only the first while the second read **2**. Score against **the bar**
   (S-box DP/LP × branch), never against the MDS ideal, and against a
   **same-characteristic** comparator — the kill's Poseidon2 row was BabyBear,
   and `M_E`'s {1,2,3} entries have no char-2 instance.
6. **If the layer is inherited from another object, THE POINT SET is the design
   decision.** Weft died by evaluating *inside its own interpolation window*.
   Moving the evaluation set off the window is **free** (same butterflies, shifted
   twiddles) and is the difference between branch 6 with a fixed lane and branch 8
   (one transform) or 25 (two transforms, MDS *by theorem*).

Tooling we own: `~/src/ring-ro-hash/weft2_structure.py` (steps 1–4 + both branch
sides), `weft_branch.py` (the self-certifying `branch(M) = branch(M⁻¹)` passes),
`mark32_sysrs_branch.py`. Corollary kept from the first draft, now with its real
mechanism attached: **a linear layer inherited from another object imports that
object's structure — and the import is through the POINT SET, which is free to
change.**

## ⚑ 7d-bis. BEFORE YOU CONCLUDE A PRIMITIVE CANNOT BE ANALYSED (2026-08-18, paid for by the gadget-Feistel)

`notes/formal-cryptanalysis-pipeline.md` §4 concluded the gadget-Feistel was
**structurally opaque to the algebraic instrument**, and left it there. That was
half an answer. The follow-up lane
(`notes/feistel-classical-tooling.md`) found the primitive is **perfectly
expressible** to the bit-level classical toolchain — a full round was built as a
CLAASP component graph and matches the versioned spec 40/40 — and that **the
question "is it AO-shaped or classical-shaped?" does not predict anything**,
because the answer was *both, in different layers*.

**The question that predicts the outcome:**

> ⚑ **IN WHICH LAYER DOES THE ODD-PRIME MODULUS SURVIVE?**

Measured on the gadget-Feistel, per layer:
- base-B decomposition, `B = 2¹⁶` over a 64-bit modulus → **bit-slicing, ZERO components.**
- plane products `Y_j·Y_{j+1}`, where `d·B² = 2³⁶ ≪ q` → the modulus is **reduced away
  before the layer**, so it is mod-2ⁿ exact and classical and free.
- `F_r = Σ g·Y + Σ h·Z`, dense public constants **in R_q** → the modulus **survives**, and
  this one line is **97% of the 14.5M components per round.**

So, in this order:

1. **Name the substrate of each LAYER separately**, not of the primitive. A layer whose
   values are provably small relative to the modulus is a **classical layer** and should be
   priced against bit-level tools (CLAASP/CLAASP-MP, SAT/SMT differential search), not
   against algebraic ones.
2. **Check the tool's arithmetic field before its capability list.** ⚑ **A `modulus`
   parameter the models ignore is worse than an absent one.** CLAASP's MODADD accepts an odd
   modulus, honours it in the *evaluator*, and models it as mod-2ⁿ everywhere else — the
   constraint text is byte-identical and CLAASP-MP returns the *same ANF for a different
   function*. Run the tool's own self-consistency check (`check_anf_correctness` or
   equivalent) at **≥200 samples on a LOW-ORDER bit** before believing any output: on the
   bit it tests by default the divergence rate was 0.030, so it misses with p = 0.54.
3. **Before "the tool cannot be run", ask what QUANTITY it bounds and whether that quantity
   is directly measurable.** CLAASP-MP bounds the F₂ algebraic degree; the exact degree is a
   cube sum, and 2¹² evaluations × 10 base states settled in 4 minutes what a ~10⁹-variable
   MILP would have reported. **A scale wall is not a verdict; the quantity behind it usually
   is.**
4. **One base state cannot tell a distinguisher from a coin.** Half the output bits balanced
   over a cube is what a *random permutation* gives. Count bits balanced across N independent
   base states, against the chance baseline `NOUT·2⁻ᴺ` — and make sure your grid contains a
   **known-true** property the harness must find, or "we found nothing" means nothing. (Ours:
   the 1-round Feistel branch copy, found at 1024/1024 against a baseline of 1.)
5. ⚑ **"No published model can be instantiated" is UNDONE WORK, not a theorem.** State it
   with the *specific requirement that fails*, and **eliminate the plausible-sounding
   non-blockers by name** — for the gadget-Feistel, "it is a Feistel" and "it is unkeyed" are
   both covered in the MITM literature and neither is the blocker. If you do not name them,
   the next reader will cite them as reassurance.
6. **Count the instruments, and do not add them up.** Four instruments reporting they see
   nothing is **one** fact about our instruments, not four about the primitive
   (`feedback-every-instrument-is-blind-to-the-next-wound`).
7. ⚑⚑ **"NO TOOL MODELS IT" AND "THE MODEL EXISTS AND NOBODY CAN RUN IT" ARE DIFFERENT
   VERDICTS, AND THE SECOND IS STRONGER.** This lane wrote the first and the sweep returned
   the second. For the decomposition layer, **three designer papers write the constraint
   themselves** (Monolith 2023/1025 §B.3, Reinforced Concrete 2021/1038 §B.4, Skyscraper-v2
   Eq. 21) — and **every solved instance in the literature is a 6-16 bit toy prime**, with
   Monolith calling full-size ones *"computationally intractable"* in its own words.
   **So always ask, in this order: (a) does anyone write the encoding? (b) has anyone RUN it
   at real parameters?** A "no" at (b) with published toy-scale numbers is a **measured wall**
   you can cite; a "no" at (a) is usually just a literature search you have not finished.
8. ⚑ **When the automated instruments all refuse, go find the HAND-BUILT attack.** The only
   published technique that reaches a decomposition layer is Liu et al., eprint **2024/1900** —
   a hand-written limb-wise carry-DDT automaton in C++, explicitly *"Independent of the
   S-box"*, reaching 3/5-round Tip5 and 2/6-round Monolith-64 collisions. **The absence of an
   automatable model is not the absence of an attack**, and the attack-me item should name the
   concrete technique, not a family ("order-2 / boomerang").

## 8. STANDING ORDERS (copy verbatim into every brief)
- Read theorem statements, not abstracts, for anything you call a bound.
- Verify claimed absences with multiple spellings AND post-mirror via web.
- A quote you cannot re-find by grep does not exist. (A lane fabricated one;
  the grep caught it.)
- Statement-first with refutation teeth for anything formalized; a named
  obligation Prop is a good outcome, a `sorry` is not.
- If blocked >2/3 of budget on one step, write the partial report FIRST, then
  continue. Silent lane death costs more than partial results.
- Under-claiming is correct. The report gates decisions; err toward breaking
  your own findings.

## 9. ⚑ THE HANDOFF RULE (added 2026-08-13, paid for by a transcript audit)

A transcript-mining lane found that **every high-value loss in this project
had the same mechanism: a lane produced the result and the DELIVERY CHANNEL
failed** — credits exhausted mid-write-up, `SendMessage` rejected as "prompt
too long", or a consolidation pass that kept the verdict and dropped the
model. The recording discipline is excellent; **the handoff between a lane
finishing and a note existing has none.**

Therefore, every lane:
1. **Writes its note FIRST, incrementally, not at the end.** Create the
   notes file early and append as findings land. A note that exists at 40%
   completeness beats a perfect report that dies at 95%.
2. **Leaves a pointer for every on-disk artifact it creates** — scripts,
   Lean files, test files, cloned repos — in that note. Finished work with
   no pointer is deleted work. (Recovered examples: `~/src/ring-ro-hash/
   design_*.py`, `minidregg/Theory/IntegerFingerprint.lean`, two claude.ai
   decision memos whose URLs appear nowhere in the repo.)
3. **Never reports a number only in prose to the orchestrator.** If it was
   computed, it goes in a file.
