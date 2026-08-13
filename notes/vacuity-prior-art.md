# The census is a reinvention — twice over. Here is the terminology and what survives.

2026-08-13. Ember called this before the lane ran ("it's what you literally do
all the time"), and the literature agrees. Recording so we cite instead of claim.

## Our vocabulary → the published vocabulary

| ours | published name | source |
|---|---|---|
| carrier census / unwitnessed carrier | **vacuity**, spec. *antecedent failure*; **and in Lean, the `has_inhabited_instance` linter** | Beer/Ben-David/Eisner/Rodeh FMSD 2001; van Doorn/Ebner/Lewis CICM 2020 |
| refutation teeth | **falsity coverage** / **vacuity coverage**; at spec level **bug-completeness-score**; **mutation proving** | Chockler/Kupferman/Vardi CHARME 2003; Endres et al. FSE 2024; mCoq ASE 2019 |
| the whole discipline | **sanity checks** (named, surveyed) | Kupferman, CONCUR 2006 |
| census as a CI gate | **static coverage / verification coverage** | Tomb & Joshi, **FMCAD 2025** |
| `assert false` probing | **smoke testing** — shipped in Boogie, Why3, Frama-C; Dafny has `--warn-contradictory-assumptions` | — |

**mathlib had our exact query six years ago.** CICM 2020 §3.3: the
`has_inhabited_instance` linter checks each `Type`-valued declaration for
derivable inhabitation. Only the *motive* differs — theirs is applicability,
ours is vacuity. Same question, opposite reason.

**And Chockler/Kupferman/Vardi 2003 is our two-tier law, 23 years early**:
"1. Falsity coverage: does the mutant still satisfy the spec? 2. Vacuity
coverage: if it does, does it satisfy vacuously?" = ATLAS laws 1 and 2.

## What genuinely survives as ours (three items, stated as contributions not inventions)

1. **Ranking by load-bearing-ness** (`hypothesisCount`) — no cited instrument
   ranks; mathlib's linter is pass/fail per declaration.
2. **Teeth on the instrument itself.** Tomb & Joshi's own RQ4 worries about
   false negatives and they have **no red-proof**. Our self-test would fail
   loudly if the query stopped detecting. "A gate that can't go red is not a
   gate," applied to a published instrument class that lacks it.
3. **The audited-non-target registry** with named impossibility evidence,
   keeping the honest raw count separate from the actionable frontier.

**And the sharpest one-sentence framing, which IS defensible:** Isabelle's
locale interpretation and HOL's `typedef` impose a nonemptiness obligation at
definition time. **Lean does not.** The census is the retrofit of an
obligation those systems get for free from their definitional principles —
which is exactly why the instrument is needed *in Lean specifically*.

## Two improvements the literature hands us

- **Unsat-core / dependency coverage** (Tomb & Joshi) would catch the vacuity
  our census structurally cannot see: a carrier that IS inhabited but whose
  hypothesis never participated in the proof.
- **Mutation proving** (mCoq, 12 Coq projects, "unveiling several incomplete
  specifications… manifested as live mutants") is the mechanised form of the
  teeth law across a whole tree rather than per-keystone.

## ⚠ A methodological warning we must carry

Endres et al. FSE 2024: "our completeness metric was consistently lower when
only considering **natural** bugs; naturally occurring LLM code generation
bugs are harder to kill than artificially seeded bugs." **Synthetic teeth
overstate your teeth.** Our RED witnesses are hand-built mutations — they may
be systematically easier to catch than the failures that actually occur.

## Our specimens, published nine years ago

Fonseca et al., EuroSys 2017 (IronFleet/Verdi/Chapar, 16 bugs, and after eight
months of hunting: **"No protocol bugs were found in the verified systems"** —
every bug lived in the specification, the shim, or the tooling):
- **Bug I1 IS our teeth law run as an experiment**: they disabled IronFleet's
  deduplication in seven lines and **"the patched implementation still
  verified."** A mutation that should have gone red, did not.
- **Bug I2 IS "the wrapper answers for the work"**: NuBuild consumed only the
  first message of Dafny's output, so the verifier "falsely reported that any
  program passed verification checks, **including programs that asserted
  false**." Our `tee|tail` exit-code class, in a real pipeline, 2017.

Adopt their three-bucket taxonomy (**specification / shim / tooling**, all
inside the TCB) + Kupferman's sanity-check family + Tomb & Joshi's four gap
types. Our SP1 and Isabelle-STARK specimens map cleanly onto them.

## The one hole that IS ours to fill

**The AI4Math literature has no vacuity content at all** — DBLP and arXiv
sweeps for reward-hacking-in-Lean, vacuous LLM formalization, faithfulness of
autoformalization: nothing. Meanwhile the SE side already built the metric
(Endres's bug-completeness-score, mutant-killing for AI-generated
*specifications*). **Nobody has published on an AI prover producing a
kernel-clean theorem that is true because its premise type is uninhabited —
a mode neither an SMT unsat core nor a mutant-killing metric can see.**
That is the contributable slot, we have real specimens, and it is small and
honest.

## The pre-AI baseline, for any speed claim we make

**Effort is linear in proof size; proof size is QUADRATIC in specification
size** (Staples ESEM 2014 + Matichuk ICSE 2015, 215K lines of seL4 proof).
seL4: ~9:1 effort ratio, ~23:1 line ratio; **a 12% code change cost 1.5–2
person-years to re-verify**. CompCert: 87% of 35K lines is spec+proof.
Any AI-speed claim should be stated against *that law*, not against
lines-per-day.
