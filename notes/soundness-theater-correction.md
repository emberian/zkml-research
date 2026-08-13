# Course correction: the verification apparatus became the work

2026-08-13, ember: *"I'm worried we've descended into soundness theater and
away from actually understanding what's out there in the platonic realm and
the way to compose it into the best possible proof system (fastest, etc)."*

Fair, and here is the ratio, counted:

**Today produced ~15 refutations of our own claims, 4 audits, 3
corrections-of-corrections, and 7 factual patches. Against that: one genuine
design artifact (the GKR substrate memo) and two builds (ring noise lift,
coefficient matmul).**

The verification apparatus started as a way to keep the work honest and became
the work. And the specific failure inside that: **a perfectly honest ledger of
a system that is 100× too slow is still a system that is 100× too slow.** I
was optimizing the ledger.

## The concrete symptom

We hold dozens of *local verdicts* — Celer NO-GO, transciphering dead,
bootstrapping dead, Ext4 under the bar, 130 is CBR-shaped, H2 closed, the
registry mis-specified — and **no synthesized architecture.** The convergence
note identified "a multilinear/GKR substrate is what all four workloads need"
and the response was five more audits rather than *what is the fastest thing
that can be built, and how do the pieces compose.*

## What the balance should be

Verification is a **gate on claims**, not a source of them. It belongs at the
end of a design, not in place of one. The discipline earned its keep — the
absence-claim failures were real, the vacuity findings were real, the H2
measurement genuinely settled something — but the ratio inverted, and each
correction generated two more corrections because auditing is unbounded.

**The rule going forward: a lane that produces a verdict about our own claims
must be outnumbered by lanes that produce a design, a measurement of the
frontier, or a build.**

## What was dispatched instead (2026-08-13)

1. **The prover speed floor, derived from first principles** — the symbolic
   cost function per workload, instantiated at our parameters, with the
   dominant term identified *and its cause*, and a ranked list of what could
   be removed. Explicitly a derivation, not a survey. Includes the two ratios
   that decide our architecture and that nobody has computed: matmul-as-
   sumcheck vs matmul-as-AIR-trace at a real layer size, and the whole
   fold_add batch as one vector relation vs the 98,304-equation AIR family.
2. **Why the fast systems are fast** — read SLOP, SWIRL, leanVM, Expander,
   Binius64, Ceno for *engineering*: where prover time actually goes, the
   specific tricks (Jagged PCS, stacked polynomials, univariate skip, MLE
   memory layout), what they gave up, and what isn't in any paper. Explicitly
   reconnaissance under the substrate law — read freely, adopt nothing.

Both are briefed to deliver **derivations and mechanisms**, not verdicts.
