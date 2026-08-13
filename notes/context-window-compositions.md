# Compositions we blew past in our own context window

2026-08-13. Ember: "what insights from our own context window did we maybe
blow past without realizing how it could be composed with our constructions?"
Reread of the whole session. The pattern of the misses is the session's own
meta-error again: each insight stayed filed under the pillar where it ARRIVED
and never got re-scanned against constructions built later. Ranked.

## A. Run our vacuity instruments ON the Avigad/StarkWare repo

We hold the clone (`~/src/formal-proofs`). Our sharpest criticism of their
S-two formalization was "the premise is unaudited — nothing inhabits
`LookupsSatisfied`, no instrument would notice." **We own the instrument.**
The carrier census is repo-generic Lean-environment walking; pointing it at
their development is a day, yields either "their bridge premises are
inhabited" (good to know) or concrete uninhabited carriers (a collegial gift
of exactly the kind ember wants to lead with), and validates the census
externally either way. Missed because: census = "minidregg hygiene" in our
heads; Avigad = "competitor analysis." Same tool, never aimed.

## B. The weight registry can ship THIS WEEK via range-streaming

The E8M0 lane already does ranged HTTP reads of checkpoint tensors against
safetensors offsets. A Merkle commitment over a model's full tensor set is
the same technique run over all ranges — no full download, no GPU, no prover.
The registry is Pillar III's "most defensible item" and it has ZERO
proof-system dependencies: we could publish commitments to every Tier-1
model (gpt-oss, DeepSeek-V4, Kimi-K3) plus the tooling, now, as the first
Hollow-LLM-closure artifact. Missed because: the measurement lane was filed
as "format question," the registry as "phase 4 design."

## C. The ε_beacon → 0 beacon substrate is already in breadstuffs

The audit theorem's conclusion: only G=1 beacons (threshold VUF / VDF) zero
the beacon term. **breadstuffs has `pqvrf` and `dregg-pq` crates in the
workspace, and fhegg has n-of-n threshold ceremonies with a proven smudging
bound.** A PQ threshold VUF — the exact object the bound wants — is an
assembly of parts we own, not an acquisition. (And Relect itself is
FHE-based SSLE; fhegg's threshold BFV is the substrate that whole paper
family assumes.) Missed because: pqvrf scrolled past in a workspace listing
eight hours before ε_beacon existed.

## D. Lean as single source for BOTH the program and the constraints

catena's hexpr is "a compact syntax for open hypergraphs" — a serialization
format. Our Lean already emits JSON descriptors (DescriptorIR2, the BFV
AIRs). Compose: **the per-op Lean semantics could emit both the executable
catena/hexpr program AND the constraint descriptors from one definition** —
making the spec/executable twin structurally impossible for the ML path,
which is the house law's terminal form. Nobody in any lane proposed it;
the catena lane got to "they are building our spec for us" and stopped one
step short of "so emit their programs from our spec."

## E. catena's determinism flags dissolve the backend-pinning caveat

The MXFP4 census's load-bearing caveat: the provable statement must pin a
serving backend (twelve vLLM backends, OCP leaves order undefined). catena
compiles with `-ffp-contract=off -fno-fast-math`, ordered folds, no libm —
**a catena-compiled server IS a pinned backend by construction**, so the
statement pins the math. The two findings sat three days apart and were
never joined: catgrad is the proving seam, catena is the deterministic
serving spec, and together they close the caveat without waiting for
OCP-conformant hardware pinning.

## F. The MXFP4 window analysis IS most of the "numerical half of Ozaki"

The Ozaki verdict named the unclaimed object: "choosing a FLOAT split so
limb products are exact by construction + shift machinery + error-free
recombination." Our own MXFP4 result — E2M1 elements are multiples of ½, a
k=32 block dot is an exact ≤13-bit integer, spreads fit width-8 windows —
**is that object at MXFP4 width**, measured. The unclaimed gap is narrower
than the ledger says: what remains is the recombination/normalization
constraint shape, not the split. Two of our own notes, same week, unjoined.

## G. The fusion experiment runs on our OWN wgpu stack at toy scale

Producer-consumer fusion ("stream FHE limbs through the sumcheck fold as
produced, pay traffic once") was filed as needing HPU RTL or CUDA serving
kernels. But fhegg's wgpu negacyclic NTT and the solver's wgpu matvec
already share a queue abstraction — **a BFV fold + a sumcheck fold on one
wgpu dispatch stream is a weekend-scale test of the fusion claim** on
hardware we have, before any FPGA. Missed because fusion arrived labeled
"hardware pillar."

## H. The house wound-classes are missing CLAUSES of the audit checker

"Refusal renders as the expected verdict" and "fail-open gate" are minted
breadstuffs wound classes. The audit theorem's checker `Chk` has exactly
this hazard: a checker whose parse failure renders as accept makes q → 0
silently. The Lean spec should carry a **fail-closed clause with teeth** —
a case where Chk errors and the theorem forces alarm — imported from the
wound-class discipline. Missed because wound classes live in "house memory"
and the theorem lived in "new research."

## I. Three tuple-compression findings are ONE lemma

Avigad's `combine.lean` restricted-bad-set trick, Celer's γ-fold for
vector-valued lookups, and the conditional CommitSurface-α-binding route are
the same object: compress tuples via challenge powers, define badness
relative to the conclusion, get linear bad sets. We recorded them pairwise
across three notes. One Lean lemma serves all three consumers (LogUp bus,
Celer adaptation, apex redesign) — and it is small.

## J. The spatial burst bound may already have a Lean leg

The audit lane found `OracleLogLinkedOpenedSampling.lean`'s `(1−radius)^t`
column-sampling bound and filed it as "spatial sampling within one committed
word — not the audit theorem." But the theorem's NEW lower-bound clause
(2026/541's 1/N single-path ceiling; spatial × temporal bursts multiply) is
exactly a spatial-sampling statement. The machinery distance from what
exists to the spatial clause should be checked before writing it fresh.

## The meta-lesson, again

Same shape as the missed-threads review: corrections and findings stay local
to the pillar that produced them. The fix is mechanical and we should adopt
it: **every time a construction lands (a theorem spec, a milestone, a
caveat), sweep the session's earlier findings against it once** — the sweep
that produced this note took one reread and found ten.
