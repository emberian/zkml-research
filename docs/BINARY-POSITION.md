# The binary-field position: our layer is field-agnostic, and the short path is not Ligerito

2026-08-14. Full analysis: `notes/binaryspartan-position.md` (1,203 lines).

## ⚠ Same correction as the sibling lane: BinarySpartan EXISTS

This lane also could not find it and said so. **It is in the eprint review
queue** — ember holds the title page, abstract, and EF benchmark slide — so by
construction it is absent from every mirror, author listing and repo search.
**Two independent lanes made the same inference from a sound search.** The
class is now well enough attested to be a standing rule: *absence from a
published corpus is evidence about the corpus, never about reality, and a
paper described as unpublished is not evidence at all.*

## ⚑ But the benchmark scrutiny stands, and it matters

- **The EF harness (`privacy-ethereum/csp-benchmarks`) runs on an M1/8-core,
  not an M4 Max.** Measured there: Flock **33.93 ms**, Binius64 **67.29 ms** —
  and the slide's "Vega 44.2" corresponds to `spartan2` at **541.72 ms**.
- ⚑ **"Vega" is P-256 + Hyrax — discrete-log, NOT post-quantum.** A
  post-quantum comparison table with a discrete-log entry in it.
- ⚑ **Flock's own verified abstract (eprint 2026/1329) reports 82k BLAKE3/s on
  a SINGLE M4 Max core**, against BinarySpartan's 410k on twelve — **2.2–2.4×
  faster per core, and >660k on ten cores, i.e. it wins outright in
  aggregate.**
- **The 6.2 ms latency and 219k h/s throughput claims differ by ~41×** — which
  is the *batched-vs-single* gap, the same shape as Thaler's `1/B + 1/n`
  overhead being 0.22% at B=512 and 100% at B=1. **Both figures can be true;
  quoting them together as one system's characterization is the error.**
- ⚑ **And "Poseidon was broken" is not what happened.** The Poseidon Initiative
  pivoted **Poseidon2 → Poseidon1 (MDS)** over a margin-eroding attack, still
  runs through Dec 2026, and there is **no institutional EF artifact — one
  researcher's thread.** **leanVM today is KoalaBear: a 31-bit PRIME field.**

## ✅ THE DELIVERABLE: 13 of 18 keystones transfer with NO new mathematics

**Decisive census: 0 `IsPrimitiveRoot`, 0 `rootsOfUnity`, 0 `primitiveRoot`
anywhere in the tree.** Every Reed–Solomon code is over an abstract
`dom : ι ↪ F`. ⚑ **The usual reason a proof system is prime-pinned — a smooth
multiplicative subgroup — never applied to us.** The prime pins that exist are
`ZMod 5/7` *teeth* and a BabyBear *deployment* layer; **never a theorem
binder.** Sponge indifferentiability is field-*free* (`[AddCommGroup Rate]` =
XOR), and the degree-3 rung was **already built char-2-deliberately.**

## ⚑⚑ ONE WALL, AND IT IS A VACUITY TRAP WAITING TO SPRING

`Selvage/Proximity.lean:178` — `FoldingData` carries **`two_ne : (2 : F) ≠ 0`
as a STRUCTURE FIELD.** That is **uninhabitable in characteristic 2**, so
**every theorem over it goes VACUOUSLY TRUE, on a green build, the moment
anyone "instantiates it at a binary field."** A whole binary-field port could
land, compile, pass its axiom pins, and prove nothing.

**Its replacement already exists and is proved.** *This is the single most
important line in the analysis.*

## The short path — and it is not Ligerito

**BaseFold on the additive tower → then ring-switching.**

⚑ **Ring-switching is a COMPILER with security-preserving reductions** (Thm 3.5
proved by *constructing an emulator*) — **precisely and only what Selvage is**
— and **Diamond–Posen's own stated compilation target is "a characteristic-2
adaptation of BaseFold."** ***Step 1 produces exactly what step 3 consumes.***

**Ligerito cannot compose from what we hold**: ours is FRI-shaped (ℓ=2 affine
line); Ligerito needs interleaved codes, column distance, tensor coefficients
and column openings — all absent. ⚠ **And Ligerito is an unrefereed note with
two errata in its error bound, both in the favourable direction.**

**The real gap is ring-switching's connectors**: no `Basis` of an extension
over a subfield exists in 400 files, and `liftWord` points the wrong way.

## Corrections to my brief

- **The binary cone is NOT unwired** — it is consumed by 4 `Compiler/` and 3
  `Assurance/` modules, with a real proved multi-round bound
  `m·2^(ℓ−1)/|F| + (1−τ)^q` in **`AdditiveFriQuery.lean` (836 lines)** — not
  the file I named.
- **`HalfThresholdFriTower` is not binary at all** (`CharP` count 0).
- **The `Phalanx` in `~/paperbin` is the wrong paper** (FHE ciphertext
  packing); the right one is eprint 2021/1263.

## Who else is doing this

**Exactly one group: ArkLib + CompPoly** (EF-funded, Quang Dao, active this
week). Clean is structurally prime-only (`[Fact p.Prime]`); soundcalc-lean's
`FieldParams` carries a **primality proof**. **Binius64 (632 Rust files) and
Flock carry zero formal content — not even a differential test.**

**They are ahead on ring-switching and composition. But their FRI-Binius has
no soundness statement at all (`-- TODO: state RBR KS`), and there are 33
`sorry`s in the Binius leaves — against our 0.**

## Repo defects surfaced en route

⚑ **Two `Assurance/Tower256AdditiveFri*` modules are VACUOUS at positive
height** — `merklePcs_empty_of_positive` *proves their carrier type empty.*
Plus `docs/SELVAGE-COMPLETE.md:155-159` is refuted by
`jointGameFamily_impossible` while `:106-107` calls landed work open, and
stale docstrings in `AdditiveNTTTransform.lean` would mislead an auditor into
thinking the additive cone **assumes** a proximity gap when it **proves** one.
