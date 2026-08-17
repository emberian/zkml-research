# What is genuinely open

2026-08-16. Written from live context. **Ordered by what it blocks**, not by
interest.

## Blocking the binary-field path

1. ⚑ **Bind the ordered basis in the additive-FRI transcript.** *Three
   independent sources agree*: our GF(16) counterexample
   (`keystone_basis_ambiguity` — one word, one domain, two orderings of the
   same basis, two different committed tables), ring-switching's handoff where
   it makes `Extractable` **FALSE**, and **Diamond–Posen's own Corollary 4.5.**
   The controller today binds a sponge `domainId`, *not a basis*. **Nothing
   should recurse over additive FRI until this lands.** *(A lane is on it.)*
2. **Two additive tower conventions coexist and will disagree** —
   `AdditiveFriTower` folds the **reversed** basis while the multilinear layer
   peels **LSB-first**. Unifying needs the deployed index layout; deliberately
   not decided silently.

## The composition operator the library lacks

3. ⚑ **The partial-sumcheck realizer** (`scChain_*Honest_partial` at `k ≤ m`).
   **The soundness half is already done** — `sumcheck_soundness` is `{v d}`-
   generic with a terminal clause naming no cube. **It unblocks five of five
   target systems.** *(A lane is on it.)*

## The biggest measured available win

4. ⚑ **Sumcheck-batch the reduced opening — ×2.05 per turn**, named in
   `WRAP-NATIVE-HASH-DECISION.md` and never taken. **It is the precondition
   that makes every hashing argument true** (a free hash goes ×1.57 → ×4.5).
   *(A lane is on it.)*
5. ⚑ **The leaf is too small.** `K = wrap/leaf = 26.9`; SP1's and OpenVM's is
   **< 1**. *Nobody swaps proof systems between layers — they make the leaf
   carry more.* **This is the architectural item and nobody is on it.**

## Open holes with exhibits and no closure

6. **vFHE cross-limb, hole B (expressibility)** — `⌊t·x/Q⌉` reads the CRT
   reconstruction, so there is **no per-limb equation to bind**. Exhibited;
   unpriced. Single-prime dissolves it, gated on H1.
7. **`ε_chk` cannot be instantiated limb-locally** — a faithful-execution
   checker must decide *provenance*, and provenance is invisible to any
   per-limb check **by construction**.
8. **`max_log_arity` is unpinned** in the recursion verifier, same mechanism as
   the `num_queries` hole. ⚠ **Direction and magnitude NOT derived — do not
   quote a number.**
9. **`ε_beacon`** — we hold the grinding *mechanism*, not a beacon model.

## Needs a decision from ember

10. ⚑ **The `num_queries` pin does not reach breadstuffs.** It is landed in
    `~/dev/plonky3-recursion` at `52e1fab`; `breadstuffs/Cargo.toml:370-373`
    pins an older rev. **Pushing is outward-facing, so a lane correctly
    stopped. Until it is pushed and the rev bumped, the hole is open in
    breadstuffs.**
11. **Whether to cut over `permEmissionNarrow`** — 1.076× per batch, **1.000×
    in the tower**, for a VK rotation and a chip AIR re-emit. *My read: not
    worth the flag day alone.*
12. **Whether to drop the blowup** — ⚠ **my read is NO.** `lb=6` is the
    **minimum of an iso-security grid** by 1.5–3×, and dropping it is **×3.21
    worse per turn** once the wrap is counted.

## Measurement debt

13. **`ThreadPool::install` needs re-pricing** — advertised 2.2–2.5× from the
    laptop, **measured 1.14–1.80× on hbox.** It was called "the biggest
    untaken lever"; that claim is now in doubt.
14. **The latency figure's phase shares are still laptop-derived and
    pre-batching.** Re-deriving them on hbox is the next measurement.
15. ⚑ **The arithmetization lever for hashing, unmeasured**: the same two
    primitives cost **102× in R1CS, ~31–56× bit-decomposed, ~3.2× under a
    lookup argument — inside the crossover band.** ***R is a property of how
    you arithmetize, not of the hash*** — **and we already hold LogUp.**
    *Highest-value open measurement on that axis.*

## Standing residuals (older, still true)

16. **H1** — does the 61-bit joint-representation point survive a 2.4-bit
    margin? *H2 collapsed INTO it; they are not independent gates.*
17. **Our FHE parameter point may not be post-quantum at all** — (N=4096,
    log q=109, t=2²⁰) is a *classical*-line set; Apple ships 83 bits at
    N=4096 for `.quantum128`.
18. **`[ACC-extract]`, `[LOGUP-ADDRESS-LINK]`, `TwistContinuity`** — named
    seams, unproved.
19. **Knowledge soundness**, tree-wide: most soundness theorems quantify over
    a *given* witness. Spartan is an argument **of knowledge**; the extractor
    story is `Unit`-witnessed in places.
