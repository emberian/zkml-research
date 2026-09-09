# Anchored sparse first external product

[EXECUTED] Lean emits the actual saved first external-product relation as 2,048 rows ×279 witness columns, with46 public scalars and295 arithmetic constraints after the existing assertion-sharing pass (330 before it). The complete trace is2,285,568 bytes. Nine selected actual rows, including the sparse sign boundaries and component boundaries, pass the interpreter; altered output, raw low bits, and anchor are refused. See `artifacts/emission.json` and `results/emission.log`. The separate native consumer owner performs the full proof; this package does not launch crypto or claim a whole PBS proof.

[PROVED] `Theory/SparseNegacyclic.lean` defines ordinary signed negacyclic coefficient convolution by a finite sum. `certificate_sound` is generic over a commutative ring and arbitrary N,a,b with0<a≤b≤N: one derived anchor and the two-shift recurrence determine every coefficient. `prefix_certificate_sound` specializes N512/a44/b162 and derives the anchor from every checked weighted-prefix transition. It never cancels2. `anchor_omission_fails` exhibits the actual2^24 half-modulus ambiguity even if the signed wrap recurrence is also imposed. `prefix_certificate_inhabited` supplies the mathematical premises for every input polynomial.

[PROVED] `Compiler/TfheSparseRow.lean:row_sound` lifts accepted BabyBear arithmetic to canonical24-bit integers and equations over `ZMod16777216`. Every radix64 digit is range-checked; signed carries have3 checked bits and offset4; no-field-wrap bounds are derived for each arithmetic column. The final source aliases the existing24 output bits into six raw radix64 digits with eight low zero bits, proving raw output=256×normalized output as an integer.

[PROVED] `Compiler/TfheSparseCertificate.lean:whole_sound` joins the actual source to the generic convolution. Its `Linked` premise contains only shared-array/index/flag identities, not a prefix transition, anchor equation, recurrence, or desired convolution. `Compiler/TfheSparseTeeth.lean:whole_premise` inhabits the complete accepting/linked premise with the exact index-dependent flags; separate scale and anchor refusal theorems are pinned. All33 theorem declarations have exact guarded axiom output; only Lean's standard axioms occur. `results/validation.json` records the single-module checks; a root closure build remains an integration task.

[DERIVED scope] This is the selected saved digit polynomial s=+1 on[0,44),0 on[44,162),−1 on[162,512). Each of the four arbitrary active raw key polynomials is reduced modulo2^24, H=s*K is proved there, then output=256H is represented modulo2^32. Raw GGSW row7 is selected by the external public reader. The other decomposition polynomials must be zero and the selected digits must equal256s; the reader checks this exact fixture shape. The source is not a certificate for arbitrary digit polynomials, an FFT implementation, evaluation-key correctness, noise, or a complete PBS.

[SOURCE / TCB] The owner reader at `../consumer/src/main.rs:rows` reconstructs the public table from canonical raw GGSW/output bytes and the saved digits. It checks the complete coefficient/component coverage, digit pattern, low8 output bits, signed previous index atj0, both shifted key permutations, shared weighted prefix arrays, and flags. `Linked` expresses this remaining reader correspondence explicitly. The generic signature fold and existing assertion-sharing optimizer exclusively generate the AIR; Rust supplies no constraint expressions. JSON/binary parsing, the public reader, native witness generation, and the proof backend are not proved by this package.

The46 public fields are:

| Indices | Meaning |
|---|---|
|0–7|id,component,j,first,plus44,plus162,prefixPlus,prefixMinus|
|8–11|K[j], radix64 little endian|
|12–15|K[(j+512−44)%512]|
|16–19|K[(j+512−162)%512]|
|20–23|Y[j]|
|24–27|Y[j−1], or−Y[511] mod2^24 atj0|
|28–31|S[j]|
|32–35|S[j+1]|
|36–39|S[512]|
|40–45|raw u32 output, radix64 little endian|

[EXECUTED] Reproduce the existing module checks with `python3 check.py` from this directory. It uses the owned build overlay and leaves companions read-only. Emit with the exact `lake env`/`LEAN_PATH` invocation recorded in `results/commands.txt`; the emitter takes `NEW_OUTPUT_DIR PUBLIC_ROWS_JSON`. The original public fixture, companion trees, and all predecessor sources remain unchanged. `proposal.patch` contains only the six new modules and standalone emitter; dependencies include the frozen `Compiler.BfvQueryMul` and `Compiler.AirAssertionShare` packages.

[EXECUTED] All six final module checks passed with empty logs and 33 guarded pins. Read-only `git apply --check proposal.patch` passed on minidregg 6937394e1dc2c2aaff986c7d4b3a258aca5d16fd / Lean4.30.0. `SOURCE_PINS.json` also records the frozen off-tree query/arithmetic/sharing/integer-emission dependencies and exact public rows.
