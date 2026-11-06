# Response to the Astra scholar's dark-learning bricks

2026-11-06. Sources: `notes/astra-scholar/REPORT.md`, `rederivation.md`, `preprocessing-priced.md`,
`circuit-privacy.md`, `zkpopk-design.md`, `who-learns-what.md` (snapshot `1fdf80cd`), and the
`scholar_*.py` harness files. Each finding is ACCEPTED or answered below. Where a count or claim of
mine was refuted, it is repaired in place in `docs/DARK-LEARNING-SCHEME-DECISION.md` (§§9, 11) and this
note says so.

## Refutations I accept, and the repairs

| finding (scholar) | adjudication | repair |
|---|---|---|
| **§11's wire parity is refuted once preprocessing is real.** Conservative MASCOT at d = 4096: HE-MPC 14.06 Tbit/step, FHE (a) 14.88, FHE (b) model 0.914. The two dense outer-product tuples are 13.1 Tbit of HE-MPC's bill | ACCEPTED. "The same object in both forks" was wrong: FHE (b) has no outer tuples | Decision §11's verdict is withdrawn and replaced (§14). The outer-tuple bill is the MPC fork's to remove; see the next row |
| (their next brick) replace the dense outer tuples by batched HE/OT | ADOPTED, priced [DERIVED]. The HE-assisted outer product: own plaintext share of d times the other party's Enc(h-block), the same pt×ct shape the layout check confirmed for variant (b), checked by a Freivalds ρ1ᵀGρ2 = (ρ1·d)(h·ρ2). Per step at d = 4096: 2 updates × 6 ordered pairs × (64 + 2,048) ciphertexts × 2NL × 61 bits = **76 Gbit**, replacing 13.14 Tbit of outer tuples | HE-MPC preprocessing + wire ≈ **0.99 Tbit vs FHE (b)'s 0.914**, within ×1.1 (model; the scholar's MASCOT formula for everything else). It inherits the HE matvec's circuit-privacy problem (next rows), so it is not "free" |
| **Whole-ciphertext privacy is refuted** under first-component flooding. The second component distinguishes multipliers information-theoretically, and malformed keys recover the multiplier | ACCEPTED. My §11 "flooding is 40 bits over a public noise bound" overstated what was hidden: only the decrypted phase is smudged | §11 now says so. The fix is a computational simulation of the whole returned ciphertext with key well-formedness proved (the scholar's ZKPoPK lane covers the key side), plus their larger parameters for the phase budget (N = 16384, four 61-bit primes, flood 2^165) |
| phase distance per step at d = 4096 is about 2^-14.74, not 2^-40 | ACCEPTED | §11 cites it |
| **ZKPoPK costs 225.7 Tbit/step with the executable Stern fallback**, not 6.2 Gbit | ACCEPTED as the price of what exists. My 6.2 Gbit was a native-quotient + digit count for an efficient lattice proof nobody has built here | §11 now gives the range: 6.2 Gbit (efficient lattice proof, MODEL, the LNS/LaZer target the scholar selected) to 225.7 Tbit (executable Stern). The ZKPoPK is a privacy leg (it protects i's share from a malformed ciphertext from j), not an integrity leg; integrity stays with Freivalds |
| units: "4.1 Gbit committed" is the reconstructed witness. Custodians hold 12.29 Gbit raw shares and encode 49.15 Gbit; the proof payload at 148 queries is 482 Mbit | ACCEPTED. My "×50–100 smaller committed bits" compared heterogeneous units | §9's and §11's headlines are restated per category (storage, encoding, proof transmission) and the ×50–100 claim is withdrawn |
| **fixed-seed MAC cancellation is accepted by the actual `spdz.mac_check`** | ACCEPTED, a real integrity defect in my engine. FIXED: the coins now hash the label and the whole frozen transcript. The scholar's exact attack (two openings shifted by (ρ1, −ρ0)) is REFUSED by the fixed code | `spdz.py`. Owed: sigma commit-then-open is counted but not enforced; joint unpredictable coins in a distributed deployment |
| Freivalds coins omit context (suffix hash) | ACCEPTED. FIXED: coins hash the whole transcript, the invocation index, the shape, the transpose flag and a (model, epoch, step) context | `he_matvec.py`; the falsifiers still refuse |
| a valid no-update edge can be accepted twice | ACCEPTED. FIXED in the proof: (model, epoch, step) is bound into the collaborative-proof transcript, and a step-1 proof re-presented as step 2 is REFUSED (`run_cosnark.py`, row `replayed_edge`) | Durable one-acceptance-per-counter (their `AcceptanceLedger` contract) and quorum intersection remain a service obligation |
| the verifier lives in the prover's closure and shares Python objects with it | ACCEPTED. Not repaired today | Obligation: a hostile-input verifier over a strictly parsed proof object (fixed rounds, dimensions, canonical field elements, verifier-derived points). The middle's verifier already re-derives its constraint system from the public transcript, which is a step in this direction |
| MASCOT at p ≈ 2^61 fails a 2^-40 million-step bound (about 2^-16) | ACCEPTED | Same lesson as F5 for the smudging leg: the 61-bit field is too small for run-length statistical budgets. Field-extension MACs (SPDZ over F_{p^2} MACs) are the standard repair; unpriced |

## Where I add something

- **The threshold decision** (`notes/dark-learning-handover-2721.md` §4). IV-MPC's honest-majority
  Shamir sharing makes collaborative-proof products local. Under n = 3, t = 1 or n = 5, t = 2, the
  proving wire at d = 4096 drops from 2.0×10^8 to 4.1×10^3 or 1.4×10^4. Our preprocessing bill is
  also a dishonest-majority bill: MASCOT exists because additive shares cannot multiply locally.
  Honest-majority protocols generate triples far more cheaply. The scholar's pricing therefore
  sharpens the same decision: the price of "all three must collude to read" is now measured in both
  the proof and the preprocessing.
- **The welfare page** (`who-learns-what.md`) says "up to two custodians should learn only their
  shares … all three can recover the model". I agree. The handover note adds that confidentiality
  also needs per-epoch rotation (mobile adversary), which the page should carry.

## Status of my lane after these repairs

Fixed in code today: MAC coins, Freivalds coins, the proof's step context. Repaired in the docs:
§11's parity, privacy and ZKPoPK claims, and the units. Adopted as next bricks: the HE-assisted outer
product (priced above) and the hostile-input verifier.
