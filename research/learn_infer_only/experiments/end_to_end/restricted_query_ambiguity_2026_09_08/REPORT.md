# A nonvacuous continuing feature pair for the actual query policy

[EXECUTED] The actual sixteen semantic query rows admit an exact, small integer ambiguity witness inside the learner's int8 feature domain. A vector delta changes **39 real feature coordinates**, has maximum magnitude **4** and squared norm **94**, and satisfies **Y delta = 0 exactly over the integers**. Its padding coordinate is unchanged. An actual unregistered text query, “I have a strange payment in my statement”, has **w dot delta = 38**. [WITNESS.json](WITNESS.json) contains every coordinate and the complete paired histories; [PROOF.md](PROOF.md) gives the preservation argument.

[EXECUTED] The left history is the original six cached observations from the completed restricted-key learner. The right history perturbs the three card-arrival observations by delta, 2delta and 3delta, leaving the three cash-withdrawal observations unchanged. All resulting feature coordinates lie in [-77,77], and every final padded coordinate is zero. Each side has the same six teachings, class labels and two capacity-two expiry events. No new encoder or cryptographic execution was needed.

| Completed teaching round | Left withheld card-arrival score | Right score | Difference | All registered scores |
|---|---:|---:|---:|---|
| Revision 2 | 202,211 | 202,249 | 38 | Equal |
| Revision 4 | 399,367 | 399,481 | 114 | Equal |
| Revision 6, after both expiries | 404,646 | 404,836 | 190 | Equal |

[DERIVED/EXECUTED] Registered projections agree on **each individual issued input**, not merely on a selected aggregate. Consequently every linear combination of the sixteen registered queries agrees on every input and every common allowed additive teaching/expiry schedule. The concrete checker confirmed 96 per-input equalities and 192 class-memory equalities across all six events. Both final active card-arrival memories remain distinct. The withheld row is outside the full registered row span over F_p, certified by its nonzero dot product with delta modulo p.

[DERIVED/EXECUTED] Signed score ranges are preserved without changing p, Delta or noise. Every two-int8-input registered score is bounded by 2,520,950; the withheld query's bound is 2,467,610. Both are below p/2. The largest actual class-state coordinate magnitude is 151. The hidden score difference therefore cannot be explained by modular wraparound.

[EXECUTED] Construction used one 64×80 public integer lattice reduction, with the first returned row satisfying the witness conditions. LLL took 0.019 seconds; the entire construction took 0.103 seconds. It used the first 64 real feature coordinates and a fixed unregistered query selected before that reduction. All 64 returned rows were recorded, without another matrix, parameter search, model run or crypto oracle. A separate standard-library [verifier](verify.py) validates the exact certificate without LLL or NumPy; [VERIFICATION.json](VERIFICATION.json) records its passing result.

[SCOPE] This closes the nonvacuity gap for the **admitted int8 feature domain and this actual fixed query policy**. It does not exhibit two natural-language texts with these embeddings, establish membership of the perturbed vectors in the frozen encoder's image, prove natural-language state ambiguity, or test computational privacy. Ciphertext bytes and timing are not asserted equal. The conditional ring privacy construction, full per-input coalition query span and host/implementation/hardness limits remain unchanged. No previous source, runtime, key or model was modified.
