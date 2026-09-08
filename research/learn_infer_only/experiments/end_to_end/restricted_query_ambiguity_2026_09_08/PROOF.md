# Exact preservation under continuing additive learning

[DERIVED — statement] Let Y be the actual 16×577 integer query matrix in the frozen restricted-query registry. Let delta be the integer vector in WITNESS.json. The checked identities are

`Y delta = 0` over the integers, and `w dot delta = 38`,

where w is the actual cached unregistered query vector for “I have a strange payment in my statement”. The final padded coordinate of delta is zero, and its support consists of 39 coordinates strictly below 576.

For any paired input sequence satisfying `x'_j = x_j + a_j delta`, and any common finite integer coefficients c_j,

`Y (sum_j c_j x'_j) = Y (sum_j c_j x_j)`.

The unregistered difference is exactly `38 sum_j c_j a_j`. These are integer identities, before taking residues, and hold regardless of how many additive operations produced the coefficients.

[DERIVED — proof] Distributivity gives

`Y(sum c_j x'_j − sum c_j x_j) = sum c_j a_j (Y delta) = 0`.

Applying w instead gives `sum c_j a_j (w dot delta) = 38 sum c_j a_j`. This proves both claims. Equivalently, an induction starts at equal zero projections. A teaching step adds vectors with equal Y projections. An expiry subtracts the corresponding originally issued vectors, also with equal Y projections. Each step preserves equality. The complete original-input correspondence is required; this is not an assertion about arbitrarily mismatched expiries.

[DERIVED — complete recipient-span consequence] For every coalition coefficient vector lambda, `lambda^T Y x'_j = lambda^T Y x_j` for each issued input j. Hence the entire coalition row span agrees on every input and every common allowed additive combination. This is stronger than equality of the final class means. In the constructed pair, class labels, counts, event order and expiry identities correspond exactly, so all deterministic rankings of those same means also agree. This statement concerns projection outputs plus that common metadata, not equality of ciphertext bytes or timing traces.

[DERIVED — strict withheld direction] If w belonged to the row span of Y over F_p, then `w dot delta` would vanish modulo p because every row of Y annihilates delta. But 38 is nonzero modulo p=28,439,893. Thus w is outside even the full registered coalition's F_p span. Its changing score is not padding-only hidden information or a renamed registered projection.

## Instantiation in the admitted feature domain

[EXECUTED] The left sequence is the original six-observation feature fixture, three examples each for `card_arrival` and `cash_withdrawal_charge`, interleaved in that order. The right sequence adds delta, 2delta and 3delta to the three card-arrival vectors and changes no cash-withdrawal vector. Both sides have the same class-specific window capacity two and the same two expiry events. The right vectors have maximum absolute coordinate 77, and their final coordinate remains zero, so all are admitted by the existing int8 feature transport. The largest feature perturbation is 12. The largest actual class-state coordinate magnitude across both histories is 151.

[EXECUTED/DERIVED] For the card-arrival memory, the live perturbation coefficient sums are 1, 3 and 5 after complete rounds; its withheld score differences are therefore 38, 114 and 190. Registered score differences are all zero throughout. Cash-withdrawal state differences are zero throughout. The final active memories remain distinct after the first observations have expired.

[DERIVED/EXECUTED — signed interpretation] Every registered query obeys the same public bound used in the executed learner: for any two admitted int8 vectors, the score magnitude is at most `2*127*max_i ||Y_i||_1 = 2,520,950`. The withheld query's corresponding bound is 2,467,610. Both are strictly below `floor(p/2)=14,219,946`. Thus the exact signed equalities and differences cannot be artifacts of modular score wraparound. The unchanged ring parameters, noise cutoff and encoder scaling are not modified.

[EXECUTED] `verify.py` is a separate standard-library integer checker. It verifies the source/fixture hashes, reconstructs the withheld query directly from the saved NumPy integer array without NumPy or LLL, checks all 16 annihilation identities and the withheld dot product, and reconstructs all six updates and both expiries. It confirms 96 per-input registered score equalities and 192 class-memory score equalities. No Lean theorem is claimed here: the preservation proof above is elementary integer linearity with an independently checked concrete witness.

## Scope of the construction

[SCOPE] The right vectors are admitted bounded feature vectors; no pair of natural-language texts producing these two feature sequences has been exhibited. In particular, this does not establish that the right sequence lies in the image of the frozen E5 encoder. The left texts and both feature sequences are public construction data.

[SCOPE] Equal authorized projections make the pair nonvacuous for the conditional fixed-query construction's message domain. They do not make the raw public ciphertexts equal, prove computational indistinguishability, establish a lower bound against domain-specific recovery, or remove implementation, host, timing and cryptographic-hardness assumptions. No ring encryption, decryption, private-key read, model execution or attack test was performed in this package.
