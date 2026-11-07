# Threshold reveal for the key-generation seed: a design, not built

2026-11-06, gen 4. Root decision: keep commit-reveal for now, with selective-abort bias carried as a named ledger
term, **ε_abort = (k + 1)·p** for k recorded aborts (decision doc §21). This page designs the alternative.

## The problem being removed

In commit-reveal the last revealer computes the seed before revealing. If it dislikes the seed it withholds, takes
the blame, and the ceremony reruns: each abort is one more draw. An event of probability p over the seed can then be
forced with probability up to (k + 1)p.

## Design: PVSS-dealt coins, threshold reconstruction

Each custodian's coin is fixed and recoverable by the others **before anyone can compute the seed**, so withholding
no longer changes the outcome.

1. **Deal.** Custodian i draws r_i and posts a publicly verifiable secret sharing of it to the ledger.
   - Shamir, threshold κ of n, encrypted to each custodian's registered transport key.
   - A NIZK that the encrypted shares lie on one degree-(κ−1) polynomial whose constant term is committed as
     C_i = Com(r_i). This is the Schoenmakers/SCRAPE family [INFERRED from memory, not re-read].
   - Everyone verifies every dealing. An invalid dealing excludes that dealer's coin; it does not restart.
2. **Close.** Once n dealings are posted, or a deadline passes, the ledger fixes the set D of valid dealings.
   **seed = H(epoch, {C_i}, {r_i : i ∈ D})** is now determined, even though nobody knows it yet.
3. **Reveal.** Each custodian posts its r_i, checked against C_i. A missing r_i is reconstructed from any κ
   decrypted shares (decryption is proved) and is never re-drawn. The seed cannot change after step 2, so aborting
   in step 3 buys nothing.

**What it needs.**
- **κ.** Privacy of r_i before close needs fewer than κ corrupt holders; liveness of reconstruction needs at least κ
  honest ones. With n = 3, κ = 2 works only if at most one custodian is corrupt. That is an honest-majority
  assumption for seed fairness. It is weaker than 3-of-3 custody's tolerance for the weights, and must be stated as
  such.
- **A coalition of two** can reconstruct the honest coin before close and then decline to close. If the ledger rule
  is that an epoch whose dealings stall gets re-dealt, the selective abort comes back. The rule must instead be:
  **close at the deadline with whatever valid dealings exist, never re-deal.** The honest custodian's own coin is
  always in D, which keeps the seed uniform against any coalition that cannot read it, i.e. fewer than κ.
- **Cost per ceremony** (once per epoch): n dealings of n encrypted shares plus one NIZK each. That is a few kB, and
  negligible next to the 10 Mbit key proofs.

## The other option: a delay function

seed = VDF(H(reveals)), with a delay longer than the reveal deadline. The last revealer cannot evaluate the seed in
time to filter, and needs no honest-majority assumption. It does need a VDF with a trusted or class-group setup and a
calibrated delay against the fastest adversary hardware; mis-calibration silently restores the bias.

## Recommendation

If 3-of-3 custody must also hold seed fairness against two corrupt custodians, neither design gives it outright:
- PVSS needs an honest majority;
- a VDF needs calibrated hardware assumptions.

The cheapest honest path is the current one: keep commit-reveal, record every abort, and budget (k + 1)·p. Move to
PVSS with deadline-close when the custodian set grows to n ≥ 5, where κ = 3 tolerates two corrupt custodians and the
fairness and custody thresholds come closer together.
