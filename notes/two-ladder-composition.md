# The two vFHE ladders compose — and the composition solves the leakage oracle

2026-08-13. Ember's observation: stark-in-fhe and fhe-in-stark "achieve very
different constructional outcomes" — so build both. Working that through, it
is better than both-separately: the composition resolves the worst open
problem each has alone.

## What each achieves (from the Laminate/719 read)

- **SNARK-over-FHE** (719 line: prove the *ciphertext operations* were
  executed correctly): **publicly verifiable** server-work integrity. Anyone
  — the network, an auditor, a slashing contract — checks that the FHE
  engine did the work it was paid for. No plaintext contact, no leakage,
  composes cleanly with commit-then-audit sampling. What it does NOT give:
  any statement about the *plaintext* semantics (garbage-in-ciphertext,
  faithfully processed, verifies fine).
- **FHE-over-SNARK** (Laminate: homomorphically evaluate the GKR prover;
  prove the *plaintext relation*): the client with sk learns the actual
  computation on the actual data was right — the semantically strong
  statement. What it costs: **designated verifier** (only sk-holder), and
  **one bit of leakage per observed verdict** — which under public
  commit-then-audit becomes a leakage oracle (my flag from the Laminate
  read, left unresolved).

## The composition

Run both on the same evaluation:

1. The server's FHE evaluation (payload AND the homomorphic GKR-prover
   evaluation — which is itself just more ciphertext operations) is covered
   by the **public** SNARK-over-FHE layer, sampled under the audit game.
   Public verdicts, no plaintext contact, **zero leakage by construction**
   — the audit game runs entirely on this layer.
2. The client privately decrypts the Laminate transcript and checks the
   **semantic** claim. Its verdict never needs to be public: slashing and
   reputation ride layer 1, so the one-bit oracle never opens.

Different failure modes covered: layer 1 catches a server that skips or
corrupts ciphertext work (including corrupting the blind proof
computation); layer 2 catches wrong-circuit/wrong-input at the semantic
level, blind. And the layering is not double-paying: layer 1's statement
INCLUDES layer 2's prover work, so the marginal cost of adding Laminate
under an existing SNARK-over-FHE audit regime is Laminate's own overhead
(5-67x estimated, amortized by the client checking only when it cares) —
while the audit regime's cost is sampled, per the economics pillar.

**Claim status: [mine], design-level, unpriced.** The pieces are all read
(Laminate trust model, 719 protocol, the audit theorem) but nobody has
stated this composition; the closest is Laminate's own Remark 2.6 noting
FHE-over-SNARK resists IND-CPA-D attacks that SNARK-over-FHE invites —
which slots in as a third complementarity: the layers also cover each
other's *cryptographic* attack surfaces.

Next: price it (layer-1 coverage of the GKR-prover evaluation is the new
term — how much ciphertext work does homomorphic GKR add for 719-style
proving to cover), and check whether Laminate's noise-provisioning floor
(+32 bits for base) interacts with the audit-sampling floor I flagged.
