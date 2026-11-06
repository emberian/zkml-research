# IV-MPC (ePrint 2026/2721) read against the MPC fork: chaining, authentication, collaborative proof, handover

2026-11-06. Source: Dalskov, Kallesøe, Khoshakhlagh, "Authenticated Outsourced Incrementally Verifiable
MPC", read in full from the text extraction at
`/Users/ember/paperbin/dalskov-kallesoe-khoshakhlagh2026-authenticated-outsourced-ivmpc.txt`.

(An earlier version of this note, commit `c70f685c`, was written from a PDF that I rendered as six pages
only; that limit was my reader's, not the file's. This version replaces it. The Downloads copy of the
PDF is a Cloudflare challenge page, not the paper.)

The paper is squarely about our MPC fork. Its motivating example (§1.1) is "a system that regularly
updates a machine learning model based on new training data", run as reactive MPC in epochs:
[st_i] ← Π_MPC(F_i, [st_{i−1}], [x]) and [y_i] ← Π_MPC(G_i, [st_i]).

## 1. Side by side [READ for theirs, with section numbers; ours from the scheme decision §§9, 12, 13]

| | IV-MPC (2026/2721) | our MPC fork |
|---|---|---|
| privacy threshold | **honest majority, t < n/2** (§2.1). Needed "to reconstruct the degree-2t polynomials generated during the sumcheck phase" | **dishonest majority**: additive SPDZ, n = 3, privacy until all three collude |
| integrity | **full corruption** (t = n): "the adversary cannot forge a valid proof for an incorrect state update" | full corruption (§9, §12): the same goal |
| commitments | Pedersen vector commitments (DL), hiding; ElGamal/CL encryption for PoPCS (§3.1, App. B) | hash-based: per-custodian share-codeword Merkle roots over the 61-bit prime; hiding layer (§13) |
| post-quantum | **no** (discrete log; HSM-CL class groups) | yes (hash + lattice FHE keys elsewhere) |
| step proof | CSP + sumcheck: the witness X = (x, o, y), a gate zerocheck Σ eq·(L̃R̃ − Õ), and linear-form openings of X (§5.1) | the same shape: spine sumchecks + rank-1 checks; the middle's zerocheck over preprocessing triples + linear batch (§12) |
| products inside the distributed prover | **local**: Shamir shares of degree t multiply into degree 2t and are reconstructed in the clear because the round polynomials are public anyway (§5.2.1) | **Beaver multiplications** (additive shares cannot multiply locally): **99.8% of our proving wire** (1.57 M of 1.58 M at d = 64) |
| zero knowledge | Libra-style masking polynomial g = Σ g_i(y_i) for the sumcheck (§5.2.1); the linear-form openings are an uncompressed Σ-protocol with masked responses z = eX + r (§5.2.2) | layer 1 built (hiding PCS); layers 2–3 designed (commit the transcript, then a collaborative ZK-Ligero of the verifier's checks) |
| who compresses / recurses | **an untrusted public helper P\*** works on the public transcript: CSP compression, SPARK for the wiring matrices, and IVC via NARK + accumulation [BCMS20] (§5.2.2, §5.3) | nobody yet: each step's proof is checked directly, and chain verification is linear in the number of steps |
| chaining | inside the recursion circuit: C_old → C_new, accumulator update, sublinear checks of π_step and Π_old (§5.3) | parent commitment = previous child commitment, checked by the verifier per step (§9); carried openings under hiding (§13) |
| input authentication | the recursion circuit verifies an authority's signature σ on the input commitment C_X (§5.3; §1.3 footnote 5) | **missing**; added below |
| handover | DPVSS from PoPCS: outgoing parties reshare with publicly verifiable encrypted openings, plus a Lagrange consistency check against the **canonical** commitment C = [s]U1 + [r]U2 (§4.1). **Stateless**: every handover is verified against the latest canonical C (§4.2) | none: a static committee |
| concrete costs | **none** (no evaluation section in the paper) | counts at d = 64 measured and d = 4096 by formula |

## 2. What their design shows about ours

**2a. Our proving wire is the price of the dishonest-majority threshold, and they show it exactly.**
- With Shamir shares and t < n/2, every product in the sumcheck rounds is local: the parties compute
  degree-2t shares of the round polynomial and open it.
- Our additive shares need a Beaver triple per product. That is the 2.0×10^8 proving wire at
  d = 4096 (§12), and the reason the proof costs ×2.3 the step.
- Under their threshold our zerocheck wire would be only the round-polynomial openings: tens of
  elements per round instead of 4·L Beaver openings. [INFERRED from their §5.2.1 and our §12 counts.]
- **This is a decision for ember, not a bug.**
  - For n = 3, honest majority means ONE corrupted custodian learns nothing, but TWO read the mind.
  - Dishonest majority needs all three to collude, and pays ×~10^3 in proving communication for it.
  - A middle option: n = 5, t = 2 Shamir (two of five may collude). That keeps local products and
    raises the collusion bar to three of five independent custodians. Its online SPDZ-equivalent cost
    rises with n (resharing is n², openings n·(n−1)).
- The counts to decide it are below, in §4's experiment.

**2b. Adopt the public helper P\*: the host does the heavy public work.**
- Their split is that the MPC produces a zero-knowledge but uncompressed public transcript, and an
  untrusted helper in the clear compresses it and runs the recursion.
- **In our threat model the natural helper is the host.** It can do all the compression and recursion
  work without reading anything, because the transcript it receives is ZK. That makes the host useful
  without giving it the mind.
- The prerequisite is our ZK layers 2–3: the transcript must be ZK before it leaves custody. Their
  Phase 1 uses masked responses z = eX + r for the same reason.

**2c. Chaining becomes incremental.** Our verifier currently checks every step, so its work grows with
the number of steps. Their recursion circuit verifies the new step proof and the previous IVC proof
sublinearly, and folds the expensive PCS checks into an accumulator.
- A hash-based analogue exists in principle: accumulation without homomorphism (BCLMS21-style) or
  FRI/WHIR-based recursion over our 61-bit field.
- Its in-circuit cost (Merkle paths, codeword checks) is unpriced here. [INFERRED; no novelty claim.]

**2d. Input authentication: adopt it, now** (P5, provenance of experience).
- Their footnote 5: "If all the MPC nodes misbehave, nothing is stopping them from choosing new inputs
  for a previous state." Our spine commits x and our middle commits y as custodian-supplied vectors.
  Under the full collusion our proof is built for, the custodians choose the training data. Our proof
  shows the step was computed correctly ON WHATEVER INPUT THEY CHOSE.
- **Repair.** The data-provenance authority signs each input batch's commitment, and the step proof
  (or the recursion circuit, per 2c) checks the signature against pk_auth on (commitment, step index).
  - In our PQ hash-only design the signature is hash-based.
  - Or the authority publishes the batch Merkle root and the PCS opens against it.
- This is also where C11's welded absence attaches: the authority's batch root is what the absence
  proof is against.

**2e. Handover: their stateless trick does not transfer, because our commitment is not canonical.**
- Their canonical commitment C = [s]U1 + [r]U2 is linearly homomorphic. Resharing (s, r) leaves it
  unchanged, so each handover is verified against the latest C alone (§4.2).
- Our commitment is the tuple of per-custodian share-codeword roots. Resharing changes every root.
- **A post-quantum canonical anchor over F_p shares is an open construction here.**
  - DL commitments are not PQ.
  - Lattice (Ajtai) commitments are homomorphic only over short witnesses, while additive shares mod p
    are uniform. Digit decomposition restores shortness but breaks the homomorphism, because digits of a
    sum are not sums of digits.
- **Our design instead (not built):**
  - **A handover is one more step type in the same chain.** The outgoing and incoming committees jointly
    open their two share-tuple commitments at a random point and show the difference is zero:
    Schwartz–Zippel on the MLE, one linear constraint in the layer-3 inner circuit. It costs two PCS
    evaluations, under 1% of a step proof at d = 4096.
  - **Statelessness then comes from recursion (2c),** with handover as a second step type: non-uniform
    IVC, their §1.3 "non-uniform IVC" option.
  - **An outgoing committee that refuses to open stalls the chain.** That is a liveness failure, not a
    safety one, and it is fail-closed: the old committee keeps the state.
  - **A weight commitment that is also a handover endpoint has a third hiding life,** so HIDE ≥ 3t
    (`cosnark.LIVES`).
- **Their DPVSS reshares with publicly verifiable ENCRYPTED openings** (PoPCS: the opening is a
  ciphertext to the incoming party's key, plus a proof that it encrypts f(α)). We would need the PQ
  analogue: a lattice-encrypted share with a proof of correct encryption against our hash commitment.
  That is the same object as the scholar's ZKPoPK lane, and should be designed once for both.

**2f. Proactive refresh is a requirement.** Their §1.2 and footnote 4 apply directly to C22. Integrity
under the proof does not depend on the committee, but confidentiality does. A static committee
accumulates corruption risk over a long run, so **rotation every epoch belongs in our custody design.**
Its per-epoch cost is a resharing of W (n²·|W| ≈ 1.5×10^8 elements at d = 4096, n = 3) plus the
handover proof.

## 3. Things in their paper I would challenge

- **No concrete costs anywhere.** Every efficiency claim (linear-time distributed prover, logarithmic
  overheads) is asymptotic.
- **Final evaluation claims.** §5.1 has the prover "send three claims" l_y, r_y, o_y. Their ZK paragraph
  masks the sumcheck with g but, in what I read, does not say how those final evaluation claims are
  hidden (Libra also masks the witness polynomial). [READ: not stated in §5.2.1; I may have missed it in
  the appendices, which I skimmed.]
- **The input authority** is "semi-honest and independent of the MPC adversary", realized with blind
  signatures (§1.3). That is a new trusted party. In our setting it is the data-provenance authority
  P5 already needs, but its independence from the custodians is an assumption to name, not derive.

## 4. The threshold decision, counted (`cosnark_gates.counts_honest_majority_MODEL`)

Proving wire of the collaborative proof per step: ours as executed (additive, Beaver products) against
IV-MPC's choice (Shamir, t < n/2: local products, only round polynomials opened). The honest-majority
rows are a MODEL.

| d | additive n = 3, dishonest majority (executed formula) | Shamir n = 3, t = 1 | Shamir n = 5, t = 2 |
|---:|---:|---:|---:|
| 64: middle / spine | 1,575,336 / 10,308 | 2,508 / 468 | 8,360 / 1,560 |
| 4096: middle / spine | 201,330,690 / 639,768 | **4,134 / 936** | **13,780 / 3,120** |

**Under honest majority the collaborative proof's communication is essentially free:** ×5×10^4 less
at d = 4096. Our dishonest-majority threshold, collusion of all three to read, is what makes the proof
cost ×2.3 the step.

What the table does not price:
- the MPC step itself under Shamir (degree reduction per multiplication, different malicious-security
  machinery);
- the n² resharing per epoch at n = 5.

What is not a matter of cost: **at n = 3, t = 1, two colluding custodians read the mind.** The options
for ember:
- **(i)** n = 3 additive: all three must collude to read; the proof costs ×2.3 the step as built, or
  ×0.15 with the modelled levers of §12.
- **(ii)** n = 5 Shamir, t = 2: three of five must collude to read; the proof is free in communication;
  the step and the resharing grow with n.
- **(iii)** n = 3 Shamir, t = 1: cheapest; two of three read.

My recommendation is (ii) if five independent custodians are available, otherwise (i) with the §12
levers. That is a recommendation about whose collusion is plausible, which is ember's call, not a
count's.
