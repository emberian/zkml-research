# Custody handover: ePrint 2026/2721 (IV-MPC), read against our collaborative proof

2026-11-06. Source: `/Users/ember/Desktop/2026-2721.pdf`, provided by ember. **That file contains only
pages 1–6**: the abstract, §1 introduction, Figs. 1–2, and §1.3 up to "MPC friendliness". The PoPCS
definition and construction, the distributed CSP/sumcheck proof system, the handover protocol, the
security model and all cost tables are on later pages that I have not read. Everything below about
those parts is tagged [CLAIM, abstract] or [INFERRED]. The ePrint PDF itself is behind a Cloudflare
challenge that my headed-browser fetch could not pass. The copy ember first named, in
`~/Downloads/2026-2721.pdf`, is that challenge page, not the paper.

Paper: Dalskov, Kallesøe, Khoshakhlagh, "Authenticated Outsourced Incrementally Verifiable MPC".

## What the pages say [READ, pp. 1–6]

- **Setting** (§1.1, Fig. 1). Reactive MPC in epochs. For epoch i, [st_i] ← Π_MPC(F_i, [st_{i−1}],
  [x_1..x_m]) and [y_i] ← Π_MPC(G_i, [st_i]). Their motivating example is exactly ours: "a system that
  regularly updates a machine learning model based on new training data".
- **The problem** (§1.2).
  - Long-lived secret state is exposed to adaptive corruption, so shares must be refreshed and
    committees rotated (proactive security, [HJKY95]). Footnote 4: a corrupted committee at epoch e
    "does not hold the secret shares for epoch e + 1".
  - Naive public verifiability must prove the whole chain st_i = F(st_{i−1}, …), st_{i−1} = …, which
    "quickly gets out of hand", and must also "track the cryptographic chain of custody to ensure each
    committee legally received the valid state from the previous one" (p. 4).
- **Contributions** (p. 4):
  1. **PoPCS**, a private-opening PCS: "an incoming committee prove[s] that they received a valid
     resharing of the secret state … without learning the underlying state".
  2. A distributed proof system for state transitions from compressed Σ-protocols and sumcheck.
  3. **Stateless handovers**, decoupled from the horizontal IVC (Fig. 2): "because resharing a state
     does not change its value, we can anchor the vertical handover proofs to the canonical state
     commitment produced by the most recent MPC update … verifying the latest handover suffices"
     (p. 5).
- **Construction choices** (§1.3, p. 6):
  - π_i = (π^G_i, π^F_i), with π^F by IVC [Val08] over st_i = F^(i)(st_0, w_i);
  - **input binding** by a trusted signer: w_i carries (x_{i,k}, σ_{i,k}) with
    verf(pk_auth, x_{i,k}‖i‖k, σ) = 1, because "if all the MPC nodes misbehave, nothing is stopping them
    from choosing new inputs for a previous state";
  - non-uniform IVC or universal circuits when F_i varies;
  - **MPC-friendliness** via compressed Σ-protocols [AC20]. The page ends there.

## What it means for our program

**1. Our commitment is share-dependent, and that blocks their stateless handover.** [INFERRED]
- Our collaborative PCS (decision §9) commits W as the n-tuple of each custodian's share-codeword root.
  Re-sharing W (proactive refresh, or a new committee) changes every share and so every root. The
  commitment is not canonical in the state.
- Their stateless handover needs a commitment that resharing leaves unchanged: a "canonical state
  commitment". A linearly homomorphic commitment gives this. With per-party Com(w_i; r_i) whose sum is
  Com(w; Σ r_i), resharing (w, r) jointly leaves the sum unchanged, and an incoming committee can prove
  its new pieces sum to it. I expect their PoPCS is of that kind. Their use of compressed Σ-protocols
  suggests discrete-log commitments [CLAIM, inferred from the abstract and §1.3; construction not
  read].
- **For us that route has two obstructions:**
  - **Post-quantum.** DL-based homomorphic commitments are not PQ. Our custody threat includes harvest
    now, decrypt later (C22).
  - **Share-shortness.** Lattice (Ajtai/SIS) commitments are linearly homomorphic only over short
    witnesses. Additive shares mod p are uniform, not short. Digit decomposition restores shortness
    but breaks the homomorphism, because digits of a sum are not sums of digits.

  So a PQ canonical anchor over F_p shares is an open construction. I make no claim that one
  doesn't exist.

**2. What we can do instead (DESIGN; not built).**
- **(a) Handover as a chain step.** A handover is one more kind of step in the SAME chain: the old and
  new committees jointly open their two share-tuple commitments at a random point and show the
  difference is zero.
  - That is Schwartz–Zippel on the MLE, soundness log₂|V| / |F_ext|.
  - The hiding PCS of §13 hides the two values, and the equality is one linear constraint in the layer-3
    inner circuit.
  - Cost per handover: two PCS evaluations, i.e. O(√|W|) proof elements. At d = 4096 that is under 1%
    of a step proof.
  - The verifier then follows one chain mixing horizontal steps and vertical handovers. That is
    STATEFUL: linear in their number, unless the chain is folded by recursion/IVC. Folding treats the
    handover as just another step type (non-uniform IVC). We lose their stateless-anchor shortcut but
    keep a PQ, hash-only design with no hashing inside the MPC.
- **(b) The old committee's last duty.** In (a) the outgoing committee must take part in the equality
  opening before it erases. An outgoing committee that refuses to cooperate stalls the handover. That
  is a liveness failure, not a safety one, and it fits fail-closed custody: no accepted handover means
  the old committee keeps the state, and the chain does not advance.
- **(c) The hiding lives.** A weight commitment that is also a handover endpoint gets a third life
  (child, handover source, parent), so HIDE ≥ 3t and the mask rows split three ways (`cosnark.LIVES`).
  This is a direct consequence of §13's design point.

**3. Adopt their input binding, now.** Our middle proof (§12) commits y, and the spine commits x, as
custodian-supplied vectors. Under full collusion the custodians can choose inputs. That is P5,
provenance of experience, and their footnote-5 point exactly. **Repair:** every training input arrives
signed by the data-provenance authority, verf(pk_auth, x‖step‖k, σ) = 1, and the step proof checks the
signature on the committed input. In a hash-only PQ design that is a hash-based signature inside the
inner circuit, or the authority's commitment to the batch Merkle root that the PCS opens against.
This also gives C11's welded absence a place to attach: the authority's batch root is what the absence
proof is against.

**4. Proactive refresh is now a requirement, not an option.** Their §1.2 argument applies directly to
C22: integrity under the proof does not depend on the committee, but confidentiality does, and a
static committee over a long run accumulates corruption risk. Our decision §3 named three custodians
in independent trust domains and said nothing about rotation. **Rotation every epoch** (resharing,
plus (a)'s handover proof) belongs in the custody design. Its per-epoch cost is one resharing round
(n² · |W| elements: 1.5×10^8 at d = 4096, n = 3) plus the handover proof.

## What I could not check (pp. 7+), and would need to

- PoPCS: its definition (what the incoming committee proves, and against what anchor), its commitment
  scheme, field/group, and whether it is PQ.
- The distributed CSP + sumcheck proof: corruption threshold, MPC-friendliness, cost per state
  transition.
- The handover's security model: adaptive corruption across epochs, erasures, and what "stateless"
  costs per handover.
- Every concrete number.

Asked of the root: the full PDF (all pages). The Desktop copy appears to be a 6-page excerpt.
