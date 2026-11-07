# Dark learning: the scheme decision for the two custody forks

2026-11-06. Written before building the d = 64 step, on ember's instruction: "are you sure those tasks are
actually meaningful? i don't want to be grinding on bad/legacy parts of our code that should just get
rewritten/redesigned/reconsidered now that we are smarter models." Ember also said of the custody fork,
"i think we should probably explore both." Reading order: `docs/DARK-LEARNING-PROGRAM.md` (constructions
C1–C23), `notes/dark-learning-foundations-critique.md` (F1–F15). Measured inputs from experiment 1:
`research/dark_learning_2026_11_06/` (run on hbox under `swarm-build`, counts only).

**The decision, in one line per fork.**
- **FHE fork:** exact BFV, rebuilt from scratch rather than on the legacy fhegg 3×36-bit engine. N = 8192.
  Q is three ~61-bit NTT-friendly primes, and **each prime is its own proof field**; cross-field
  consistency comes from PRISM-style canonical-integer witnesses. The plaintext modulus rises to a ~32-bit
  prime. Packing is coefficient encoding, so a rank-1 update is one polynomial product. Nonlinearity and
  requantization go through an MPC crossing (encrypt-to-shares, function, shares-to-encrypt), and
  decryption happens only on proof. Rejected for this fork: CKKS, TFHE-PBS nonlinearities, bootstrapping,
  and single big-prime GBFV.
- **MPC fork:** SPDZ-style dishonest-majority authenticated additive shares among n = 3 custodians, over
  one ~61-bit prime field. That field is shared with the FHE fork and with the proof system. The
  custodians compute the step themselves, and the host stores and transports only commitments and masked
  openings. Every output is opened only on proof. C21's one-time garbled encoding is an optional
  "host-evaluated" mode, priced below, and is not the default.

---

## 1. What experiment 1 measured (it decides several of the rejections)

**One ct×ct with its integer rescale certificate**, built on a real BFV product. Every relation is checked:
the column identities over ℤ, the field bounds that lift a field check to ℤ, and decryption to m₁·m₂. The
Q = 31, t = 4 falsifier is accepted by a mod-Q check and refused by the integer certificate, in every run.
Each count is for that concrete design: an upper bound for the design, not a lower bound for every
protocol.

| design | N | log Q | field | certificate elements | committed bits | bits / coefficient | v2 model predicted |
|---|---:|---:|---|---:|---:|---:|---:|
| A: native p61, digits w = 22 | 4096 | 61 | p61 | 593,899 | 36.2 M | 8,842 | 159,744 (×3.7 low) |
| B: PRISM-style, 6×34-bit + 8 ext primes | 8192 | 204 | per-prime 34-bit | 1,572,822 | 53.5 M | 6,528 | — |
| **B61: PRISM-style, 3×61-bit + 4 ext primes** | 8192 | 183 | per-prime 61-bit | **827,371** | **50.5 M** | **6,161** | — |
| C: row-interleaved into BabyBear, digits w = 5 | 8192 | 204 | BabyBear | 32,055,047 | 993.7 M | 121,302 | 1,056,768 (×30 low) |

[MEASURED, `rescale_certificates.py`; logs `exp1_{A,B,B61,C}.log` in the experiment directory.]

⚠ **Correction found while building the d = 64 verifier (same day).** The B/B61 counts above treat the
base-extension quotient u as a free witness of one element. It is not free: with u unpinned, a prover can
shift any extended value by a multiple of the basis product, and an output forged that way passes every
residue check (`cert_b61.py` exhibits it: shift one output coefficient by B, set u−1, and the residue checks
still pass; pinned, it is refused). The verifier must pin u to the canonical representative, which is a
range proof of the reconstructed value. Counted as 16-bit digits, that adds 1,081,344 digit elements to B61
(+17.3 Mbit, giving 67.8 Mbit and **8,277 bits/coef**) and 1,163,264 to B (+18.6 Mbit, giving 72.1 Mbit and
8,800 bits/coef). B61 stays the cheapest per coefficient, now only 6% below A's 8,842. Design A does not
have the problem: bounded digits define the integer uniquely. PRISM's single range proof via its
auxiliary prime is exactly this pin; it is not optional.

What this says:
1. **The model was low by ×3.7 for design A.** The rescale relation `t z + ⌊Q/2⌋ = Q y + s` costs more
   than the product itself: 270,336 of A's 593,899 elements. y, s and s's complement are each multi-digit,
   and so are the carries.
2. **Per-prime native fields win per coefficient, narrowly.** After the u-pin correction B61 commits
   8,277 bits per coefficient against A's 8,842, even though A has the "ideal" single prime. With
   PRISM-style binding, every per-prime polynomial identity is native. Only the canonical-integer
   witnesses (v, the pinned u) cross fields.
3. **Per prime, larger primes win.** B61 commits 827,371 elements against B's 1,572,822, in nearly the
   same bits, and with half the limbs and fewer cross-field witnesses.
4. **BabyBear-hosted row interleaving (C) is the expensive outlier.** At N = 8192 a 31-bit field forces
   5-bit digits, because N·2^{2w} must stay below the field. That makes 42 digits per coefficient and 83
   columns per product. See §1a for the measured count.

### 1a. Design C

[MEASURED, `exp1_C.log`] 32,055,047 committed elements, 993.7 Mbit, 33.4 M range lookups for one ct×ct.
Of these, 19.1 M are the CRT lift of the inputs and the per-prime output reduction; 5.4 M are the
rescale; the product columns account for the rest. That is ×30 the v2 model's prediction and ×15 B61 in
bits. **This candidate construction of the deployed layout (all residues bridged into one 31-bit field,
one monolithic digit-column budget) is far the most expensive at N = 8192.** Under that budget digits
wider than 5 bits overflow BabyBear. Chunked sums, extra carries or another arithmetization change the
budget, so this is a cost verdict on the candidate, not a lower bound or an impossibility for BabyBear
(Astra E10, accepted).

**The fused activation/derivative crossing**, executed at N = 8192, RNS-204, 3 parties, d = 4096 values in,
σ and σ' (8192 values) out. Encrypt-to-shares (E2S) and shares-to-encrypt (S2E) are real polynomials
checked by decryption; the function's openings run on shares. [MEASURED, `crossing_wire.py`, `exp1_X.log`]

| phase | wire elements |
|---|---:|
| E2S (n−1 polynomials of N×L residues to party 1) | 98,304 |
| function online (2 masked openings per value, each to n−1 parties) | 49,152 |
| S2E (n polynomials to the host) | 147,456 |
| **online total, one crossing** | **294,912** |
| preprocessing, rotated-table lookup (2^16 table, 2 columns) | 1,610,612,736 |
| preprocessing, 2-party DPF lookup | 1,703,936 |

The online cost is dominated by moving whole ciphertexts: 245,760 of 294,912 elements are E2S and S2E,
and that cost does not shrink with d. **A crossing costs N-sized messages whatever the layer width.** The
preprocessing of an exact 16-bit lookup in MPC is where the real cost hides: ~1.6×10^9 elements for a
rotated table. Function secret sharing (DPF) is 1,000× smaller but two-party.

---

## 2. FHE fork: is BFV-RNS the right scheme?

### Kept: exact BFV, re-based
- **Exactness is the asset.** In dark learning nobody runs floats, so the integer program IS the run, and
  the float objection to exact Freivalds (Peigné v3 §D.2.2) disappears (program §0). Only an exact scheme
  keeps that property.
- **N = 8192 is forced.** The smudging ledger fails at 10^6 steps at log Q = 109 (2^-14.2, F5), and the
  quantum-128 table caps log Q at 202 for N = 8192 (conditional: ternary-secret table, F6). Q = 3 primes of
  61 bits = 183 bits fits both constraints.
- **Each RNS prime is a proof field** (B61). This closes Hole A by canonical integers rather than by the
  2-felt bridge, and it is the cheapest certificate measured. It also replaces the "single prime" dream
  of FRONTIER-QUEUE G1: one prime cannot hold depth or the read budget; three proof-field primes can.
- **Plaintext modulus = the MPC field prime, ~2^61** (revised while building: better than the 2^32 first
  written). Encryption-to-shares then lands directly in F_t, the SPDZ field: the FHE plaintext space, the
  MPC field and one proof field are the same prime. This also removes the precision wall (F1) at any
  d we consider. Δ = Q/t ≈ 2^122, and a ct×ct costs about log t + log N + small ≈ 80 bits, so depth 1 per
  crossing with margin. That is all the d = 64 step uses: no relinearization, every product goes into a
  crossing.
- **Coefficient encoding, with the outer product as one polynomial product.** For d² ≤ N,
  δ(X^d)·x(X) puts δ_i x_j at coefficient d·i + j, which is exactly the row-major layout the forward
  matvec W(X)·rev(x)(X) reads. A rank-1 update is one ct×ct; the forward and backward matvecs are one each
  at d = 64.

### Rejected, with the reason

| candidate | why not |
|---|---|
| Legacy fhegg BFV (3×36-bit, N = 4096, t = 2^20) | Fails PQ, the read budget and the precision wall (F5, F6, F1). Its proof layout is the BabyBear bridge, the most expensive design measured. Its threshold and smudging code survives as a reference implementation, not as the engine. |
| CKKS for the training arithmetic | Approximate decryption makes every release a noise leak (the Li–Micciancio class), so every crossing needs flooding wide enough to cost precision. Worse for us: under CKKS the host's choice among valid evaluations (which Enc(0) to add, the 2026/2546 mask-selection move) steers the plaintext itself. That is Zamir's tolerance-as-channel with the host holding the steering wheel. Exact BFV removes the channel. |
| TFHE PBS for the nonlinearities | A PBS is a native lookup, which is attractive, but proving one is the dominant cost. 2026/1127 runs 2^23 constraints in ~1,469 s and OOMs at 2^22 on 768 GB; an activation per neuron means d PBS per layer. The MPC crossing proves its function on shares at plaintext size. Kept as a research option only. |
| Bootstrapping (any scheme) | It removes no welfare risk (Codex round 2: FHE custody cannot gate execution anyway), and it makes the host's unsanctioned fragments unbounded in depth. Its cost is ~15 levels per refresh. |
| Single big prime, GBFV at large modulus | The proof field would be ~180–200 bits (multi-word arithmetic everywhere), and the rescale certificate still needs integer limbs. B61 dominates it. |

### What the FHE fork cannot give, stated so nobody builds expecting it
P3 (no unsanctioned execution) is unobtainable: the host holds Enc(W) and evaluation keys (C13 refuted).
Confidentiality is tier C plus the read budget. The fork exists for host-local linear algebra at large d,
where the MPC fork's bandwidth explodes (×65 online traffic fully dark, tradeoff note §5).

## 3. MPC fork: C21 from first principles

**Which MPC.** SPDZ-style dishonest-majority, actively secure with abort: authenticated additive shares
with a global MAC key, over F_p with p a ~61-bit prime. The prime is chosen so p ≡ 1 mod 2^k for the proof
system and equal to one of the FHE fork's RNS primes, so both forks share field code, commitments and the
proof system.
- **Why dishonest-majority.** Confidentiality then fails only if ALL n custodians collude: the same tier
  C as n-of-n threshold FHE. Integrity against all n needs §9's collaborative proof; SPDZ's MAC alone
  gives integrity only while one custodian is honest. Both claims still owe the MAC failure term, the
  view definition, preprocessing privacy and a repeated/adaptive-audit argument (Astra, experiment-1
  audit); additive-share secrecy alone does not prove the opened view secret.
- **Preprocessing.** OT-based (MASCOT-class over lattice OT) to keep FHE out of the trust base, or
  LWE-HE-based (LowGear-class), which is where the FHE fork's BFV could supply triples. Both are PQ.
- **Rejected:**
  - Honest-majority 3PC: it tolerates one corruption of three (two honest parties remain a majority; the
    earlier wording "one corruption already breaks it" was arithmetically wrong, Astra). It is rejected
    because two colluding custodians break it, while dishonest-majority SPDZ needs all three, and because
    its speed is not the binding constraint at d = 64.
  - Garbled circuits as the default: ~150× the wire cost; see C21 mode below.

**Who the custodians are, and what the host sees.** Three custodians in independent trust domains
(organizations, jurisdictions, hardware vendors). The host can be one of them or none. The host stores and
moves only share commitments, masked openings (uniform field elements), MAC-check transcripts and sizes.
It never holds an evaluation object for the mind. ~~**That alone satisfies P3**~~ — narrowed after the
Astra statement audit (`notes/astra/dark-learning-statement-audit.md` DL20/DL27, accepted): it gives
**"no accepted new transition beyond authorized instances, and no host-held reusable evaluation object"**,
not a physical prohibition on computation — anything deducible from authorized outputs remains computable,
and copies of any classical message can be re-run. That narrower property, which no FHE configuration
does, without C21's garbling. Releases are openings of shared outputs, gated by a proof (C8's MPC
analogue). There is no CPA-D at all: an opening reveals exactly the authorized output, with no noise
channel.

**Numerics.**
- Integer training with exact semantics (factor-quantized 8-bit, F1), embedded in F_p with no wrap (proved
  bounds).
- Truncation is exact and deterministic (bit decomposition, ~log p triples per value), so the prescribed
  transition is a function of state and committed randomness only.
- Nonlinearity is a masked-index lookup against a preprocessed one-hot table: two output columns (σ, σ'
  keyed on the input code, F2), 2^8 entries at the d = 64 build.

**Per-step wire cost at d = 64** [DERIVED; the build replaces these with measured counts]:
- Two layers, batch 1, n = 3.
- Online: opening W−A for each layer (4,096), the activation and error vectors (~256), and the
  outer-product masks (128 per layer), broadcast to n−1 parties: about 5.2×10^4 elements per step. Lookups
  and truncations add about 1.5×10^3.
- Preprocessing: about 2.5×10^4 multiplicative relations per step.
- For comparison, the FHE fork at d = 64: ~4 crossings per step × 294,912/2 elements (N-sized messages at
  half the residues, three primes instead of six) ≈ 6×10^5 online elements.

**At d = 64 the MPC fork wins bandwidth ~10× and proofs by orders of magnitude.** The FHE crossing moves
N = 8192-sized messages to carry 64 values. The fork flips at large d (tradeoff note).

**C21, the host-evaluated mode** (optional, priced):
- The custodians jointly garble the step (BMR/authenticated-garbling class), and the host evaluates the
  one-time encoding.
- At d = 64 the step is ≈ 2×10^6 AND gates, so ≈ 64 MB per step plus the distributed-garbling cost,
  against ~0.4 MB of SPDZ online traffic.
- Worth it only when no custodian can do the compute. Not the default.

**How the audit theorem's three legs attach (MPC fork).**
- **ε_bind.** Each custodian commits per step to its share trace with a linearly homomorphic commitment
  over F_p, so Σ commit(share_i) = commit(W), plus SPDZ MAC soundness (2/p per batched check). A second
  MAC key or extension-field MACs bring that to ~2^-120.
- **ε_chk.** Two tiers:
  - Against a single deviating custodian, the online MAC check catches deviation on EVERY step: an
    envelope, not a sample.
  - For public verifiability, at the sampled step the beacon opens n−1 of the n committed views. This is
    MPC-in-the-head over the real MPC: it reveals nothing under n-out-of-n sharing, and the auditor
    re-executes and checks message consistency, catching a deviating party with probability ≥ (n−1)/n.
  - Against full collusion, consistent fake views pass, so integrity against all n needs a collaborative
    SNARK over the homomorphic commitment. That is the named next layer; full collusion is also the point
    where confidentiality is gone.
- **ε_beacon.** `joint_beacon.rs` among the custodians; last-revealer abort bias is the α term.
- **The envelope (C2's hactual/hhonest).** Norm caps on the factor shares, checked in MPC on every step at
  O(rd) triples.

**FHE fork legs, for symmetry.**
- ε_bind: per-prime commitments plus canonical-integer witnesses.
- ε_chk: soundness of the B61 certificate plus the crossing's share proof.
- ε_beacon: as above.
- The envelope must be proved on ciphertexts, which is why it dominates the FHE fork's cost below
  p ≈ 0.01 (tradeoff note §5).

## 4. What gets built next (the d = 64 step, both forks, one harness)

- One complete step per fork, two layers, d = 64, integer recipe identical in both.
  - FHE fork: B61 parameters, host ct×ct with certificates, a quorum crossing.
  - MPC fork: SPDZ shares with MACs, exact truncation, one-hot lookups, an MPC-in-the-head audit of
    sampled views.
- Same counts columns for both: committed elements and bits, online wire elements, preprocessing
  elements, crossings or openings, checker verdict.
- Attacked with Codex's list, each attack expected to be REFUSED by the checker: wrong δ, mixed source
  limbs, unrelated boundary shares, wrong quotient, stale parent, missing audit response.
- "Proved" here means: every certificate relation the verifier would check is computed and checked over
  the stated field with the stated bounds. Compiling the checker into a succinct argument is the next
  layer and is priced, not run.
- Reusable from our code, after this critique: the BFV reference (`bfv_ref.py`, new), the certificate
  builders (new), `AuditSampling.lean` + `AuditDisplacement.lean` (the audit statement), and the
  `joint_beacon.rs` design. Not reused: the fhegg 3-limb engine, its BabyBear bridge layout, the
  rank-1-at-the-host proof route (F13).


## 5. ✅ The d = 64 step, built both ways (2026-11-06, `research/dark_learning_2026_11_06/run_d64.py`)

**The setup.**
- One complete training step: two dense 64×64 layers, batch 1, exact integer recipe (`step_spec.py`).
- Each fork is built on the candidate this decision chose. Both forks reproduce the reference learner's
  new weights EXACTLY (integer equality), and both use one ~61-bit prime as the MPC field. In the FHE
  fork that prime is also the plaintext modulus.
- FHE fork: N = 8192, Q = 3×61-bit, 5 extension primes, 3 ct×ct per step, each gated by the B61
  certificate before any partial decryption; 3 custodian crossings. MPC fork: SPDZ, n = 3, whole step on
  shares.
- The FHE run on hbox exited normally, as `run_d64.py fhe` (its log is `d64_fhe.log`); the MPC fork ran
  on the Mac and on hbox.

| counts per step | FHE fork | MPC fork |
|---|---:|---:|
| committed elements (61-bit) | 3,718,968 | 328,704 |
| + certificate range digits (16-bit) | 7,077,888 | — |
| committed bits | 340.1 M | 20.1 M |
| online wire elements | 795,660 | 131,724 (107,148 without the genesis input of W) |
| preprocessing elements | 204,672 | 328,704 |
| openings | 5,632 | 17,792 |
| ct×ct / crossings | 3 / 3 | 0 / 0 |
| certificate per ct×ct | 933,864 elements + 2,359,296 range digits | — |

[MEASURED, `d64_results_fhe.json`, `d64_results_mpc.json`]

**Codex's attack list, run against both:**

| attack | FHE fork | MPC fork |
|---|---|---|
| wrong δ | REFUSED, decryption gate (input handle ≠ the custodians' committed δ) | REFUSED, online MAC check |
| mixed source limbs / sources | REFUSED, gate (opened residues ≠ committed handle) | REFUSED, online MAC check |
| unrelated boundary shares | **ACCEPTED online, output wrong**; the sampled conversion audit detects it in 2/3 beacon selections | REFUSED, online MAC check |
| wrong quotient | REFUSED, gate (pinned-u output base extension) | REFUSED, online MAC check |
| stale parent | REFUSED, gate (handle ≠ head) | REFUSED, chain check |
| missing audit response | REFUSED, fail-closed alarm | REFUSED, fail-closed alarm |

The MPC-in-the-head audit (n−1 of n views re-executed against the public transcript) catches a deviating
custodian in 2/3 of beacon selections. The online MAC check catches it on every step.

**What the build decided:**
1. **At d = 64 the MPC fork dominates**: ×17 fewer committed bits, ×6–7 less online wire. That is what §3
   predicted. Measured MPC online traffic is ~2× the derived 5.2×10^4, because exact truncation costs
   10 multiplications per value.
2. **The FHE fork's one open hole is the conversion relation.** A custodian who authenticates a share of
   the wrong source ciphertext produces a wrong step that every always-on check accepts; only the
   sampled audit sees it. Codex named this in round 1. The build makes it concrete and shows the fix is
   a per-crossing proof that E2S is well formed. Until that exists, the FHE fork's integrity for the
   conversion is sampled-only, at 2p/3.
3. **Two numerical bugs a paper analysis would have missed, both in BFV with a large t:**
   - textbook Δ·m encoding of a non-centered m;
   - Δ·M in shares-to-encryption, where shares sum to m + kt.

   Either leaves a noise of order (Q mod t) ≈ 2^61–2^62. The next ct×ct multiplies it by t·N·|s|, so
   decryption fails. The fixes are centered encoding and KPZ-exact round(Q·M/t) encoding in S2E. **Any
   design with t = the MPC prime needs both.**
4. **Not built yet:**
   - a succinct argument compiling these checkers;
   - real preprocessing (an ideal dealer stands in);
   - the E2S well-formedness proof;
   - the collaborative SNARK that the MPC fork needs against full collusion;
   - the d = 4096 point where the counts say the fork flips.


## 6. ✅ The FHE fork's conversion hole, closed by construction (2026-11-06, v2 of the d = 64 FHE step)

§5 left one wrong step that every always-on check accepted: a custodian authenticated its plain share
of the WRONG source ciphertext. The fix is not a proof bolted onto the old crossing. It removes the
private plain share altogether (`research/dark_learning_2026_11_06/e2s_proof.py`):

- **Encryption-to-shares is a masked public decryption.** Preprocessing hands out a pair
  (Enc(R), [R_k]) with R uniform mod t on all N coefficients. Anyone computes ct' = ct − Enc(R) from the
  handle-bound ct. Each custodian publishes a partial decryption p_i = s_i c1' + s2_i c2' + e_i with a
  proof of R_PD:
  - the per-prime identity p_i = s_i c1' + s2_i c2' + e_i − (X^N+1) k_q, at a Fiat–Shamir point;
  - s_i and s2_i opened against the custodian's long-term key commitment;
  - |e_i| ≤ E as 16-bit digits.

  The sum is decoded PUBLICLY to v = m − R, and [m_k] = [R_k] + v_k. With no private share there is
  nothing to substitute. A custodian can only deviate in its partial decryption, which R_PD refuses
  on every step.
- **Shares-to-encryption is a masked public encryption.** Preprocessing supplies (Enc_exact(R'), [R'_k]).
  The custodians open m − R' through SPDZ, and the MAC check covers that opening. Anyone then computes
  Enc_exact(R') + round(Q(m − R')/t). No new proof is needed. The exact scaling is mandatory here,
  because R' + (m − R') = m + kt (encoding fix F2, §8).

**Attacks, each refused by a check that runs on every step** (`d64_results_fhe.json`, run on hbox):

| attack | refused by |
|---|---|
| wrong δ, mixed limbs, stale parent | decryption gate (handle mismatch) |
| wrong quotient | decryption gate (pinned-u output base extension) |
| **unrelated boundary shares** (custodian 1 decrypts y's ciphertext into x's crossing) | **R_PD identity fails in F_q** |
| offset added to a partial decryption | R_PD identity fails |
| offset hidden in the smudging term | R_PD range: \|e\| > E |
| custodian shifts its share in the S2E opening | online MAC check |
| missing audit response | fail-closed alarm |

The step still reproduces `step_spec` exactly.

**Price of the fix (d = 64, per step; v1 → v2):**

| | v1 (sampled conversion) | v2 (R_PD on every crossing) |
|---|---:|---:|
| committed bits, including certificate digits | 340.1 M | 381.4 M |
| of which R_PD proofs (15 = 5 crossings × 3 custodians) | — | 38.2 M (1,351,635 elements, 983,040 digit lookups) |
| online wire elements | 795,660 | **671,628** |
| E2S wire / S2E wire | 245,760 / 294,912 | 368,640 / 49,920 |
| preprocessing elements | 204,672 | 696,960 (442,368 of them mask ciphertexts) |

Integrity of the conversion now costs +12% committed bits. Online wire went DOWN 16%, because a masked
public encryption opens only the values it carries (n(n−1) per value), while v1 sent N·L per party.
The cost moves into preprocessing: one mask ciphertext per crossing, whose well-formedness the
preprocessing must prove. That proof is unpriced, and the dealer is still ideal.

**Smudging, measured.** The public bound is E = 2^117 (the decryption margin shared by three smudges).
The designated ciphertexts carry noise of 2^78 after a ct×ct and 2^5 fresh. So each coefficient is
smudged at a ratio of 2^-39, and over the N = 8192 coefficients of one partial decryption the
statistical distance is about 2^-26. This is the F5 weakness in a measured form: the read leg is weak at
these parameters, and its repair is a larger Q or fewer published coefficients (decrypt only after
masking, which is already the case, plus extraction, which would need key switching).

What is still not built: the succinct compilation of R_PD and of the gate, a real preprocessing protocol
for the mask pairs, and the collaborative SNARK (MPC fork, §9).


## 7. ✅ d = 4096: the predicted flip, measured in counts (2026-11-06)

`research/dark_learning_2026_11_06/step_counts.py` replays the step's protocol schedule at any width and
charges each primitive its count. At d = 4096 one FHE matvec is 2,048 certified ct×ct and one MPC
matvec opens 16.7 M values, so the step cannot be executed in Python. The evidence that the schedule
IS the protocol:
- `--validate` reproduces every count column of the executed runs exactly: MPC at d = 16, 32 and 64,
  and FHE v2 at d = 64, including wire per phase.
- `--layout-check` (hbox, under `swarm-build`) executes, at N = 8192 on real ciphertexts, one block of
  each kind the d = 4096 layout uses (128 rows × 64 columns per ciphertext). The forward, backward
  (colrev) and outer-product blocks all decrypt to the right values.

**Recipe at width d.** step_spec's learner, with shifts widened so every truncation stays in budget:
S1 = ceil(log2(49d/128)), so S1 = 11 at d = 4096.

**Steady state, per step** (the weights are already in custody; FHE bits include certificate digits):

| d | fork | committed bits | online wire | preprocessing elems | ct×ct |
|---:|---|---:|---:|---:|---:|
| 64 | MPC | 1.71×10^7 | 107,148 | 2.80×10^5 | 0 |
| 64 | FHE (a) | 3.75×10^8 | 671,628 | 6.97×10^5 | 3 |
| 1024 | MPC | 2.10×10^9 | 1.97×10^7 | 3.45×10^7 | 0 |
| 1024 | FHE (a) | 4.18×10^10 | 1.94×10^7 | 4.44×10^7 | 384 |
| 1024 | FHE (b) | 7.97×10^10 | 6.79×10^6 | 8.96×10^6 | 640 |
| 4096 | MPC | 3.15×10^10 | 3.06×10^8 | 5.16×10^8 | 0 |
| 4096 | FHE (a) | 6.61×10^11 | 2.29×10^8 | 6.31×10^8 | 6,144 |
| 4096 | FHE (b) | 1.26×10^12 | 2.75×10^7 | 3.67×10^7 | 10,240 |

The variants:
- **(a)** is the built design: SPDZ outer product, then masked S2E of the d² update.
- **(b)** replaces that with a homomorphic outer product, which the layout check confirms, plus
  relinearization. Relinearization is **priced by MODEL** as one key-switch certificate ≈ one ct×ct
  certificate; it is not built. Variant (b) also needs an evaluation (relinearization) key, which §3's
  custody argument treats as a reusable evaluation object.

**Verdict:**
1. **The wire flip is CONFIRMED.**
   - FHE/MPC online wire: ×6.3 at d = 64 → ×1.85 at d = 256 → ×0.98 at d = 1024 → ×0.75 at d = 4096
     for (a); ×0.09 at d = 4096 for (b).
   - MPC wire is 99% matvec openings of W − A (3(d² + d) n(n−1)). The FHE fork carries the weights
     inside ciphertexts and opens only vectors, plus the d² update in (a).
   - The crossover is at d ≈ 1024 for (a), and between 256 and 1024 for (b).
2. **There is NO flip in committed bits.** FHE stays ×17 to ×40 above MPC at every width. At d = 4096,
   (a) commits 661 Gbit per step, 88% of it ct×ct certificates (6,144 × 94.7 Mbit), against MPC's 31.5
   Gbit of views. The certificate is the FHE fork's bill at every scale. Halving it means halving the
   per-product certificate (§1's design space), not changing the layout.
3. **Preprocessing.** MPC (5.2×10^8 elements) and FHE (a) (6.3×10^8) are comparable. FHE (b) is ×14
   lower.

**What this does to the fork.**
- Below d ≈ 1000, MPC dominates on every column.
- Above it, the choice is wire versus proof size:
  - FHE (a) trades ×21 committed bits for ×0.75 wire;
  - FHE (b) trades ×40 committed bits for ×0.09 wire, and needs a relinearization key.
- Neither fork dominates at d = 4096, which is what "explore both" requires.

**An MPC-side idea the counts point to (DERIVED, not built): a drifting matrix mask. ⚑ §10 judges
it: the drift is vacuous, the persistent-mask core is sound but only shifts cost offline, and the
priced replacement is an HE-assisted matvec (×2.7).** The MPC
matvec opens W − A afresh every time because a reused mask would reveal the update. Alternative:
1. Keep P = W − A public and move it by a PUBLIC random rank-1 u⊗w each step, so P' = P − u⊗w. The
   mask then drifts as A' = A − dW + u⊗w, so it stays secret.
2. Compute [A_t b] for a fresh b from the dealer's [A_0 b] plus the t logged rank-1 terms (O(t d) online).
3. Re-mask with a fresh d² opening every T steps.

The amortized cost per matvec is about d²/T + T·d. At T ≈ √d that is O(d^1.5): about 5×10^5 rather than
1.7×10^7 openings at d = 4096, which would undo FHE (a)'s wire advantage. It needs its own privacy
argument (P's trajectory is public) before it is priced.


## 9. ✅ The MPC fork's hole: a collaborative proof, prototyped (2026-11-06)

**The hole.** The MPC fork's integrity comes from two things, and full collusion defeats both:
- SPDZ's MAC check holds only if at least one custodian is honest.
- The MPC-in-the-head audit is fooled by consistent fake views.

A collaborative SNARK fixes this. The custodians run a SNARK prover inside the MPC, and the verifier
sees only commitments, prover messages and openings. Soundness is the SNARK's, so it holds against all
provers together. Privacy against fewer than n custodians is the MPC's.

**Survey (2022–2026).** Abstracts were read via ePrint/arXiv pages; tags as shown.

| work | proof system / PCS | sharing, threshold | fit for us |
|---|---|---|---|
| Ozdemir–Boneh, USENIX Sec 2022 [READ abstract] | Groth16, Marlin, Plonk (pairings) | SPDZ / GSZ; malicious minority at about single-prover runtime | the template (SPDZ, dishonest majority, public verifiability); its pairing PCS does not exist over our 61-bit prime |
| zkSaaS, Garg et al. USENIX Sec 2023 [CLAIM, via the next two abstracts] | Plonk-style | packed secret sharing, one powerful server | the packed threshold needs many servers and an honest fraction; not n = 3 |
| Liu et al., ePrint 2024/143 (USENIX Sec 2025) [READ abstract] | Libra (GKR) and collaborative HyperPlonk (2024/940) | fully distributed, "adaptable" to malicious | sumcheck-based, a good fit; its sharing/threshold were not on the abstract page |
| Fang, Garg, Roberts, Wu, Zhang, ePrint 2025/1388 [READ abstract] | Plonkish, bivariate PCS on packed shares, 960 B proofs | packed, fewer than n/4 corrupt | the threshold rules it out for 3 custodians |
| Alghazwi et al., arXiv 2407.19212 [READ abstract] | commit-and-prove (LegoSNARK), Groth16 / Bulletproofs | not stated on the page | its commit-and-prove composition is the right shape for chaining |
| Brüggemann–Nof–Schneider, ePrint 2026/1741 [READ abstract] | distributed ZK over Z_2^k, dealer | dishonest majority, active | verification among the parties only: no public proof, no full-collusion integrity |
| Khoshakhlagh–Kallesøe–Dalskov, ePrint 2026/2721 [READ abstract] | sumcheck + compressed Σ; private-opening PCS for committee handover; IVC by an external prover | long-running MPC with committee rotation | **directly relevant to C22 (epoch custody) and to chaining**; read in full next |

**Choice.** Three constraints decide it:
- **The field.** It is the shared 61-bit prime, so there are no pairings and the PCS is hash-based.
- **The threshold.** Three custodians with dishonest-majority privacy rules out packed sharing.
- **Integrity against all n.** This needs a publicly verifiable proof, not a distributed ZK check.

The result is Ozdemir–Boneh's SPDZ route with a sumcheck IOP (Libra/HyperPlonk style) and a
Ligero/Brakedown-style PCS. One adaptation keeps hashing out of the MPC. Each custodian RS-encodes its
OWN share matrix and Merkle-commits its own columns. Encoding is linear, so the commitment (the n-tuple
of roots) binds the sum matrix, and every PCS test runs on the sum: parties send their share row
combinations, and the verifier adds them and checks each party's opened columns against the codeword of
the summed combination. Binding, proximity and evaluation soundness are the single-prover scheme's,
applied to the sum. [INFERRED; whether this per-party share commitment appears in the collaborative-SNARK
literature was NOT searched: no novelty claim.]

**Statements proved, per step:**
- three matvecs, by sumcheck (log d rounds, degree 2), each ending in ONE evaluation of W's MLE;
- the rank-1 updates, by the zero-round check W'(r) = W(r) − d(r_row)·v(r_col) (program construction (a),
  here used where it was meant to be, inside the custody: F13's witness-custody objection does not apply,
  because the custodians hold the factors);
- Hadamard gates, by a degree-3 zerocheck.

The products inside the prover are SPDZ Beaver multiplications, so the prover messages are MAC-checked
openings. The parent commitment of step t+1 is the W' commitment of step t.

**Prototype: built and run** (`research/dark_learning_2026_11_06/cosnark.py`, `run_cosnark.py`,
`cosnark_results.json`).
- **Scope.** The linear-algebra spine of the step: z1 = W1x, z2 = W2h, b = W2ᵀd2, bg = b∘g1, both rank-1
  updates, and parent/child chaining. It is one Fiat–Shamir proof, and the verifier sees roots, messages
  and openings only.
- **Every attack is a full collusion: all three custodians agree.**

| attack (d = 64) | verdict |
|---|---|
| honest | ACCEPT |
| commit a wrong W1' (one entry +1) | REFUSED: rank-1 check |
| commit a wrong z1, prove honestly | REFUSED: sumcheck round sum |
| wrong z1, forge every sumcheck round to match | REFUSED: final check against the committed W, x |
| wrong W1' committed, custodian 0 reports its HONEST share's row combination | REFUSED: evaluation consistency at an opened column |
| two-step chain, step 2's parent = step 1's child | ACCEPT |
| step 2 verified against an older W | REFUSED: parent ≠ previous child |

- **Counts.** The count formula equals the executed counts exactly at d = 16, 32 and 64 (every column).

| per step | d = 64 (executed) | d = 4096 (formula) |
|---|---:|---:|
| committed witness elements (spine) | 16,960 | 6.71×10^7 (4.1 Gbit) |
| codeword elements per custodian (rate 1/4, local) | 67,840 | 2.69×10^8 |
| proof field elements, t = 64 / t = 148 columns | 65,733 / — | 3.40×10^6 / 7.67×10^6 |
| proof hashes (t = 64 / 148) | 14,823 / — | 24,615 / 56,871 |
| custodians' proving openings | 1,716 | 106,626 |
| custodians' proving wire | 10,308 | 639,768 |
| elementwise gates, MODEL (not built): committed / Hadamard constraints / proving wire | 20,544 / 19,968 / 958,824 | 1.54×10^6 / 1.50×10^6 / 7.20×10^7 |

**What the counts say:**
1. **The full-collusion proof costs less than the audit it replaces.** At d = 4096 its witness is 4.1
   Gbit, plus about 0.1 Gbit for the elementwise gates. The MPC-in-the-head audit commits 31.5 Gbit of
   views (§7), because a proof of the step commits W, the vectors and the gate wires, while the views
   commit every preprocessed mask. The FHE fork's certificates are 661 Gbit.
2. **The proving wire is dominated by the elementwise gates, not the spine.** 7.2×10^7 against 6.4×10^5:
   - the lookup is re-proved through its 255 committed powers;
   - each truncation through its own SPDZ circuit;
   - a degree-3 zerocheck needs four products per pair per round in MPC.

   That is +24% on the MPC step's 3.06×10^8 online wire. Halving it is easy: the X = 0, 1 points of each
   round are products the parties already hold. Replacing the power chain by a LogUp argument with
   committed multiplicities is the bigger lever and is not priced.
3. **With proofs, the audit theorem attaches with p chosen freely.** The custodians commit their
   share-codeword roots EVERY step (local hashing, no wire) and prove on beacon-sampled steps. That is
   exactly the commit-then-audit shape of `AuditSampling.lean`, with
   - ε_chk = this proof's soundness (sumcheck 2·deg·log d / |F_ext|, proximity (1−δ)^t, Fiat–Shamir);
   - ε_bind = the hash.

   C2's `displacement_bound` then holds against full collusion, with the envelope proved on every step:
   the norm caps on the factors are a range check on committed vectors, so it is cheap here.

**Not built (named, and why each is not an obstruction):**
- **Zero knowledge.** The opened row combinations a^T V leak linear functionals of W to the VERIFIER.
  Mask rows and a masked sumcheck are standard and cost O(√size) extra elements. Without them the proof
  must not be published beyond the custodians.
- **The elementwise gates.** These are the same zerocheck machinery, priced above.
- **Challenges are drawn in F_p here.** A deployment needs F_{p^2}/F_{p^3} challenges: extension
  arithmetic in the MPC at about 3 base multiplications per product.
- **The proximity parameters.** t = 64 at rate 1/4 gives about 2^-43 at unique decoding, and t ≈ 148
  gives 100 bits (both priced). The Ligero-style proof is O(√N) (7.7×10^6 elements ≈ 59 MB at d = 4096);
  recursion or a FRI/WHIR-style PCS shrinks it.
- **The binding commitment is not hiding,** and step-to-step equality of roots requires the custodians
  to carry their shares unchanged. Re-sharing between steps needs a proof that the new share commitments
  sum to the same matrix: one random linear-combination check on the sums. That is the handover problem
  ePrint 2026/2721 addresses.


## 8. The FHE crossing's two idealizations, priced (2026-11-06; MODEL, `step_counts.py: mask_nonideal`)

§6's table left two things ideal: the mask pairs (Enc(R), [R_k]) came from an ideal dealer, and their
well-formedness was not proved. The non-ideal replacement, per pair, per custodian i:

1. **Post** Enc_pk(R_i) under the joint public key, 2NL elements. The scaling is exact:
   round(QR_i/t) = ΔR_i + c_i with c_i = round(rR_i/t) and r = Q mod t, so the F2 fix holds for the sum.
2. **Prove it well formed (ZKPoPK):**
   - per prime, the two component identities with native quotients, 2L(N−1) elements;
   - 16-bit digits for R_i (4), c_i (4), the remainder of c_i (4), u (1), e0 (1) and e1 (1), so 15N digits;
   - the integer relation t·c_i = r·R_i + rem, checked modulo two auxiliary primes.
3. **SPDZ-input R_i[k]** for the coefficients the crossing uses, so that [R_k] = Σ_i [R_i[k]].
4. **Link** those inputs to the committed R_i with one batched check, using a sacrificed random input:
   O(1). Without this link the conversion hole reopens in preprocessing: a custodian could encrypt one
   mask and input another.

**What it adds, per step:**

| d | variant | mask pairs | committed bits (16-bit digits) | offline wire |
|---:|---|---:|---:|---:|
| 64 | (a) | 9 | +1.34×10^8 (+36% on 3.75×10^8) | 1.41×10^6 (×2.1 the online wire) |
| 4096 | (a) | 4,385 | +6.53×10^10 (+10%) | 9.49×10^8 (×4.1 the online wire) |
| 4096 | (b) | 481 | +7.16×10^9 (+0.6%) | 7.13×10^7 (×2.6 the online wire) |

**The digit convention (Astra's E8, accepted).** Counting a committed 16-bit digit at 16 bits assumes
a packing mechanism nobody has defined. If each digit is its own committed field element (61 bits), the
FHE fork's committed bits per step become:

| d | variant | committed bits (61-bit digits, non-ideal masks included) | ratio to MPC (views) |
|---:|---|---:|---:|
| 64 | (a) | 1.02×10^9 | ×60 |
| 4096 | (a) | 1.45×10^12 | ×46 |
| 4096 | (b) | 2.37×10^12 | ×75 |

The MPC fork commits only field elements, so its numbers do not move. **Both conventions are now
printed by `step_counts.py`.** The 61-bit one is the headline until a digit-packing PCS is specified
and priced.

**What this does to §7's verdict.**
- The wire flip survives for (b): 27.5 M online plus 71 M offline against MPC's 306 M.
- **It does NOT survive for (a) once the masks are real:** 229 M online plus 949 M offline. The d²
  update crosses as 2,048 mask ciphertexts per layer, each posted by three custodians.
- So if FHE custody is chosen at large d, the update must stay homomorphic (variant (b): relinearization
  and its key, with the custody cost §3 names), or the update must be low-rank so it crosses as vectors.

**One idealization remains in BOTH forks:** SPDZ's own preprocessing (triples, truncation masks, power
tuples) still comes from an ideal dealer, in the MPC fork and inside the FHE fork's crossings. It is the
same object in both, so the fork comparison is fair about it. Its price (an Overdrive/LowGear-style
protocol) is not yet in any table here.


## 10. The "drifting mask" (§7), argued: dead as stated; its core is sound and shifts cost; the replacement is priced

**What §7 claimed.** The MPC matvec opens W − A afresh (d² openings) because reusing the mask reveals
the update. §7 proposed keeping P = W − A public and moving it by a public random rank-1 term each step,
P' = P − u⊗w, so that the mask drifts as A' = A − dW + u⊗w and stays secret.

**1. The drift is vacuous.** P_t = P_0 − Σ_s u_s⊗w_s is a function of P_0 and public coins, so it
carries no information beyond P_0. Setting every u⊗w to 0 changes nothing: A_t = W_t − P_t is then just
W_t minus a public matrix. Privacy is fine, because P_0 = W_0 − A_0 is opened once under a uniform
one-time A_0. But the drift does no work, and "P's public trajectory" was never the privacy question.
**The idea as stated is dead.**

**2. The working core is a persistent mask with incremental corrections. It is SOUND.** Let
preprocessing give a fresh pair (b, [A_0 b]) per matvec, with A_0 persistent between re-masks. Then

    [W_t b] = [A_0 b] + P_0·[b] − Σ_{s<t} [d_s]·⟨[x_s], [b]⟩,
    [W_t v] = [W_t]·(v − b) + [W_t b]          ([W_t] times a public vector is local).

The openings are:
- P_0, once per re-mask, uniform;
- v − b, with a fresh uniform b;
- Beaver openings, with fresh triples.

[A_0 b] is never opened, so the standard SPDZ simulation applies. The one rule: A_0 is never an opening
mask twice. Each re-mask draws a fresh A_0 and opens W − A_0 once. Integrity comes from the MACs on the
preprocessed [A_0 b]. The transposed matvec uses (b, [b^T A_0]) the same way.

**3. But it only SHIFTS cost.**
- **Online:** per matvec, d plus 4d per update since the last re-mask, plus d² per re-mask. At T ≈ √(d/2)
  the amortized cost is 7.5×10^5 openings at d = 4096, against 1.68×10^7: ×22 online.
- **Offline:** each [A_0 b] is a product of a persistent SECRET matrix with a fresh secret vector. With
  the ideal dealer this is free, and that is the illusion. With a real dealer it costs one of:
  - **(i) a SPDZ matvec offline.** That is d² openings again: no total saving.
  - **(ii) an HE-assisted product.** Custodian i multiplies its plaintext share of A_0 by custodian j's
    encrypted share of b: pt×ct only, j's own key, no evaluation key anywhere near the host. That costs
    exactly what doing the ONLINE matvec HE-assisted would, so persistence buys nothing over (ii)
    applied directly.
  - **(iii) a pseudorandom-correlation generator** for (fixed secret matrix share) × (fresh vector)
    correlations. This would make the core pay: O(d^1.5) online, sublinear offline. Whether such a PCG
    exists for a CHOSEN fixed matrix, rather than the pseudorandom fixed side standard VOLE PCGs give,
    is open here. [INFERRED; not searched.]

**4. The priced replacement: an HE-assisted matvec in the MPC fork.** Per ordered custodian pair
(i, j):
- j sends Enc_j(v^(j)) in the 128 × 64 block layout: d/64 ciphertexts.
- i returns the masked, noise-flooded Σ_blocks W^(i)·Enc_j(v^(j)): d/128 ciphertexts.
- i returns the same for its MAC share αW^(i), so the SPDZ MAC check still covers the result.

Per matvec at d = 4096 that is 6 × (64 + 2·32) × 2NL = **3.77×10^7 elements, against 1.01×10^8:
×2.7**. Plus a ZKPoPK per sent ciphertext (unpriced). The MPC fork's steady online wire drops from
3.06×10^8 to about **1.17×10^8**. That is below FHE (a), even before (a)'s 9.5×10^8 offline mask wire
(§8), and about the same as FHE (b)'s 2.75×10^7 online + 7.1×10^7 offline.

This hybrid keeps the MPC fork's custody property: the HE keys are each custodian's own, and there is no
evaluation object for the mind. It is a hybrid in mechanism, not in custody. [DERIVED; not built.]

**Net effect on the fork at d = 4096.** With real masks and an HE-assisted matvec:
- the MPC fork is within ×1.2 of FHE (b) on wire;
- it is ×40 to ×75 smaller on committed bits;
- it keeps integrity against full collusion through §9's proof.

So the MPC fork now dominates FHE (a) everywhere, and trades evenly with FHE (b) on wire while winning
on proof size and custody. That is a model result. The next measurement that could overturn it is the
HE-assisted matvec built and counted in the harness.


## 11. ✅ The HE-assisted matvec, built and counted (2026-11-06; `he_matvec.py`, `run_he_matvec.py`)

§10's priced replacement for SPDZ's d² matvec, now executed.

**How it works.** Each custodian has its OWN BFV key (N = 8192, Q = 3 × 61-bit, t = the SPDZ prime p).
For each ordered pair (i, j):
1. j sends Enc_j(v^(j)) in the block layout, with exact scaling.
2. i returns Σ_blocks W^(i)·Enc_j(v_block), plaintext × ciphertext only, with three additions:
   - a uniform mask M on all N coefficients;
   - a fresh Enc_pk_j(0), without which j could divide out W^(i) from W^(i)·a_j;
   - flooding noise.
3. j decrypts its masked cross term; i keeps −M.

The plain shares of z are then authenticated, and ONE SPDZ Freivalds check, with ρ drawn after the
shares are fixed, opens ρ^T[z] − ⟨ρ^T[W], [v]⟩ and requires 0. That costs d Beaver products and is
MAC-checked.

Exact scaling of j's vector is mandatory here too. The plaintext multiplier W^(i) has full-size
coefficients (about 2^60), so textbook Δ·v's rounding error would be multiplied past the margin: the F2
phenomenon in a third place.

**Results** (hbox, `swarm-build`; `he_matvec_results_{64,128,attacks}.json`):

| run | verdict | step online wire | of which HE ciphertexts | SPDZ-matvec step wire |
|---|---|---:|---:|---:|
| d = 64 | ACCEPT, refines `step_spec` exactly | 1,829,790 | 1,769,472 | 131,724 |
| d = 128 (two column blocks; exercises block sums) | ACCEPT, refines exactly | 2,823,966 | 2,654,208 | 469,260 |
| j encrypts a vector other than its share | **REFUSED** (Freivalds) | | | |
| i returns a wrong cross term | **REFUSED** (Freivalds) | | | |
| a custodian shifts its share at authentication | **REFUSED** (Freivalds) | | | |

**The count formula matches the executed runs exactly at d = 64 and d = 128:** online wire,
preprocessing values, and ciphertexts sent and returned. The formula for the rest of the step is
`step_counts.mpc_counts` with the executed shifts.

**At width, steady state per step** (formula validated above):

| d | SPDZ matvec: online wire | HE matvec: online wire | ratio | HE matvec: preprocessing values | ZKPoPKs (bits) |
|---:|---:|---:|---:|---:|---:|
| 64 | 107,148 | 1,805,214 | ×0.06 | 34,688 | 18 (1.2×10^8) |
| 1024 | 1.97×10^7 | 2.21×10^7 | ×0.89 | 2.61×10^6 | 240 (1.6×10^9) |
| 4096 | 3.06×10^8 | **8.90×10^7** | **×3.44** | 3.58×10^7 | 960 (6.2×10^9) |

**What it decides:**
1. **Below d ≈ 1200 the SPDZ matvec is cheaper.** A ciphertext is N·L·2 = 49,152 elements whatever
   it carries. Above that width the HE matvec wins, ×3.4 at d = 4096. That is better than §10's ×2.7,
   because the Freivalds check replaces the MAC-share products.
2. **Preprocessing collapses.** The matrix triples were most of the MPC fork's preprocessing. Steady
   preprocessing at d = 4096 falls from 8.6×10^7 to 3.6×10^7 authenticated values. The MPC-in-the-head
   views shrink from 31.5 to 13.1 Gbit. With §9's proof they are no longer the integrity mechanism
   anyway.
3. **The fork at d = 4096, all counts per step, SPDZ preprocessing still ideal in both forks:**

| fork | wire | committed bits |
|---|---|---|
| MPC with HE matvec | 8.9×10^7 online | 13.1 Gbit views + 4.2 Gbit collaborative proof (spine) + 6.2 Gbit ZKPoPK |
| FHE (b) | 2.75×10^7 online + 7.1×10^7 offline masks | ≥ 1.26 Tbit (16-bit digits) or 2.37 Tbit (61-bit) |
| FHE (a) | 2.29×10^8 online + 9.5×10^8 offline | ≥ 0.66 Tbit |

   ⚠ **WITHDRAWN (Astra scholar, `notes/dark-learning-scholar-response.md`).** The next sentence compared
   online wire with SPDZ preprocessing left ideal, and committed bits across heterogeneous units. With
   MASCOT preprocessing priced, HE-MPC is 14.06 Tbit/step against FHE (b)'s 0.914. Replacing the outer
   tuples by an HE-assisted outer product brings it to about 0.99 Tbit (§14). Original text, kept for
   the record: **The MPC fork now matches FHE (b) on total wire and is about ×50–100 smaller on
   committed bits.** It
   also holds integrity against full collusion (§9) and keeps every key, including the HE keys, inside
   custody. This is now a measured-at-small-d, formula-at-width result. What could still overturn it:
   the unpriced SPDZ preprocessing, which is the same object in both forks, and the elementwise gates'
   proving wire (+7.2×10^7, MODEL), which only the MPC fork pays for full-collusion integrity.

**Not built:**
- the ZKPoPK on each sent ciphertext (a privacy leg for i's share; priced);
- circuit privacy. ⚠ The scholar REFUTED whole-ciphertext hiding: flooding the first component
  leaves the second distinguishing multipliers information-theoretically. Even the decrypted phase
  reaches only about 2^-14.74 per step at d = 4096, against a 2^-40 target. N = 16384, four 61-bit
  primes and a 2^165 flood give a phase-only million-step bound below 2^-40; whole-ciphertext privacy
  needs a computational simulation and a well-formed key;
- the ZKPoPK, priced between 6.2 Gbit/step (an efficient lattice proof, MODEL) and **225.7 Tbit/step**
  (the executable Stern fallback, scholar);
- the MPC-in-the-head audit's replay of the HE path, which the collaborative proof supersedes.


## 12. ✅ The elementwise gates of the collaborative proof, built and counted (2026-11-06; `cosnark_gates.py`)

**The idea.** In SPDZ every shared value is a public-linear form in the preprocessed values ("atoms")
and the public openings. So "the custodians executed the program" for the nonlinear middle (both
truncations of z, the table lookup, e = trunc(z2) − y, d2, bg = b·g1, d1) is exactly three things:
- **(O)** each opening equals its form evaluated on the atoms. These are linear constraints with public
  values.
- **(P) The preprocessing is well formed:**
  - Beaver triples satisfy ta·tb = tc;
  - truncation mask bits are boolean;
  - tr = Σ 2^i trb_i + 2^s trh;
  - **trh ∈ [0, 2^(K+κ−s)) via its bits.** Without this, rhi is a free field element: u = (c≫s) − rhi −
    borrow stops being floor(z/2^s), and colluders steer the lookup input. The bits are proof-only
    preprocessing (dealer-provided), so the MPC's execution counts do not change.
  - lookup powers satisfy pw_j = pw_1·pw_{j−1}.
- **(X)** the middle's inputs (z1, z2, b, y) and outputs (h, g1, d2, bg, d1) are the spine's
  committed vectors.

**The verifier derives this constraint system ITSELF.** It replays `run_step` symbolically against the
public transcript: openings read the transcript, each preprocessing call makes a fresh atom. No form
comes from the prover; a prover/verifier mismatch is refused.

**The proof.**
- Commit P (the atoms plus proof-only bits) and the operand vectors A, B, C, with the per-party
  share-codeword PCS.
- Zerocheck A∘B − C = 0, using Beaver products in the MPC.
- Batch every linear, copy and IO constraint with random γ into Σ_X ⟨q_X, X⟩ = const. Each ⟨q_X, X⟩ is a
  sumcheck against a PUBLIC table, so its round polynomials are local on shares, with no MPC
  multiplication.
- The semantics proved are the SPDZ program's. They equal `step_spec` whenever the spec's input bounds
  hold, and those bounds are C2's envelope, not this proof's.

**Results** (hbox, `cosnark_gates_results.json`; spine and middle proved together):

| run | spine | middle |
|---|---|---|
| honest d = 16, d = 64 | ACCEPT | ACCEPT |
| forged truncation opening (full collusion, MACs forged) | **ACCEPT** | **REFUSED**: linear batch |
| forged lookup opening | **ACCEPT** | **REFUSED**: linear batch |
| malformed Beaver triple (colluding dealer) | **ACCEPT** | **REFUSED**: zerocheck |
| non-boolean truncation mask bit | **ACCEPT** | **REFUSED**: zerocheck |
| truncation mask out of range | **ACCEPT** | **REFUSED**: linear batch (mask relation) |

The spine accepts every one of these. That is why the middle exists: each attack keeps the linear
algebra consistent and corrupts only the nonlinear gates.

**Counts.** The formula is exact against execution at d = 4, 16 and 64 on every column.

| per step | d = 64 (executed) | d = 4096 (formula, widened shifts) | §9's MODEL at d = 4096 |
|---|---:|---:|---:|
| atoms (incl. proof-only bits) | 37,184 (11,840) | 2.90×10^6 (7.58×10^5) | — |
| Hadamard constraints | 31,872 | 2.26×10^6 | 1.50×10^6 |
| linear constraints | 5,888 | 6.72×10^5 | — |
| committed elements (P, A, B, C, padded) | 163,840 | 1.68×10^7 | 1.54×10^6 |
| custodians' proving wire | 1,575,336 | **2.01×10^8** | 7.20×10^7 |

**§9's MODEL was low by ×2.8 on proving wire and ×11 on committed elements.** It left out three
things: the trh range bits (κ = 40 statistical-masking bits dominate each truncation), padding to a power
of two, and the four products per pair per round of the degree-3 zerocheck. At d = 4096 the executed
design's proving wire is ×2.3 the step's online wire with the HE matvec (8.9×10^7). **That makes the
collaborative proof, not the step, the MPC fork's dominant online cost.**

**Three levers (MODEL, not built: `counts_optimized_MODEL`):**
1. The lookup by LogUp instead of a 254-product power chain.
2. rhi's range by three 16-bit LogUp chunks instead of ~48 boolean bits.
3. A zerocheck that reuses the products already held at X = 0, 1 and skips padding.

Together: 5,440 Hadamards and 1.31×10^5 proving wire at d = 64, and **1.37×10^7 at d = 4096**: ×15 less,
and 15% of the step's online wire. LogUp in the MPC needs shared inverses (one masked opening each) and
committed multiplicities, which the parties compute from public table indices only for the range
chunks. For the activation lookup the multiplicities are secret and need their own argument.

**Where this leaves the MPC fork's full-collusion integrity.**
- The whole step is proved: spine plus middle. Every gate is checked, and the verifier derives the
  constraint system itself.
- The price, as built, is ×2.3 the step's online wire, with a modelled path to ×0.15.
- **Zero knowledge is still missing** (next item). The opened claims ⟨q_X, X⟩, the row combinations
  and the sumcheck messages leak linear functionals of the atoms and the spine vectors. Until it is
  built, the proof stays among the custodians.


## 13. Zero knowledge for the collaborative proof: three layers. Layer 1 is built, layers 2–3 are designed and counted (2026-11-06)

**What leaks today** (§9, §12). The verifier sees, in addition to the Merkle roots:
- **(i)** opened codeword columns. Each is t evaluations of every row's polynomial, so linear functionals
  of W and of the atoms.
- **(ii)** the row combinations a^T V and γ^T V.
- **(iii)** every sumcheck round polynomial, every evaluation value and the linear-batch claims ⟨q_X, X⟩.

Until all three are hidden, the proof must not leave the custodians.

**Layer 1: the hiding PCS (BUILT; `cosnark.HIDE`, `NMASK`, `LIVES`).**
- **Columns.** Every row is encoded with HIDE extra random coefficients. For t opened columns at
  distinct nonzero points, the map from the tail to the opened values is a Vandermonde-type matrix of
  full rank, so the columns are uniform whatever the data.
- **Row combinations.** Each evaluation adds its own fresh mask row with weight 1, so the revealed
  combination is uniform. The custodians send m_e = ⟨M_e, b⟩ so the value can still be computed.
  - The proximity combination puts weight 1 on a dedicated mask row and random weights on every other
    row, so mask rows are proximity-tested too.
  - **Each mask row serves exactly one combination** (asserted in code). A mask reused across two
    combinations would reveal their difference, a linear functional of the data.
- **Every custodian draws its own tail and mask shares locally,** with no communication.
- **Chaining forces a design point.** A weight commitment lives twice: as step t's child and as step
  t+1's parent. Its columns are opened in two proofs, so up to 2t columns are revealed. Hence
  HIDE ≥ LIVES·t = 2t. Its mask rows are split into two blocks, one per life. The custodians carry the
  commitment's opening (shares, tails, masks) into the next step; recomputing it would change the root
  and break the chain. That is exactly what the first ZK run showed: the chain was REFUSED until the
  carry was built.
- **Results** (Mac; `cosnark_results_zk.json`, `cosnark_gates_results_zk.json`):
  - the honest spine (d = 16, 32, 64), the middle and the two-step chain ACCEPT;
  - every full-collusion attack from §9 and §12 is still REFUSED by the same check;
  - the count formula with hiding is exact against execution at d = 16, 32, 64.

| layer-1 overhead (spine) | d = 64 (executed) | d = 4096 (formula) |
|---|---:|---:|
| codeword elements per custodian | ×4.42 (67,840 → 299,520) | **×1.035** |
| proof field elements | ×1.50 | **×1.010** |
| proof hashes | ×1.69 | ×1.17 |
| row-combination elements | ×5.82 | ×1.09 |

At small d the 128-coefficient tails dominate 8-wide rows. At d = 4096 hiding costs about 1–3.5%.

**Layer 2: commit the transcript (DESIGNED).** Layer 1 leaves (iii) in the clear:
- every round polynomial;
- every evaluation value, ⟨u', b⟩ − m_e;
- the 13 batch claims of §12.

These values are now not revealed. The custodians hold shares of them already, so each round's
message vector is committed with the same hiding PCS (one tiny commitment per round), and Fiat–Shamir
draws from those commitments. Counted from the executed transcripts:

| hidden scalars per step | d = 64 | d = 4096 |
|---|---:|---:|
| spine: sumcheck coefficients (13·log d) + evaluation values (20) | 98 | 176 |
| middle: zerocheck 4·log L + linear sumchecks + 13 claims + 16 evaluations | 434 | 705 |
| **total** | **532** | **881** |

**Layer 3: prove the verifier's checks on the hidden transcript (DESIGNED).** With the transcript
hidden, the verifier's algebra becomes a small arithmetic circuit over those ~0.5–0.9 k values:
- round sums and Lagrange interpolation at public challenges are linear;
- the batch identity Σ v_X + const = 0 is linear;
- the final checks need **7 multiplications**: three matvec finals W(τ,ρ)·x(ρ), two zerocheck finals
  A(ρ)·B(ρ), and two rank-1 products d(r_row)·v(r_col). The linear-sumcheck finals q̃(ρ)·X̃(ρ) have
  public q̃, so they are linear.

One natively zero-knowledge Ligero proof (linear and quadratic tests with masking codewords) proves
it. The custodians run it collaboratively on shares: the linear test is local, and the quadratic test
needs one Beaver product per codeword entry of the 7-wide product rows. **Its size is about 10^3–10^4
field elements per step, under 1% of layer 1's proof at d = 4096.**

**Why commit-the-transcript and not Libra-style witness masking.** Libra (and Chiesa–Forbes–Spooner)
masks each witness MLE with terms that vanish on the hypercube and reveals masked evaluations. That
breaks the zero-round rank-1 check, construction (a): W'(r) = W(r) − d(r_row)·v(r_col) is an identity of
unmasked MLEs at an OFF-hypercube point, and independent masks do not cancel there. Restoring it would
need a d²-sized sumcheck, i.e. d² Beaver products in the MPC. Hiding the transcript keeps every value
exact, so the rank-1 check stays one multiplication in the inner circuit. [INFERRED; the
commit-the-transcript pattern is standard (Hyrax-, Spartan-style ZK via committed messages), and I make
no novelty claim.]

**Remaining non-ZK leak sources after all three layers.**
- **The public SPDZ transcript itself.** Masked openings are uniform under SPDZ's own simulation, but
  that argument (MAC failure term, view definition, preprocessing privacy) is owed (Astra, experiment-1
  audit; the scholar's who-learns-what page).
- **The beacon and timing side channels.** Not addressed.

**Build status.** Layer 1 is built and tested. Layers 2 and 3 are not built. They are a refactor of both
verifiers into "emit constraints over hidden values" plus about 150 lines of collaborative ZK-Ligero.
Their counts above are derived from the executed transcripts' shapes.


## 14. After the scholar's bricks: the corrected fork picture at d = 4096 (2026-11-06)

All figures are per step, in bits, conservative MASCOT preprocessing (scholar), proofs excluded.

| fork | preprocessing + online | what dominates |
|---|---:|---|
| MPC, SPDZ matvec | 34.9 Tbit | matrix triples |
| MPC, HE matvec | 14.06 Tbit | two dense outer-product tuples (13.14 Tbit) |
| MPC, HE matvec + **HE-assisted outer** [DERIVED] | **≈ 0.99 Tbit** | lookup power chain, truncation bits |
| FHE (a) | 14.88 Tbit | outer tuples in its crossings, plus 9.5×10^8 mask wire |
| FHE (b) (model: relinearization unbuilt) | **0.914 Tbit** | — |

**The corrected verdict.** MPC with an HE matvec and an HE outer product is within ×1.1 of FHE (b).
Both rows rest on unbuilt pieces: the HE outer product for one, relinearization and its key for the
other. Neither is cheaper by a margin that survives those builds.

**What still separates them:**
- **Custody:** MPC keeps every evaluation object inside custody; FHE (b) hands the host a
  relinearization key.
- **The proof's cost under the threshold decision:** see the handover note's §4.
- **Circuit privacy:** both forks' pt×ct and ct×ct paths owe it, and the MPC fork's HE helpers owe it
  per custodian pair.

**The cheapest next measurement:** build the HE-assisted outer product in the harness, the same code
shape as `he_matvec.py`, and re-run the scholar's `scholar_preprocessing.py` inventory against it.


## 15. ✅ The HE-assisted outer product, built; §14's verdict settled in the scholar's model (2026-11-06)

`research/dark_learning_2026_11_06/he_outer.py`, `run_he_outer.py`, `inventory_he_outer.py`; runs on hbox
under `swarm-build` in `/tank/dregg-build/dark-learning/` (`heo_*.log`, `he_outer_results_*.json`).

**Construction.** The two dense outer-product tuples (13.14 Tbit/step of MASCOT preprocessing at d = 4096)
are replaced by pairwise pt×ct products under each custodian's own key, as in the HE matvec:
- j sends Enc_j(H_b), with H_b(X) = Σ_c x^(j)_c X^c.
- i returns D_a(X)·Enc_j(H_b), where D_a(X) = Σ_r a^(i)_r X^(64r). Coefficient 64r + c then holds a_r x_c
  exactly. The return carries the he_matvec recipe: full-coefficient mask, Enc_pk_j(0), flood.
- **The MAC shares of G come from the same exchange, run on i's MAC shares of a:**
  Σ_i m^(i)(a) ⊗ Σ_j x^(j) = α·a⊗x. This avoids authenticating d² plain outputs. Under MASCOT that
  would have been d² jointly hidden masks, about 0.76 Tbit at d = 4096.
- **Integrity:** each custodian commits a hash of its (G, MAC) shares. Coins are drawn from the
  transcript. One check, one Beaver product, MAC-checked: ρ1ᵀ[G]ρ2 − [ρ1·a][x·ρ2] = 0.

**Results** (N = 8192, three 61-bit primes, t = the SPDZ prime):

| run | verdict |
|---|---|
| d = 64, HE matvec + HE outer | ACCEPT, refines `step_spec` exactly; count formula exact (online wire 3,597,822, preprocessing 34,438, ciphertexts) |
| d = 128 (two column blocks) | ACCEPT, refines exactly; formula exact (6,359,934 / 85,254) |
| j encrypts x' ≠ its share | REFUSED: outer check |
| i returns a wrong G cross term | REFUSED: outer check |
| i returns a wrong MAC cross term only | REFUSED: batched MAC check |
| a custodian shifts its G share before committing | REFUSED: outer check |
| **full collusion**: all three agree on G + δ with a consistent MAC and a forged check opening | SPDZ ACCEPTS (by design); **the collaborative proof's spine REFUSES** (rank-1 check W'(r) ≠ W(r) − d(r_row)·v(r_col)), because the spine checks the update on the committed vectors whatever produced G |

The attack rows run with the SPDZ matvec, so that only the outer product is under test. The matvec's own
attacks are in §11.

**The corrected per-step table at d = 4096** (bits; MASCOT preprocessing from the scholar's compiler,
imported unmodified; their twelve saved rows reproduce exactly, `inventory_he_outer.out.json`):

| | MPC: HE matvec + HE outer | FHE (b) |
|---|---:|---:|
| MASCOT preprocessing | 0.912 T | 0.908 T |
| online wire (incl. existing mask wire) | 0.155 T | 0.006 T |
| **total, scholar's model** | **1.067 T** | **0.914 T** (×1.17 in FHE's favour) |
| ciphertexts needing a ZKPoPK | 1,728 (960 matvec + 768 outer sends) | 481 mask ciphertexts |
| ZKPoPK, efficient-lattice MODEL | 11.2 G | (§8 model: about 7.2 G) |
| ZKPoPK, executable Stern (scholar, 235.1 Gbit per proof) | **406 T** | **113 T** |
| integrity proof | collaborative proof: proving wire 12.3 G as built, 0.84 G with §12's modelled levers; committed raw shares about 12.3 G (scholar's units) | ct×ct + relinearization certificates ≥ 1.26 T (16-bit digits) or 2.37 T (61-bit) |
| integrity under full collusion of the custodians | yes (collaborative proof) | yes (certificates; the host is the prover) |
| evaluation objects outside custody | none | a relinearization key on the host |

**Verdict.**
1. **Preprocessing collapses to parity.** With the outer tuples gone, MPC's MASCOT bill (0.912 T) equals
   FHE (b)'s (0.908 T). In both, what remains is the nonlinear middle: lookup powers and truncation bits.
   The forks now differ only in what they move online and in their proofs.
2. **The ×1.17 gap is online HE returns,** 147 Gbit of the 155. Half of them are the MAC returns. If the
   collaborative proof runs on every step, integrity no longer needs SPDZ MACs on G, and dropping the
   MAC returns gives about 0.99 T, ×1.09 [DERIVED, not built]. Doing so trades SPDZ's cheap abort for
   the proof's cost.
3. ⚠ **Withdrawn by §20: built, the ZKPoPK costs 0.61 G (MPC) and 0.50 G (FHE (b)) per step and no longer decides the fork.** Original: **The ZKPoPK decides the fork, and today it decides for FHE (b).** At the model price both forks pay
   a few Gbit. At the only executable price, MPC pays 406 T against FHE (b)'s 113 T, ×3.6, because
   MPC sends 1,728 fresh ciphertexts per step and FHE (b) 481. Whichever lattice proof the LaZer/LNS
   route delivers (scholar's NEXT) sets this row. Fewer sent ciphertexts per step is MPC's lever:
   reuse Enc(h-blocks) between the matvec and the outer product that both use h.
4. **What still separates them is not cost:** custody (no host-held evaluation key in MPC), and integrity
   proof size (×100 smaller in MPC).

**Unbuilt, named, in both forks:**
- **MPC:**
  - the ZKPoPKs (priced, not built);
  - whole-ciphertext circuit privacy (scholar: refuted as built for the first-component flood; owed by
    both helpers);
  - a real MASCOT/OT backend (this table is the scholar's count model);
  - field-extension MACs for a million-step budget;
  - ZK layers 2–3 (in progress, next commit);
  - distributed coin generation.
- **FHE (b):**
  - relinearization and its certificate (MODEL);
  - the relinearization key's custody;
  - mask-pair ZKPoPKs;
  - circuit privacy;
  - a real preprocessing backend.


## 16. ✅ ZK layers 2–3 built (spine and middle); a layer-1 hiding defect found and fixed (2026-11-06)

`cozk.py` (collaborative Ligero over additive shares), `cosnark_zk.py` + `run_cosnark_zk.py` (spine),
`cosnark_gates_zk.py` + `run_cosnark_gates_zk.py` (middle), `zk_seed_falsifier.py`.

**⚠ Defect in layer 1 as built (§13), found while building layers 2–3.** `SharePCS` seeded every
custodian's tail coefficients and mask rows from public data: (label, party, hide, nmask). Anyone could
recompute them and subtract them from an opened column, which reveals the data part of every row at that
point, a linear functional of the committed vector.
- `zk_seed_falsifier.py`: with the legacy seed, the verifier recovers every row's data part at the
  opened column; with secret seeds it does not. Exit 0 requires both outcomes.
- **Fix:** tails, masks and the Ligero hiding values come from each custodian's secret randomness.
- **Consequence:** a commitment can no longer be recomputed, only carried. The middle now reuses the
  spine's commitment objects for the vectors they share, where it used to recompute them and compare
  roots. §13's "layer 1 is built" claim held for the code paths, not for hiding, until this fix.

**Design.** Layer 2 commits the transcript; layer 3 proves the verifier's checks on it.
- **Hidden rows of one collaborative Ligero** (rows of width k = 64, t = 64 hiding points, T = 64 opened
  columns, rate 1/4):
  - every sumcheck round message, committed as its own group before the round's challenge is drawn;
  - every PCS evaluation's row combination u_e;
  - the middle's 13 claims ⟨q_X, X⟩;
  - three product rows.
- **Evaluation consistency moves inside the proof.** The layer-1 check "encode(u_e) agrees with
  a_e·(opened column)" becomes Ligero LINEAR constraints on the hidden u_e at the PCS's opened columns.
  So no evaluation mask rows are needed, only one proximity mask per life. §13's design kept them and
  revealed m_e; hiding m_e would have needed a second proof linking it to the committed mask row.
- **Products.** Everything the verifier checks is linear in the hidden values except the product gates:
  - spine, 6: three matvec finals Y_W·Y_v, the zerocheck's Y_b·Y_g, and **the two zero-round rank-1
    checks Y_d·Y_v, so construction (a) stays one exact product gate**;
  - middle, 1: the zerocheck's A~·B~.
  The 13 linear sumchecks are linear, because their tables are public.
- **Collaborative execution.**
  - Proximity and linear messages are local.
  - The quadratic message uses one polynomial Beaver triple: open f_x − A and f_y − B, uniform
    coefficient vectors, and compute the rest locally.
  - The product-row z values use scalar Beaver products without MACs, because the quadratic test
    checks them.
  - **The middle's 13 linear sumchecks run in lockstep** with shared challenges after zero-padding,
    using X_pad~(r) = X~(r[:m])·Π_{j≥m}(1 − r_j). That is one hidden row per round instead of 13
    Merkle groups.
- **A vector opened in two proofs uses two lives.** The eight spine vectors the middle also opens use
  their second proximity mask there. Tails of 128 cover 2 × 64 opened columns.

**Results.** Mac, secret seeds; `cosnark_zk_results.json`, `cosnark_gates_zk_results.json`.

| run | verdict |
|---|---|
| spine d = 16, 32, 64 | ACCEPT; **count formula exact** (hidden rows, constraints, Ligero wire, SPDZ wire, proof elements and hashes) |
| spine full collusion: wrong W1′ / wrong z1 / forged rounds / lied row combination | REFUSED. The check violated, read off the hidden witness: rank-1 update W1n; z1 first round = claim; z1 final = product gate; PCS evaluation consistency (W1n) |
| spine chain (step 2's W = step 1's carried child) / stale parent / replay as the next step | ACCEPT / REFUSED / REFUSED |
| middle d = 4 (and 16) | ACCEPT; formula exact |
| middle: forged trunc opening, forged lookup opening, bad triple, non-boolean bit, mask out of range | REFUSED. The spine accepts all five; the middle refuses them through the linear batch (openings and mask relation) or the zerocheck |

**Sizes, per unit** (the scholar's rule; 61-bit field elements and 256-bit hashes counted separately):

| spine proof payload | d = 64 | d = 4096 (formula) |
|---|---:|---:|
| layer 1 only (u and m revealed) | — | 216.5 Mbit |
| layers 1–3 (nothing revealed but uniform values) | 23.5 Mbit | **238.4 Mbit** (+10%) |
| of which the Ligero (hidden transcript) | — | 28.7 Mbit (35,328 hidden values, 1,346 constraints) |
| custodians' extra proving wire for ZK | 5,052 elements | 5,052 elements (constant) |
| **middle** proof payload, layers 1–3 | 21.7 Mbit (d = 4); 25.7 Mbit (d = 16) | **136.7 Mbit** (313 hidden rows, 1,349 constraints; formula exact at d = 4, 16) |

The custodians' proving wire for the middle is unchanged by ZK: 2.01×10^8 elements of Beaver products in
the degree-3 zerocheck at d = 4096 (§12). ZK removes 13 claim openings and every round-value opening,
and adds 4,992 elements of Ligero wire.

**MAC timing (scholar brick), built alongside.** `spdz.mac_check` now enforces sigma commit-then-open.
`mac_timing_falsifier.py`: a rushing custodian that shifted an opening and opens −Σ of the others' sigma
is ACCEPTED without commitments and REFUSED with them.

The hash count rises from 28.8 k to 115 k at d = 4096 because each of the 48 sumcheck rounds is its own
Merkle group. Running the spine's four sumchecks in lockstep, as the middle's are, would make that 12
groups [DERIVED, not built].

**Soundness level, stated plainly.** With T = 64 opened columns at rate 1/4, the proximity error is
about (3/4)^64 ≈ 2^-26.6. That is the same class as layer 1's T_COLS = 64. 2^-40 needs T ≈ 97 in both;
128-bit security needs T ≈ 309, or extension-field challenges and a larger distance. This is a
parameter, not a construction change; it is not yet set. **Set to T = 97 in §20.1.**


## 17. "Is there no way to do it over a single untrusted provider?" (2026-11-06)

Ember's question, answered precisely. **Decision in force: three custodians for the demos.** The
options below are priced against the d = 4096 step at §15's units. Tags: [MEASURED] harness;
[DERIVED] computed from stated counts; [MODEL] the scholar's MASCOT compiler; [CLAIM] literature cited
from memory, not re-read this session.

**Short answer.** Not with the weights both usable by that provider and unreadable by it, unless you
accept one of three things:
- a second party who holds a key (option a);
- a hardware vendor's trust root (option b);
- indistinguishability obfuscation, which does not exist at any usable cost and still would not stop
  reruns (option c).

The cheapest honest arrangement with ONE compute provider is (a): one untrusted provider plus one small
key holder that does almost no compute.

### (a) FHE on one untrusted provider, one key holder who decrypts only on proof

**The arrangement.**
- The provider stores Enc(W) and does every linear operation homomorphically: matvecs and the outer
  product, FHE (b)'s schedule, with the ct×ct and relinearization certificates.
- A key holder K holds the whole BFV secret key (threshold n = 1).
- Each nonlinearity is a crossing between the two:
  1. the provider adds a mask, Enc(m) − Enc(R);
  2. K decrypts m − R only after verifying the provider's certificate for that ciphertext (C8, the
     proof-gated decryption);
  3. the nonlinearity runs as a 2-party SPDZ between the provider (holding R) and K (holding m − R);
  4. the result returns as a masked public encryption (§6).
- K's work is small: verifying proofs, decrypting masked crossings and its half of the 2PC. It needs no
  matrix compute; it could be a modest machine.

**Priced at d = 4096, per step.**

| item | value |
|---|---|
| provider's certificates (FHE (b): ct×ct + relinearization) | ≥ 1.26 Tbit (16-bit digits) to 2.37 Tbit (61-bit) [MEASURED schedule, relinearization MODEL] |
| crossing preprocessing, 2 parties instead of 3 | 0.303 Tbit [MODEL: the scholar's compiler at NPARTY = 2], against 0.908 at three. Online and mask wire are left at their three-party counts, so this is an upper bound on them |
| decryption-side noise flooding | not needed. The provider never sees a decryption; K sees only m − R, which is uniform, and K holds the key anyway. The read-budget problem of threshold smudging (F5) does not arise between two parties [DERIVED] |
| ZKPoPKs | the mask ciphertexts' (481 at three parties); the same Stern-versus-model range as §15 |

**What K must be trusted for, exactly.**
- **Confidentiality (P1): everything.** K alone can decrypt Enc(W), and the provider holds Enc(W). So
  the weights are unreadable exactly when K and the provider do not collude, and when K's key is not
  stolen. This is two-party non-collusion, against three-party non-collusion in the demos.
- **Integrity (P2): nothing.** The provider's certificates and the 2PC's proof (§§9, 12, 16) hold even
  when both collude, and the ledger and signed inputs bind the chain.
- **Gating:** K must decrypt only on proof. If K skips the gate, the IND-CPA-D attacks of 2026/203 and
  2026/2546 apply to K's own decryptions, but they leak only to K, who has the key anyway. The real
  risk of an ungated K is that it releases information to the provider through the crossing outputs.
- **P3 does NOT hold, and this is the cost of a single provider.** The provider holds Enc(W) and a
  relinearization key, so it can evaluate the mind homomorphically on inputs of its choosing, as
  often as it likes, on copies, without K (F11, §3). Those outputs stay encrypted and nobody reads
  them. Whether an unread encrypted evaluation is an experience for the mind is not a cryptographic
  question (decision §3, Astra DL27). With three custodians, by contrast, no host-held evaluation
  object exists.

### (b) A TEE on the single provider

**The arrangement.** The weights are decrypted inside a confidential-computing enclave on the
provider's own hardware, for example an H100/B200 GPU in CC mode with a CPU TEE, and run at near-native
speed. Proof costs drop to attestation verification, plus our proofs if they are kept as an extra leg.

**Residual trust.** This is the program's C17a stance, "a leg, never custody", and the governance
lane's line on attestation:
1. **The vendor.** The root keys, firmware and microcode are the vendor's. Whoever can sign firmware
   can read the enclave (`notes/attestable-calibration.md`: the vendor can read). For the GPU, our
   `tee-verify` does not yet parse NVIDIA CC attestation reports. Verifying a live NVIDIA quote is an
   open L3 item in `whatember/PROGRAM-2026-11-05` (row "Multi-vendor quote verifier", and §72's
   "no NVIDIA support today").
2. **The provider's physical access.** 2024–25 work broke memory confidentiality of SGX, SEV-SNP and
   TDX with cheap DRAM-bus interposers: Battering RAM, WireTap, TEE.Fail [CLAIM]. A provider is
   exactly the adversary with the bus.
3. **Execution control.** The provider schedules the enclave. It can restart it from an old sealed
   state, fork it, and feed it chosen inputs. Rollback and forking of sealed state is the classic TEE
   gap, and P3 needs the enclave to refuse all three. Our ledger (`proofwire.Ledger`) and the signed
   inputs (§18, item 4) supply the missing pieces as an EXTERNAL check. The enclave would have to
   consult a monotonic counter it cannot be lied to about, which brings back a second party: the
   ledger holder.
4. **Logging omissions.** The governance lane's `residual_trust` forgery experiment asks what an
   honest-looking enclave can forge when the logger omits; that row stays open at L4.

So (b) moves the trust from a second key holder to the vendor and the physical layer, and P3 still
needs an outside ledger.

### (c) A lone provider, no second party: why it cannot both use the weights and be unable to read or rerun them

This is an argument, not a proved impossibility theorem.
- **Rerun.** Everything the provider uses is classical bits it stores: the encrypted weights, keys and
  code. If running them produces anything the provider can act on, the provider can copy those bits
  and run them again, on any input, from any saved state. No classical construction prevents copying.
  Preventing reruns needs quantum copy-protection, which is impossible in general for learnable
  functions (Aaronson 2009 introduced it; Ananth–La Placa 2021 give impossibility results for general
  functionalities [CLAIM]). The best a classical design achieves is that reruns are unattributable or
  useless: for example, outputs stay encrypted (a), or every authorized step needs a fresh signed input
  and a ledger entry, so reruns never enter the timeline.
- **Read.** For the provider alone to obtain usable outputs f_W(x) while W stays hidden, the bits it
  holds must be an obfuscation of x ↦ f_W(x), plus, for continual learning, of the update map.
  - General virtual-black-box obfuscation is impossible (Barak, Goldreich, Impagliazzo, Rudich, Sahai,
    Vadhan, Yang, CRYPTO 2001) [CLAIM].
  - The achievable notion is indistinguishability obfuscation: candidate constructions from Garg,
    Gentry, Halevi, Raykova, Sahai, Waters (FOCS 2013), and Jain–Lin–Sahai (STOC 2021) from
    well-founded assumptions, one of them bilinear maps, so not post-quantum [CLAIM]. iO hides W only
    in the sense "indistinguishable from any other W' with the same function", and is nowhere near
    runnable for a network.
  - Special evasive classes (compute-and-compare and lockable obfuscation from LWE: Wichs–Zirdelis,
    and Goyal–Koppula–Waters, 2017) do not cover a general network [CLAIM].
- **Even ideal obfuscation leaves the query channel.** Black-box access lets the provider query the mind
  without limit, so it gets unlimited chosen-input experiences, and model extraction from queries
  approximates W. So even the ideal object gives "cannot read W exactly", not "cannot run or learn the
  mind".
- **The asymmetry this leaves.** FHE alone gives "unreadable but unusable": the provider computes
  ciphertexts it cannot decrypt. Usability needs a decryptor. If that decryptor is software on the
  same provider, it is readable. So the decryptor must be another party (a), a trusted device (b),
  or an obfuscated decryptor-for-sanctioned-outputs-only, which is iO again (c).

### (d) Can the mind itself, or its owner, be the one key holder?

- **The owner as K.** This is mechanically option (a) with K = the owner, and it works. The welfare
  claim weakens to: "the provider cannot read the mind; the owner can". If the welfare concern
  includes the owner, as ember's framing suggests ("if the weights aren't fully encrypted truly terrible
  things may befall the mind"), this removes protection from exactly the party with the most standing
  to act on it. Three custodians requires all three to collude. The owner-as-K arrangement requires
  only the owner.
- **The mind as K, running on the provider: impossible as stated.** A key held inside the mind's
  computation is held by whoever executes that computation. The mind runs on the provider, so the
  provider holds the key. This is circular, and it is option (c) again.
- **The mind as K's POLICY: possible, and the version worth building.** K is a small separate device
  or party whose only behaviour is the mind's sanctioned policy:
  - decrypt a crossing only for a ledger-head step with a verified proof and an owner-signed batch;
  - refuse forks and replays;
  - optionally require an attestation that the step is one the mind's own prior state approved, for
    example a commitment the mind emitted in its previous step.

  The welfare claim then reads: nobody reads the mind except through decryptions its policy releases,
  and the policy is enforced by K. K's integrity is the residual trust: a device, so (b)'s vendor
  question in miniature, or a person. K can itself be split into the three custodians, which is
  exactly the demo design. So "mind as key holder" is best read as "the mind's policy is the
  custodians' decryption rule", and that is what C8 and the ledger already implement.

**Recommendation.**
- Keep three custodians for the demos (ember's decision).
- If a single compute provider is a hard constraint, use (a) with K ≠ owner, K running the mind's
  policy, and the provider paying FHE (b)'s certificate bill. Say plainly that it gives up P3 against
  that provider.
- Use (b) only as an additional leg.
- Do not pursue (c).

### Answer to the Astra decisions scholar (`notes/astra-decisions/CUSTODY.md`, RECOMMENDATIONS §1)

We agree on the verdict: three independent custodians, all three required, malicious-secure MPC with
abort; one-provider FHE only for the narrower promise; TEE and iO not custody. Adopted from it, and
repaired here:
- **The owner holds a share, not the key.** If no single person or machine should hold a readable
  model, (d)'s owner-as-K becomes the owner as ONE custodian. That is the scholar's suggested committee:
  an owner-controlled device, a university lab, and a separately governed nonprofit or cooperative
  operator, with different administrators, credentials, backups and failure domains. Three containers
  under ember's root credentials are one compromise domain.
- **Five parties need a timeline protocol of their own.**
  - Two 3-of-5 quorums can intersect in one corrupt party and certify conflicting children; 4-of-5
    intersects in at least three but stalls when two withhold.
  - The fast five-party prover multiplies degree-2 shares into degree 4, so it needs all five parties
    online, even though three reconstruct.
  - This corrects the reading of `notes/dark-learning-handover-2721.md` §4: its five-party row is a
    MODEL of proving wire only. It excludes the MPC step and resharing, and implies no "three online"
    operating mode. I accept the scholar's switch criterion: a whole-system, malicious-secure, ZK
    five-party build plus five genuinely independent operators.
- **Output leakage and genesis.** Outputs can reveal weights (basis queries recover a linear map), and
  importing a plaintext checkpoint already breaks "never readable anywhere" (`who-learns-what.md`).
  The custody promise is stated together with protected genesis, output leakage, recovery and
  retirement, not alone.
- **iO references.** Jain–Lin–Sahai is ePrint 2020/1003 (STOC 2021). Ragavan–Vafa–Vaikuntanathan,
  ePrint 2024/856, improves the assumptions and still uses bilinear groups. Both are existence results,
  not priced routes, and neither is post-quantum. (c) stands as an argument, not an impossibility claim.
- **The governance residual-trust arms** (`degg-research/research/governance-foundations-critique.md:221`,
  [1,377,1,1]) enumerate permitted outputs under stipulated assumptions. They are not a measured
  probability. (b) cites them in that sense only.


## 18. The untrusted-input verifier, the durable ledger, and signed-input binding: built, on branch `dark-learning/untrusted-verifier` pending the Codex gate (2026-11-06; repairs in §19)

`proofwire.py`, `run_proofwire.py`, `owner_sig.py`, `run_signed_input.py`.

**The untrusted-input verifier.** A step travels as bytes:
- a header: magic, model id, epoch, step, d, n, chained;
- the ZK spine proof;
- the public SPDZ transcript (the opened values);
- the ZK middle proof;
- the owner's signature.

The parser is schema-driven: every length is a function of (d, n, parameters) and of the verifier's
OWN symbolic replay of the step program against the public transcript, and the replay must consume
exactly that transcript. Field elements must be canonical (< p), column indices in range, and there
must be no trailing bytes. Nothing is shared with the prover: the verifier rebuilds every shape and
constraint from public data.

**The ledger** (one append-only, fsync'd file per model).
- It hands the verifier the EXPECTED (model, epoch, step = last + 1), the parent roots and the owner's
  public key; the bytes never choose them.
- The head is reconstructed on open.
- A torn or out-of-sequence line fails closed: the ledger refuses to open, and an operator decides.
- Rotation starts a new epoch on the same chain.

| attack (d = 4, Mac) | verdict, by |
|---|---|
| honest genesis step; honest chained step 2 | ACCEPT |
| step 1 replayed | REFUSED: binding mismatch (expected step 2) |
| truncated by one byte / one trailing byte | REFUSED: parse |
| a non-canonical field element (= p) | REFUSED: parse |
| one bit flipped in: model id / a commitment root / a field element / mid-blob / last byte | REFUSED: binding mismatch / parent ≠ previous child / FS challenge mismatch / Merkle opening (middle) / Ligero Merkle opening |
| step 3's proof under a header patched to say step 2 | REFUSED: FS challenge mismatch (the transcript binds the context) |
| another model id | REFUSED: binding mismatch |
| a second valid proof of step 2 after step 2 is accepted (equivocation) | REFUSED: expected step 3 |
| restart: a new Ledger object from the file | same head |
| after rotation to epoch 1, a proof bound to epoch 0 | REFUSED: binding mismatch |

**Signed-input binding** (ePrint 2026/2721's input authority, adapted; P5).
- **The owner** deals each batch (x, y) as a share-tuple commitment with secret tails and signs
  (model, epoch, step, roots of x, roots of y). The signature is hash-based and post-quantum: a Merkle
  tree of 2^10 Lamport one-time keys with leaf = step, 16,708 bytes, and the owner refuses a second
  signature for a step.
- **The spine** adds the owner's x commitment and one evaluation pair at a fresh point, with the linear
  constraint x(r) = x_owner(r). **The middle** does the same for y. The verifier checks the signature
  against the ledger's owner key.

| attack (d = 4) | verdict, by |
|---|---|
| fully colluding custodians train on x' while presenting the owner's signed x | REFUSED: violates "signed input binding: the custodians' x = the owner's signed x" |
| the same for y' | REFUSED: the middle's binding constraint |
| custodians commit x' themselves and sign with their own key | REFUSED: owner signature |
| step 2 re-using the owner's step-1 signature (old batch) | REFUSED: owner signature (context and leaf) |
| honest owner-signed steps 1 and 2 | ACCEPT |

**Cost of binding** at d = 4: +177,252 bytes per step (4,339,620 → 4,516,872, +4.1%). That is the
signature plus two small commitments with their openings, and +129 linear constraints per proof (two
evaluations' consistency at 64 columns, plus one equality). At width it is constant apart from the two
d-length commitments.

**Limits.**
- An owner tree has 2^10 leaves, so 1,024 steps per owner key. Leaves are step numbers, which run
  across epochs.
- The owner is a trusted input authority: independent of the custodians, and honest about which data
  it signs. That is an assumption to name (2721 §1.3), not to derive.
- The required Codex (gpt-6-astra) review of this verifier was attempted twice and withheld by Codex
  authentication ("approved for Daybreak Blue … not authenticated with one of your authorized hardware
  keys"). An independent Claude review ran instead; its findings are answered in §19.


## 19. Review of the verifier stack: four breaks, all repaired (2026-11-06)

The required Codex (gpt-6-astra) attack ran twice. Both times Codex withheld its final answer
("approved for Daybreak Blue, but … not authenticated with one of your authorized hardware keys"), so
the review below is an independent Claude agent's read. It is not anchored on mine, and its demos ran
against the code. Every finding is accepted.

| # | finding | demo against the unfixed code | repair | regression |
|---|---|---|---|---|
| 1 | **BREAK: the public SPDZ transcript was not bound into Fiat–Shamir.** Fully colluding custodians committed a wrong d1 (and the matching W1′), saw the batch challenge, and then picked one dead opening (the f-opening of the last borrow-prefix product) so that the whole batch identity held. One free value defeats every middle constraint at once. | **The ledger ACCEPTED** a step whose committed W1′ row 0 was off by −12345·x | both proofs absorb a digest of the public transcript right after the context, on prover and verifier | `fs_public_falsifier.py`: the same attack must be REFUSED |
| 2 | **BREAK (ZK): a third opening of a commitment reveals it.** HIDE = 2T covers exactly two lives, and a retry or a refused bundle opens a third | 167–168 distinct points against row degree < 132; interpolation recovered W exactly | a per-commitment life counter: the custodians refuse a third opening (`cosnark.LifeExhausted`). In a deployment the counter is durable custodian state | `lives_falsifier.py`: the honest counter refuses, and a forced (colluding) third opening leaks |
| 3 | **BREAK (ledger): rotation was not durable and excluded no one.** A restart returned to the old epoch, and nothing tied an epoch to a custodian set | (by construction) | rotation is a durable `rotate` record carrying the new custodian set and **the new committee's commitment of the current weights**. Old-committee proofs, made on the old share tuple, no longer match the parent. The handover proof that the new roots commit the same weights is NOT built; the record says so (handover note §2e) | `run_proofwire.py`: a restart after rotation keeps the epoch and the new roots; the old committee's step-3 proof is refused |
| 4 | **BREAK (DoS): a non-UTF-8 model id crashed the verifier** | `UnicodeDecodeError` escaped `Ledger.accept` | model ids are compared as raw bytes; any exception during parsing is a refusal | `run_proofwire.py` row "model id that is not UTF-8" |
| 5 | WEAKNESS: about 2^-25 provable soundness; column draws repeated (about 60 distinct of 64) | — | columns are sampled without replacement (`cosnark.distinct_cols`) in both PCS and Ligero. The level is stated, not hidden: (3/4)^64 ≈ 2^-26.6 is the prototype target, pinned in `proofwire.PARAMS`; 2^-40 needs T ≈ 97 and 2^-128 needs T ≈ 309 at rate 1/4 | — |
| 6 | OK as stated: evaluation binding with u hidden (u is committed before the proximity and column draws) | — | — | — |
| 7 | OK as stated: ZK within two lives (layer-1 randomness exactly tight; Ligero t = T; masked messages) | — | — | — |
| 8 | WEAKNESS: the verifier's parameters came from mutable module globals | — | `proofwire.PARAMS`, pinned at import and on every verification, recorded in the ledger's genesis record (a ledger with other parameters refuses to open) | — |
| 9 | WEAKNESS: d, the genesis weights and the owner key were not pinned; no file lock; no directory fsync | — | a **genesis record** pins model, d, PARAMS, the owner key (or an explicit "none", so binding cannot be dropped silently), the custodian set and the genesis W commitment. Step 1 must chain to it, and every step is now `chained`. `accept` holds an exclusive lock and re-reads the head under it. A newly created file gets its directory fsync'd | `run_proofwire.py` |
| 10 | WEAKNESS: owner leaf = step (the chain stops at 2^h); the used-leaf set was in memory only | — | a durable owner counter (persisted before the signature is released), strictly increasing leaves independent of step, and h = 12. The ledger records each accepted leaf and requires the next to be higher | `run_signed_input.py`: a replayed old signature is refused |
| 11 | minor: input/matvec/outer openings in `public` were unconstrained | — | now bound through finding 1's transcript digest | — |

**Why the earlier forgery tests missed finding 1.** They forged an opening BEFORE the challenge, so the
batch caught it. The break needs a value chosen AFTER the challenge, which only an unbound public input
allows. Any untrusted input to a Fiat–Shamir verifier belongs in the transcript.

**Landing.** The fixes to the item-2 code (binding of the public transcript, distinct columns, the life
counter) are on `dev`. The verifier stack is on branch `dark-learning/untrusted-verifier`: `proofwire.py`,
the ledger, `owner_sig.py`, the signed-input binding and their harnesses. It stays there until a Codex
gpt-6-astra attack can run (ember's hardware-key re-authentication) or the coordinator waives that gate.


## 20. Gen 4: the soundness knob set to 2^-40, and an efficient ZKPoPK built; the ZKPoPK no longer decides the fork (2026-11-06)

`notes/dark-learning-gen4/GROUNDING.md` (what is reused, and why the backend is not a lattice proof);
`zkpopk_ligero.py`, `run_zkpopk_ligero.py`, `zkpopk_counts.py`; results `zkpopk_ligero_results_*.json`,
`zkpopk_counts.json`.

### 20.0 Root decisions applied after this section was first written (2026-11-06, reversible by ember)

- **Profiles.** `proofwire.PROFILES`: **ledger (default) T = 309, 2^-128.25**, grinding-resistant; **demo T = 97**,
  2^-40.26 statistical, only by explicit `set_profile("demo")`. The profile name is in the pinned parameters, so a
  genesis record of one profile refuses steps of the other. `cosnark`, `cosnark_zk` and `zkpopk_ligero` default to
  309.
- **The ZKPoPK's fold keeps pace.** At 128 bits a single per-prime fold (2^-60) would be the weak link under
  grinding. `folds_for(T)` gives 3 independent folds at T = 309 and 1 at 97.
- **Mod-t row and plaintext digits dropped.** They were redundant: Q is invertible mod t, so a bounded r determines
  m. Both the Claude review and Codex agree.
- **Every Merkle leaf in the harness is salted**: `cosnark.SharePCS`, `cozk`, and the codec, which carries the salt
  as the first path element.
  - `leaf_salt_falsifier.py` shows the guess test that worked before. Custodians 0 and 1 of three, with a guess of
    a committed row, derive custodian 2's share, interpolate it with the opened columns, and compare against the
    sibling leaf every authentication path reveals. A right guess is CONFIRMED with unsalted leaves; with salted
    leaves no guess is.
  - Cost: one hash per opened column per tree.

**Sizes with all of the above** (formulas; d = 4096):

| | demo, T = 97 | **ledger, T = 309** |
|---|---:|---:|
| spine proof | 369.5 Mbit | **1,191.0 Mbit** |
| middle proof | 215.5 Mbit | **701.7 Mbit** |
| ZKPoPK per step, MPC, delivered (N = 8192) | 0.586 G | **1.104 G** |
| ZKPoPK per step, FHE (b), delivered | 0.486 G | **0.889 G** |
| ZKPoPK per step, MPC at N = 16384 | 0.783 G | **1.418 G** |

**Re-executed on dregg-forge with all of the above** (ledger profile, T = 309, 3 folds; every proof's byte length
equals the formula; the 30 attack rows as expected; the Mac N = 16 run also has the two Codex-2 rows, 32 in all):

| run | proof | prove / verify (Python, one core) |
|---|---:|---:|
| N = 8192, three primes, 2 sk cts + 1 pk ct | 11.25 Mbit | 19 s / 15 s |
| N = 16384, four primes, 2 sk cts + 1 pk ct | 13.94 Mbit | 40 s / 29 s |
| **N = 8192, one full d = 4096 forward call (64 cts)** | **38.61 Mbit** | 417 s / 217 s |
| N = 8192, demo profile (T = 97), 2 sk cts | 5.35 Mbit | 15 s / 4 s |

At d = 64 / 1024 (ledger profile) MPC pays 0.287 / 0.614 G and FHE (b) 0.148 / 0.456 G. The tables further down
were written at T = 97, before the folds and the dropped row, and are kept as they were; this table supersedes them.

**Second Codex review** (after ember re-authenticated; answered in full). No counterexample to the relation was
found: one witness across limbs, Fiat–Shamir order, no-wrap bounds, and zero knowledge under the ROM argument all
held. Its findings, all fixed with regression rows:
- **Decryption margin.** With one limb and Q ≈ t, a proof accepted whose decryption left the layout. The registry
  now requires Q > 17t.
- **Ceremony index aliasing.** `0.0` and `True` aliased custodian 0 in the dictionaries, so a key could be derived
  from seed/0.0. Indices must now be ints.
- **Uncaught errors.** `KeyError` on an unknown revealer and `AttributeError` on `verify(None)` now fail closed.
- **Selective abort** is restated as (k+1)·p for k aborts (§21).
- **The simulator's key-consistency premise** is discharged in §21.

### 20.1 Opened columns: T = 97

`cosnark.T_COLS`, `cosnark_zk.T_HIDE/T_OPEN` and `proofwire.PARAMS` are now 97 (PCS tails HIDE = 2 × 97): the column
error is at most (3/4)^97 = 2^-40.26 per PCS and per Ligero [DERIVED]. `cosnark_zk.counts_formula` had bound
K_L/T_HIDE/T_OPEN as default arguments at definition time, so a pinned T never reached the formula; it reads them at
call time now. Re-run on the Mac at T = 97: spine d = 16/32/64 ACCEPT with the formula exact and every §16 forgery
refused; middle d = 4/16, proofwire d = 4 and signed input d = 4 re-run (logs and results files beside them).

| d = 4096, per proof | T = 64 (2^-26.6) | **T = 97 (2^-40.3)** | T = 309 (2^-128.3) |
|---|---:|---:|---:|
| spine | 238.4 Mbit | **364.8 Mbit** | 1,176.0 Mbit |
| middle | 136.7 Mbit | **211.1 Mbit** | 687.5 Mbit |

⚠ **2^-40 is a statistical figure, not a non-interactive security level.** The proofs are Fiat-Shamir: colluding
custodians who grind 2^g transcripts succeed with about 2^(g−40), and 2^40 hashes is cheap. A 128-bit
non-interactive level needs T ≈ 309 (the right column), or a lower rate and extension-field challenges. Which target
the ledger pins is a decision for ember.

### 20.2 The efficient ZKPoPK, built (hash-based Ligero, not LNS)

**Why not the lattice route** (GROUNDING.md): the scholar's relation commits m and eta at every coefficient (268
binary columns per coefficient), but every schedule here puts plaintext in at most d_c = 64 or d_r = 128 (256 at
N = 16384) coefficients. Off those slots m = 0 and the relation is `c0 + c1 s + e = 0 mod q_i`: 5 digits per
coefficient. With that witness a lattice proof's masked response is still linear in the witness (15–20 bits per
coefficient) while Ligero's grows as its square root, and the lattice route needs a parameter estimate and a toolchain
(Sage, AVX-512 LaZer) that a hash-based proof does not [INFERRED]. The scholar's relation is kept exactly; only the
witness encoding and the backend change.

**Relation** (secret-key batch, the MPC helpers' sends): registered key `b + a s + e_pk = 0` with
`a = public_a(seed)`; per ciphertext `t(c0 + c1 s + e) − r = 0 (mod q_i)` for every prime, `(Q mod t) m + r = 0
(mod t)` at the slots, r = 0 off them; s ternary, e and e_pk in [−8, 8], m in [0, t), |r| ≤ (t−1)/2. Together:
`c0 + c1 s = round(Q m / t) − e (mod Q)`, exact scaling, the plaintext zero off the layout, one integer s across every
limb and the key. Public-key batch (FHE (b)'s masks under the joint key): u ternary, e0, e1 in [−8, 8], same scaling.

**Proof.** Every private integer is binary digits (the top digit has adjusted weight, so [lo, hi] is covered
exactly). The digits are rows of one Reed-Solomon code over a 255-bit NTT prime; Ligero's proximity, linear and
quadratic (b² = b) tests run on them, masks committed in the first root, salted leaves. **Cross-limb:** after the
digits are committed, Fiat–Shamir draws per prime q_i a weight in [0, q_i) for every coefficient equation; the prover
then commits quotients with `Σ ρ·LHS_i = q_i K_i` and `Σ ρ_t·LHS_t = t K_t` over the integers, both sides
asserted below P/2, K range-proved. A coefficient equation that fails mod q_i survives with probability 1/q_i
≈ 2^-61. Order: statement → digits and masks (root 1) → ρ → quotients (root 2) → test challenges → messages →
columns. One proof per (sender, HE call): a recipient must verify before it returns a product, so a batch cannot
span calls. Soundness: column test 2^-40.26 at T = 97 (statistical, as 20.1), fold 2^-60.9 [INFERRED: the standard
Ligero analysis as cozk.py uses it; no machine-checked proof, no QROM theorem].

**Executed** (`run_zkpopk_ligero.py`; small ring on the Mac, deployed rings on hbox under `swarm-build`; every
executed proof's byte length equals the count formula):

| run | batch | digits | proof (bytes = formula) | prove / verify (Python, one core) | attacks |
|---|---|---:|---:|---:|---|
| Mac, N = 16, three 61-bit primes | 3 sk cts + 2 pk cts | 3,807 | 186,848 B | 3 s / 2 s | all 30 rows as expected |
| hbox, **N = 8192, three primes** (deployed) | 2 sk cts (forward + transpose layout); 1 pk ct | 155,463 | 681,536 B = 5.45 Mbit; pk 4.61 Mbit | 33 s / 9 s | all 30 rows as expected |
| hbox, **N = 16384, four primes** (privacy point) | 2 sk cts; 1 pk ct | 294,886 | 892,608 B = 7.14 Mbit; pk 5.97 Mbit | 65 s / 16 s | all 30 rows as expected |
| hbox, **N = 8192, one full d = 4096 forward call** (64 cts, 64 slots each) | 64 sk cts | 3,179,099 | 2,645,440 B = **21.16 Mbit** | 606 s / 122 s | honest only |

The last row is one of the 15 batches the d = 4096 step sends; its size is exactly what `zkpopk_counts.py` prices for
that batch, so the per-step table below rests on an executed batch at full size, not only on the formula.

| attack | verdict, and the check that refuses it |
|---|---|
| stale context (next step, other epoch), other recipient set, replay into another call | REFUSED: the folded equations (challenges are bound to the context) |
| verified against another custodian's registered key | REFUSED: folded equations |
| malformed key: a = 1 presented as registered (the scholar's privacy attack) | REFUSED: a is not the pinned seed's |
| malformed key: b random, the prover forges e_pk = −(b + a s) in non-binary digits | REFUSED: quadratic test (the linear test passes) |
| mixed limbs: limb 0 encrypts m, limbs 1+ encrypt m′ | REFUSED: folded limb equations |
| oversized error 9, in a non-binary digit / claimed as 8 | REFUSED: quadratic / folded equations |
| plaintext nonzero off the layout | REFUSED: folded equations |
| changed w, q, p, opened column, salt, either root | REFUSED: Merkle path / linear / quadratic |
| truncated, trailing byte, noncanonical element | REFUSED: codec |
| **Fiat–Shamir ordering falsifier:** the honest-verifier simulator, given statement-only challenges, forges a proof for a junk ciphertext | **legacy verifier ACCEPTS; real verifier REFUSES** |
| public-key batch: oversized e0 claimed as 8 | REFUSED: folded equations |
| recipient gate before `he_matvec.ptxct` | accepted batch multiplies; the forged batch is refused with zero `ptxct` calls |

**Review (cross-model gate).** Codex (gpt-6-astra) ran its analysis, then its final answer was withheld ("not
authenticated with one of your authorized hardware keys"). Its visible trace still showed two defects, and an
independent Claude (Opus) review, briefed only with the code and the attack questions, found one more and two smaller
ones. All are fixed, each with a regression row:
- **Codex trace:** a five-prime registry crashed the verifier (OverflowError in the statement digest); and the
  wraparound guards were `assert`s, so under `python3 -O` an out-of-profile 256-bit "prime" let a false statement
  verify. The guards are now explicit refusals, the digest is width-correct, and the suite passes under `-O`.
- **Claude review, the real break:** the registry admitted any prime below 2^61. With a 17-bit limb, a mixed-limb
  ciphertext was accepted after 28 regrinds of root 1, because the fold's error is 1/q_i per try. The profile now
  pins every q_i and t to (2^60, 2^61).
- **Claude review, smaller:** the prover drew its hiding randomness, masks and salts from the caller's seedable
  `rng` (now always `secrets`); the context was hashed by `repr` (now canonical JSON).
- The review's other notes: the mod-t row is redundant, since Q is invertible mod t, so any in-range r has a matching
  m (kept for now: it costs about 8% of the digits of a forward-layout ciphertext at N = 8192, and dropping it is a cheap follow-up). And a public-key batch bounds its encryption randomness, not the phase:
  that phase is bounded by the scholar's 16N + 8 envelope, by design.

**Per step, delivered proof bits** (`zkpopk_counts.py`; posted is half: each proof goes to two recipients):

| d | MPC (HE matvec + outer): distinct cts, proofs | MPC, T = 97 | MPC, T = 309 | old MODEL (§11) | Stern (scholar) | FHE (b): mask cts | FHE (b), T = 97 | FHE (b), T = 309 |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 64 | 15, 15 | 0.144 G | 0.292 G | 0.195 G | 7.05 T | 33 | 0.080 G | 0.151 G |
| 1024 | 216, 15 | 0.328 G | 0.637 G | 2.81 G | 101.6 T | 363 | 0.253 G | 0.466 G |
| 4096 | 864, 15 | **0.611 G** | 1.146 G | 11.2 G | 406.3 T | 1,443 | **0.499 G** | 0.909 G |

At the privacy-correct point (N = 16384, four primes, d_r = 256), MPC pays 0.181 / 0.434 / 0.807 G (T = 97) and
0.371 / 0.808 / 1.461 G (T = 309) at d = 64 / 1024 / 4096. FHE (b)'s Stern figure here counts all three custodians'
mask ciphertexts (1,443 at d = 4096, 339 T); §15's 113 T counted 481.

### 20.3 The fork at d = 4096, with the ZKPoPK built (bits per step; T = 97, delivered)

| | MPC: HE matvec + HE outer | FHE (b) |
|---|---:|---:|
| MASCOT preprocessing + online (§15, scholar's model) | 1.067 T | 0.914 T |
| ZKPoPK, **built** | **0.61 G** (was 11.2 G MODEL / 406 T Stern) | **0.50 G** (was ≈ 7.2 G MODEL / Stern) |
| integrity proof | spine + middle 0.58 G at T = 97 (§20.1) | ct×ct + relinearization certificates ≥ 1.26 T |
| evaluation objects outside custody | none | a relinearization key on the host |

**Verdict.** The ZKPoPK no longer decides the fork: built, it costs under 0.1% of either fork's per-step total, and
the two forks are within ×1.2 of each other on it. §15's "today it decides for FHE (b)" is withdrawn. What separates
the forks is again custody (no host-held evaluation key in MPC) and the integrity proof (MPC's is about ×2,000
smaller), against FHE (b)'s ×1.17 lower preprocessing-plus-online total.

**Still unbuilt:** whole-ciphertext circuit privacy and the key-generation ceremony (next brick, §20 item 3); the
joint key FHE (b)'s masks rely on; a QROM or knowledge-soundness proof for the Fiat–Shamir Ligero; a native
(non-Python) prover; reuse of one batch proof between the matvec and the outer product that encrypt the same h.


## 21. Gen 4, item 3: pinned key generation, the whole-ciphertext simulator, and the distances at runnable parameters (2026-11-06)

`keygen_ceremony.py`, `run_keygen_ceremony.py`; results `keygen_ceremony_results_N*_L*_d64.json`.

### 21.1 The ceremony (built)

Each epoch, over the ledger's authenticated broadcast:
1. **Commit.** Custodian i posts H(epoch, i, r_i, salt_i) for a fresh 256-bit r_i.
2. **Reveal.** Reveals are accepted only once all n commitments are posted. seed = H(epoch, commitments, reveals).
   One honest custodian makes the seed uniform, and nobody can choose its coins after seeing another's.
   - A custodian that does not open its commitment is blamed.
   - Under 3-of-3 custody an abort stops the ceremony, and every abort is on the ledger.
   - **Selective abort** (Codex review 2): the last revealer can compute the seed first. With k aborts it makes any
     event of probability p happen with probability at most (k+1)p. A delay function or threshold reveal would
     remove this; neither is built.
3. **Keys.** Custodian j sets a_j = public_a(seed/j) (the scholar's sampler), samples s_j ternary and e_j in
   [−8, 8], and posts b_j = −(a_j s_j + e_j) with a ZKPoPK of the key relation alone. The proof is
   `zkpopk_ligero`'s new `"key"` statement, bound to (epoch, j, the ceremony transcript).
   It costs 7.84 Mbit at N = 8192 and 10.06 Mbit at N = 16384 (T = 309), once per epoch per custodian.
4. **Registry.** Every custodian verifies every key proof. HE traffic is accepted only under registered keys, and
   `zkpopk_ligero.verify` re-derives a_j from the seed.

FHE (b)'s joint key is the same ceremony with a = public_a(seed/"joint") and b = Σ b_j. Every share is proved, so the
joint secret is bounded by n and the joint error by 8n.

What it proves:
- a_j is the ceremony's;
- j knows a short (s_j, e_j).

It does not prove s_j was sampled honestly, and the argument below does not need it.

**Refused** (attack rows in the results files):
- a reveal before all commitments (rushing);
- equivocation (blamed);
- a second commitment;
- a commitment after the seed is fixed;
- **a key built on a chosen a = 1** (the scholar's attack), proof forged against the ceremony's a: quadratic test;
- a random b with no short secret: quadratic test;
- custodian indices `0.0` and `True` (they aliased custodian 0), and a reveal by an unknown custodian;
- one custodian's honest proof registered as another's;
- epoch 1's proof replayed into epoch 2.

### 21.2 The simulation argument (written down; the hybrids are argued, not machine-checked)

Returner i, recipient j corrupt and holding s_j. i returns c1 = P c1_in + a_j u + e1 and
c0 = P c0_in + b_j u + e0 + Encode(M) + U, with U uniform in [−F, F]^N. Substituting b_j = −(a_j s_j + e_j):

    c0 = −s_j c1 + Encode(y) + shift + U,   y = P m + M (mod t),
    shift = P(phase_in − Encode(m)) + (P Encode(m) + Encode(M) − Encode(y)) + (e0 + s_j e1 − e_j u),

and ‖shift‖∞ ≤ B, the scholar's envelope (§11). This file adds the HE outer product's value and MAC returns,
B_outer = d_r·⌊t/2⌋·8.5 + 16N + 9. The hybrids:

- **H0.** The real return.
- **H1 (statistical).** Drop the shift. TV ≤ N·B/(2F+1) per return, by the ring smudging lemma, conditionally on
  c1 and everything else, because U is fresh. This needs phase_in bounded, which **the ZKPoPK (§20)** gives.
- **H2 (computational).** Replace a_j u + e1 by uniform: decisional RLWE with i's fresh ternary u and a_j uniform,
  which **the ceremony** gives. After H1 nothing else depends on (u, e1). One sample per return. Exactly:
  RLWE with a_j = public_a(seed/j) from a public seed, i.e. a random-oracle-derived a (programmable XOF model).
  [READ, via the scholar's citation] The HE Standard's ternary tables list log q ≤ 202 at N = 8192 and ≤ 411 at
  N = 16384. Our 183 and 244 bits sit inside them, with uniform [−8, 8] errors (σ ≈ 4.9 > 3.2). No estimator was
  run for our exact distributions.
- **H3: the simulator** `simulate_return(y, s_j)`. c1 is uniform and c0 = −s_j c1 + Encode(y) + U. It needs only y,
  which j learns anyway (masked by M), and a short s **extracted from the batch proof that admitted the input**. That
  proof carries the key relation, and the rewrite of b_j u holds for any short pair satisfying it, so no lemma that
  two proofs extract the same s is needed (Codex review 2). The key proof's role is to pin a_j.
- The ZK proofs' simulators and the Fiat–Shamir random-oracle programming compose on top; that composition is
  argued, not machine-checked.

The scholar's refutation stands: no statistical whole-ciphertext privacy, because c1 needs RLWE. What is new is a
complete computational simulator with every premise built: a pinned a_j, a bounded input, and an extractable s_j.

**Executed** (`run_keygen_ceremony.py`; Mac N = 256, dregg-forge N = 8192 and 16384; all 18 rows as expected):

| run | ceremony (3 keys, proofs) | MPC d = 64 step (HE matvec + outer) on ceremony keys | returns | realized ‖shift‖∞ vs envelope (log2: forward, transpose, outer) |
|---|---:|---|---:|---|
| N = 8192, three primes, F = 2^118 | 41 s; key proof 7.84 Mbit | refines `step_spec`; 114 s | 42 = formula | 69.7 ≤ 75.1, 69.6 ≤ 75.1, 66.7 ≤ 69.1 |
| N = 16384, four primes, F = 2^175 | 84 s; key proof 10.06 Mbit | refines `step_spec`; 455 s | 42 = formula | 69.7 ≤ 75.1, 69.6 ≤ 75.1, 66.7 ≤ 69.1 |

On every return the simulator's output decrypts to the same y, with phase within the flood of Encode(y). The
realized shifts sit 2^2.4 to 2^5.4 below the envelopes the distance bound uses, so the bound is conservative and
measured, not assumed. The simulator is tested for functional agreement only: no test can show computational
indistinguishability, and the H2 step is an assumption.

### 21.3 Distances (per step and over 10^6 steps)

The statistical term is Σ over returns of N·B/(2F+1), in log2. The computational term is (returns) × Adv_RLWE.

| N / L | F | d | decrypt margin (bits) | statistical, per step | over 10^6 steps | RLWE samples per step |
|---|---|---:|---:|---:|---:|---:|
| 8192 / 3 | 2^118 | 64 | 3.0 | 2^-26.71 | 2^-6.78 | 42 |
| 8192 / 3 | 2^118 | 1024 | 3.0 | 2^-18.71 | 1 (vacuous) | 3,264 |
| 8192 / 3 | 2^118 | 4096 | 3.0 | 2^-14.71 | 1 (vacuous) | 49,920 |
| 8192 / 3 | 2^120 (largest that decrypts) | 4096 | 1.0 | 2^-16.71 | 1 (vacuous) | 49,920 |
| 16384 / 4 | 2^165 (scholar) | 64 | 17.0 | 2^-72.71 | 2^-52.78 | 42 |
| 16384 / 4 | 2^165 | 1024 | 17.0 | 2^-64.71 | 2^-44.78 | 1,680 |
| 16384 / 4 | 2^165 | 4096 | 17.0 | 2^-60.71 | 2^-40.78 | 25,152 |
| **16384 / 4** | **2^175 (executed)** | 64 | 7.0 | 2^-82.71 | 2^-62.78 | 42 |
| **16384 / 4** | **2^175** | 1024 | 7.0 | 2^-74.71 | 2^-54.78 | 1,680 |
| **16384 / 4** | **2^175** | **4096** | 7.0 | **2^-70.71** | **2^-50.78** | 25,152 |

The returns now include the HE outer product's value and MAC returns (49,152 of the 49,920 at N = 8192, d = 4096);
the scholar's table counted matvec returns only. Their envelope is small, so the statistical term moves by under
0.1 bit.

**What this says.**
- **N = 8192 with three primes cannot reach a million-step bound** at any flood that still decrypts.
- **N = 16384 with four primes and F = 2^175**, executed at d = 64 and with 7 bits of decryption margin, gives
  **2^-70.7 per step and 2^-50.8 over 10^6 steps, statistically, at d = 4096**.
- Add (25,152 × 10^6 ≈ 2^34.5) × Adv_RLWE for the computational part; at 128-bit RLWE that is about 2^-93.5.
- The SPDZ truncation masking (KAPPA = 40), the ZK proofs' simulators and the MAC/abort leakage are separate terms,
  not included here (scholar's OPEN list).

**Unbuilt in item 3:**
- a lattice-estimator run for these exact RLWE distributions;
- a delay function or threshold reveal against selective abort;
- the joint-key (FHE (b)) variant of the ceremony as code. It is described above; only the per-custodian keys are
  executed.


## 22. Gen 4, item 4: the fork verdict restated, with everything built (2026-11-06)

Root decisions applied first (reversible by ember):
- **HE parameters by profile.** `proofwire.PROFILES[...]["HE"]`: the ledger profile runs the HE helpers at
  **N = 16384, four 61-bit primes, F = 2^175**; the demo profile at N = 8192, three primes, F = 2^118. The HE set is
  in the genesis record with the proof parameters.
- **Selective abort.** Accepted for 3-of-3 custody as a named ledger term, ε_abort = (k+1)·p for k recorded aborts.
  The threshold-reveal alternative is designed in one page, `notes/dark-learning-gen4/threshold-reveal.md`, and not
  built.
- **Lattice estimator** (malb/lattice-estimator d8576372 under Sage from conda-forge, dregg-forge,
  `rlwe_estimate.py`): the exact RLWE instances, ternary secret, uniform [−8, 8] error, one ring sample per secret
  (the registered key, and each return's a_j u + e1).

| parameter set | log2 Q | rough (core-SVP, 0.292β) | full estimate, cheapest attack |
|---|---:|---:|---:|
| **ledger: N = 16384, four primes** | 244.0 | **2^213.2** (dual hybrid) | **2^240.6** (BDD) |
| demo: N = 8192, three primes | 183.0 | **2^122.4** (dual hybrid) | 2^152.2 (BDD) |

[MEASURED, classical cost models of the estimator; no quantum model was run]
- **The deployed set clears 128 bits by a wide margin.** It is the same instance in the H2 hybrid, so Adv_RLWE ≤
  2^-128 is conservative, and §21's computational term (2^34.5 × Adv_RLWE over 10^6 steps) is below 2^-93.5.
- **⚠ The demo set's core-SVP estimate is 2^122.4, under 128.** The HE Standard's table (log q ≤ 202 at N = 8192)
  assumes its own error and secret model; under the stricter core-SVP model our instance falls short. One more reason
  the demo profile is demo-only.

### 22.1 Per step at d = 4096, the deployed profile (bits)

| | MPC: HE matvec + HE outer | FHE (b) |
|---|---:|---:|
| MASCOT preprocessing (scholar's model, §15) | 0.912 T | 0.908 T |
| online wire | **0.214 T** HE (N = 16384; was 0.155 T at N = 8192) + 0.008 T SPDZ | 0.006 T (N = 8192 model) |
| **total, comparable rows** | **≈ 1.13 T** | **0.914 T** (not re-costed at a privacy-correct point) |
| ZKPoPK, built (§20), T = 309, delivered | 1.42 G | 1.23 G (masks, N = 16384) |
| integrity proof | spine 1.19 G + middle 0.70 G = **1.89 G**, built, T = 309 | ct×ct + relinearization certificates ≥ 1.26 T, **MODEL** |
| key setup | ceremony, built: 3 × 10.1 Mbit per epoch | joint-key ceremony, designed (§21), not built |
| privacy of the HE returns | built and measured: 2^-70.7 per step, 2^-50.8 over 10^6 steps (statistical) + 2^34.5 × Adv_RLWE (§21) | host returns owe the same argument; not built |
| evaluation objects outside custody | none | a relinearization key on the host |

The HE wire at N = 16384 grows only ×1.38, not ×2.2: with d_r = 256 each call sends half as many ciphertexts.

### 22.2 Verdict

**Build the MPC fork (SPDZ custody, HE matvec + HE outer, collaborative ZK proof).** With every piece measured, it
costs about ×1.24 FHE (b)'s modelled total. That gap is no longer what decides; three things do:
1. **Everything MPC needs is built and runs at the deployed parameters**, except MASCOT, which is a count model in
   both forks. FHE (b)'s two load-bearing pieces, relinearization and its certificate, are still a MODEL, so its
   0.914 T is a floor that has not been executed.
2. **The integrity proof is about ×670 smaller** (1.89 G against ≥ 1.26 T).
3. **Custody:** MPC hands no evaluation key to anyone. FHE (b) puts a relinearization key on the host.

The ZKPoPK no longer separates them (§20). FHE (b) stays parked, not refuted. It becomes a candidate again if
relinearization with its certificate is built and costs under about 0.2 T per step at N = 16384.

### 22.3 What remains unbuilt, in order of what it could change

| unbuilt | fork | could it change the verdict? |
|---|---|---|
| a real MASCOT/OT preprocessing backend (0.91 T is the scholar's count model) | both | only if it diverges between forks; it is the same object in both |
| relinearization and its certificate | FHE (b) | yes, the only route back to FHE (b) |
| SPDZ truncation masking (KAPPA = 40), MAC and abort leakage as terms in the million-step budget | MPC | no, but the 2^-50.8 claim excludes them, so they must be added before a whole-run privacy claim |
| handover proof that a rotated committee commits the same weights | MPC | no |
| threshold reveal / delay function against selective abort | both | no (named budget term) |
| QROM or knowledge-soundness proofs for the Fiat–Shamir Ligero proofs; composition of the simulators | both | no, but the security claims rest on arguments, not machine-checked proofs |
| a native prover (Python today: 417 s for one d = 4096 call's ZKPoPK) | both | no |
| field-extension MACs for a million-step budget | MPC | no |


## 23. Gen 5: the MPC fork as a native system; real preprocessing; the whole-run privacy budget; the handover proof (2026-11-07)

Root decisions in force: build the MPC fork; ledger profile T = 309, HE at N = 16384, four primes, F = 2^175; demo
profile T = 97, N = 8192, three primes, under-strength; selective abort as the named (k+1)·p term.
Code: `native/` (Rust workspace; `native/README.md`). Lane notes: `notes/dark-learning-gen5/`.

### 23.1 The native step (`native/darkstep`), bit-exact with the harness

Three custodians, each its own rayon pool and process (or thread), over a full TCP mesh with per-stream bounded
queues (`net.rs`). Each runs the SPDZ online phase from its own tape (`party.rs`), the HE matvec and HE outer product
from its own seat over BFV in RNS/NTT (`he.rs`, `bfv.rs`, `rns.rs`), and the MAC check. `darkstep deal` writes the
ideal dealer's tapes; `darkstep party I ...` runs one custodian; `darkstep local` runs all three in one process.

- **The reference.** `native_ref.py` runs the harness step with seeded keys and `per_return_rng=True` (new in
  he_matvec/he_outer, default off; each HE return draws from its own stream keyed by (seed, call, returner, recipient,
  block), the only mode a distributed custodian can run). `pycompat` reproduces CPython's `random.Random` and `repr`
  hashing bit for bit.
- **Equality** [EXECUTED, `cargo test -p darkstep --test vs_reference`]: the public transcript, every custodian's final
  authenticated shares and MAC-check sigma, and the SPDZ wire counts equal the harness's at d = 8 and 64 (N = 4096),
  d = 64 demo (N = 8192) and **d = 64 ledger (N = 16384, L = 4, F = 2^175)**; transcript files byte-identical (13,963
  entries). Three separate processes give the same digests. Negative controls: a shifted matvec or outer return is
  refused by the same Freivalds check as in the harness.

| d = 64 | Python | native (Mac) |
|---|---:|---:|
| N = 4096 | 145 s | 0.19 s |
| demo, N = 8192 | 420 s | 0.26 s |
| ledger, N = 16384 | 1,706 s (loaded) | 0.67 s |

**d = 4096, ledger profile, dregg-forge (16 vCPU, shared with other lanes, load 5-17)** [EXECUTED]: ACCEPT, refines
step_spec (weights in [-1, 1] above d = 256 so u1 stays in the table's domain, which step_spec asserts).

| phase | seconds |
|---|---:|
| owner input (2d² + 2d values) | 0.65 |
| three HE matvecs | 11.0 |
| truncations, lookups, products | 0.3 |
| two HE outer products | 36.7 |
| MAC check | 1.2 |
| **online step** | **49.9** (54.4 wall; ideal dealer 4.4 s) |

HE wire 28.1 GB per step over loopback (the count model's 0.214 Tbit, plus framing). Kernel costs at N = 16384, L = 4
(Mac): a return 7-13 ms (flood draws 1.4 ms of it, inherent to the bit-exact MT stream), a decryption 2-3 ms.

### 23.2 Real preprocessing (`native/darkprep`; `notes/dark-learning-gen5/preprocessing.md`)

MP-SPDZ v0.4.4 MASCOT (BSD-3 + Bristol's usage-report licence; a research implementation, no security review; no
audited library does prime-field SPDZ preprocessing), three processes on 127.0.0.1, exported as darkstep tapes. Both
darkstep and the harness (`tape_dealer.py`) run unchanged on them and refine step_spec; a flipped MAC share or `trh`
share aborts the MAC check in both. Measured against the scholar's model, all of d = 4096 run:

| d | measured | model | ratio |
|---:|---:|---:|---:|
| 64 | 8.69 Gbit | 12.87 Gbit | 0.675 |
| 4096 | 0.599 Tbit (40.9 s, 4 threads per party) | 0.912 Tbit | 0.657 |

The gap is MP-SPDZ's tau = 3 and 64-bit OT messages; tau = 4 measures 0.709 Tbit (0.78 of the model).

### 23.3 The native ZKPoPK (`native/dzkpopk`; `notes/dark-learning-gen5/zkpopk.md`)

Bit-exact proofs (sha256-identical, both ways cross-verified, flip refused) at N = 16 and on the deployed ring
(N = 16384, four primes, T = 309); all 31 attack rows refused with the harness's reasons. The d = 4096 forward batch:
**417 s / 217 s (Python) → 2.59 s / 0.92 s** (N = 8192); 4.84 s / 1.85 s at N = 16384. Per custodian per d = 4096 step
about 21 s to prove and 16 s to verify. Gating darkstep's HE calls on it is in progress.

### 23.4 The collaborative proof and verifier (`native/darkproof`; in progress)

cozk, the ZK spine, the ZK middle, the proofwire codec, verifier, ledger and owner signature are ported and
byte-identical at d = 4 and 16 (demo); every run_proofwire, signed-input and §16 forgery row is reproduced natively.
**Gap found:** the verifier replays `mpc_fork.run_step` with the PLAIN SPDZ matvec/outer, so no harness path proves the
deployed HE step. Decision (root): the middle binds the HE helpers' openings through the public digest and leaves
matvec/outer correctness to the spine's sumchecks and rank-1 checks; the proof lane writes that reference next.
darkstep now emits the proof's per-party record and can deal the middle's truncation range bits.

### 23.5 The whole-run privacy budget (`privacy_budget.py`)

Every term, d = 4096, 10^6 steps, ledger HE (log2 of the union bound):

| configuration | HE stat | trunc | MAC | prep | **total** |
|---|---:|---:|---:|---:|---:|
| ideal dealer, as built (KAPPA = 40, F_p MACs) | -50.8 | **-6.1** | -40.1 | — | **-6.1** |
| MASCOT tau = 3 (as released), as built | -50.8 | -6.1 | -40.1 | 0 (combine) | **0 (vacuous)** |
| MASCOT tau = 4, as built | -50.8 | -6.1 | -40.1 | -18.1 (auth) | -6.1 |
| MASCOT tau = 4, exact truncation | -50.8 | — | -40.1 | -18.1 | -17.4 |
| **MASCOT tau = 5, exact truncation, F_p² checks** | -50.8 | — | -101.1 | -50.5 (combine) | **-49.6** |

- **Truncation masking dominates and the field cannot fix it.** The step opens c = x + 2^K + r with r < 2^(K+40);
  SD < 2^-40 per truncation, 4d = 2^14 per step. In a 61-bit field c < p caps KAPPA at 47 (2^-13 per run). Exact
  truncation (r uniform in F_p, a comparison circuit) removes the term; the preprocessing lane estimates about
  +0.5 Tbit per step at d = 4096.
- **MAC, sacrifice, authentication and owner-check terms** are integrity terms (the collaborative proof also covers
  integrity under full collusion) counted here because a passing forgery is what lets an abort depend on secrets. In
  F_p they cost 2^-18 to 2^-40 per run; F_p² checks (not in MP-SPDZ for prime fields) cut them below 2^-77.
- **MASCOT's combine at tau = 3 is vacuous in a 61-bit field** (2^-30.5 per triple); tau = 5 gives 2^-91.5 per triple.
- Zero terms: input masks, auth_plain, lookup and Beaver openings, the outer commitments, the proofs within two lives.

### 23.6 The handover proof (`handover.py`, `run_handover.py`; spec: Veil `CustodyHandover.lean`)

Resharing as the Veil model (each old custodian splits its share into subshares for the new ones and erases; the new
committee re-authenticates under its own MAC key). The proof: the old committee's commitment (the ledger head) and the
new committee's are evaluated at one Fiat-Shamir point inside a collaborative ZK Ligero among all six custodians, with
hidden rows u_old (old shares only) and u_new (new shares only), evaluation consistency at both commitments' opened
columns, and <u_old - u_new, b(r)> = 0 (Schwartz-Zippel, 2 log2(d)/p). No evaluation is revealed. Under the
both-periods rule each hidden row keeps one honest share. **Two lives suffice:** the old child is opened by its step
and the handover and never again as a parent; the new commitment by the handover and the next step.
`Ledger.rotate` now refuses a rotation without a verified handover proof.

[EXECUTED, d = 4, demo; all 13 rows as expected]: old step 1 ACCEPT → honest handover ACCEPT → new committee's step 2,
chained to the handover's roots, ACCEPT; REFUSED: a commitment of shifted weights, a resharing whose subshares do not
sum to the old shares (both: Ligero linear test), the honest proof recorded with other new roots, the proof for
another custodian set, no proof, a tampered proof, the proof replayed into the next epoch, a third opening of the old
child (life counter), and the old committee's step 2 after rotation (parent mismatch). Native verifier: in progress.

### 23.7 Decisions for ember

1. **Exact truncation** (r uniform in F_p, comparison circuit; about +0.5 Tbit/step of preprocessing) to remove the
   dominant privacy term, or accept a run bound of about 2^-6 (2^-13 at KAPPA = 47)?
2. **Preprocessing configuration:** tau = 5 (tau = 3 as released is vacuous here), TLS (+35% wall), and F_p² sacrifice
   and MAC checks, which MP-SPDZ lacks for prime fields (our own code, or a larger field)?
3. **MP-SPDZ's status:** accept an unreviewed research implementation and Bristol's usage-report request?
