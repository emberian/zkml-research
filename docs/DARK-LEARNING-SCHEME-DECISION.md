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
bits. **The deployed proof layout (all residues bridged into one 31-bit field) is the wrong layout for
any ct×ct at N = 8192.** At N = 8192, digits of more than 5 bits cannot be summed in BabyBear, and every
cross-prime fact becomes integer emulation.

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
- **Why dishonest-majority.** Confidentiality and integrity then fail only if ALL n custodians collude.
  That is the same tier C as n-of-n threshold FHE, and stronger than honest-majority replicated sharing.
- **Preprocessing.** OT-based (MASCOT-class over lattice OT) to keep FHE out of the trust base, or
  LWE-HE-based (LowGear-class), which is where the FHE fork's BFV could supply triples. Both are PQ.
- **Rejected:**
  - Honest-majority 3PC: one corruption already breaks it, and its speed is not the binding constraint
    at d = 64.
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
