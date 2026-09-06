# Pre-constrained encryption, read against the protected-process target (2026-09-06)

**Question grounded.** An external handoff proposes "Route 1: pre-constrained encryption" for a
protected process `learn(state, obs) → state'`, `infer(state, q) → (state', answer)` with NO
master-read capability — not a key custodians agree not to use, but the absence of any credential
that opens the state. Sources read in full where they exist: Agrawal–Kumari–Nishimaki, *Don't Trust
Setup! New Directions in Pre-Constrained Cryptography*, eprint 2024/1294 rev. 2026-02-05
(`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2024/1294.pdf`; pages cited are the PDF's printed ones) and
Ananth–Jain–Jin–Malavolta, *Pre-Constrained Encryption*, ITCS 2022, LIPIcs 215 art. 4, pp. 4:1–4:20
(**not on eprint** — see §6; read from the CC-BY DROPS copy, cited as `4:n`; it defers every
construction and proof to a "full version" I did not locate). Pillar served: `docs/DARK-TRAINING.md`.
Leakage tiers per `minidregg/docs/FORMAL_STATUS_AND_NEXT_PROOFS.md` row "Private turns, sealed escrow,
BFV, and note spend" (Clear / Shielded / Dark; "A Dark system is a later, strictly stronger deliverable").

**Headline [DERIVED].** Pre-constrained encryption is "privately answer a permitted question," one
hop: a party holding the secret *in plaintext* encrypts, and the authority's key opens exactly
`f(x)`. Neither paper has a configuration in which an *encrypted* state is held by a party with no
key and then advanced. The standard-assumption scheme (2024/1294's sPCE) fixes every function at
setup, so `obs` cannot enter and the chain dies at hop two; the delegating scheme (ITCS'22) can
express the loop syntactically, but its security game is silent on it, and the paper proves that the
constraint class needed is iO-strength — and shows (4:11) that "ciphertext of the state + constrained
master key" *is* an obfuscated program. So Route 1 with closure collapses into the obfuscation route.
The handoff's warning about an existential extractor is confirmed verbatim in both papers (§2).
For our tree: `DARK-TRAINING.md §6` holds tier-C custody (a quorum that *can* read, in shares), not
credential absence; §5 gives the Prop that says which one we have.

## 1. Syntax and games, copied

### 1a. ITCS'22 — PCE with delegation [READ]

**Syntax (4:12, §4.1).** For constraint family 𝒞 and function family ℱ: `Setup(1^λ, C) → (MSK[C], PK)`;
`KeyGen(MSK[C], f) → sk_f` "when f satisfies the predicate, i.e., C(f) = 1" else ⊥; `Enc(PK, x) → CT`
"(when the public key is 'well formed') or ⊥"; `Dec(sk_f, CT) → y` with correctness `y = f(x)`.
Remark 1 (4:12): delegation is built into the definitions; "it is easy to adapt our definitions to
exclude the key delegation feature." **Fixed before data arrives:** `C` (and `PK`, `MSK[C]`). Functions
`f` are chosen *after* data, subject to `C(f) = 1` — that is the delegation feature.

**What "constrained setup" restricts (4:3):** "even the authority can only compute f(x) for all
functions f s.t. C(f) = 1, and nothing else." Contrast with FE (4:5–4:6): FE/ABE/IBE are
"post-constrained … such systems do not provide any security whatsoever against the setup authority
unless one considers unrealistic models where the authority simply 'forgets' the master secret key and
the randomness used for setup" — fn 3: "this is not even compliant with semi-honest security."

**Games (4:13–4:14).**
- Def 2 *SH-SAA*: for any `C ∈ 𝒞` and `x_0, x_1` with `f(x_0) = f(x_1)` for all `f` with `C(f) = 1`:
  `Pr[r ← {0,1}^poly; (PK, MSK[C]) ← Setup(1^λ, C; r); b ← {0,1} : A(1^λ, r, Enc(PK, x_b)) = b] < ½ + negl`.
  The adversary receives the setup randomness `r` (hence `MSK[C]`).
- Def 3 *SM-SAA*: `(PK, C, r, x_0, x_1) ← A`; output valid iff `C ∈ 𝒞`, `PK = Setup(1^λ, C; r).PK`, and
  `f(x_0) = f(x_1)` for all authorized `f`.
- Def 4 *M-SAA*: "there exists a (possibly inefficient) extractor algorithm Ext such that for any
  non-uniform (stateful) PPT adversary A … `(PK, x_0, x_1) ← A(1^λ)`. `CT ← Enc(PK, x_b)`. … Output b′ if:
  `C ∈ 𝒞`, where `C ← Ext(1^λ, PK)`. `|x_0| = |x_1|`, and for all `f ∈ ℱ` satisfying `C(f) = 1`, it holds
  that `f(x_0) = f(x_1)`. Else, output 1."
- Def 5 *Constraint hiding*: `PK` for `C_0` vs `C_1` (same length, `C_0(f_i) = C_1(f_i)` on all key
  queries) indistinguishable given a KeyGen oracle.
- Def 6 *Collusion resistance* (FE-style); Lemma 8 (4:15): SH-SAA + constraint hiding ⟹ bounded CR.

**Results (4:4–4:5, 4:17) [READ].** AB-PCE for point constraints from LWE (BGG+14 punctured proof);
IB-PCE for general constraints from LWE (re-purposing [6] = eprint 2021/431's "attribute-based secure
functional evaluation with public reconstruction"); AB-PCE for general constraints from WE + perfectly
sound NIZK; PCE for general constraints from iO + NIZK. Lower bounds: AB-PCE(general) ⟹ WE for NP;
PCE(general) ⟹ iO for P/poly, semi-honest SAA suffices, no sub-exponential loss (4:5, 4:11).
Semi-malicious → malicious (4:10, §5): two PKs + NIWI "that either of them is well-formed" + 2-server
HSS shares of the message; for general PCE the HSS needs perfect correctness, "from sub-exponentially
secure iO" (4:4). Semi-malicious LWE constructions need `A` from "a structured distribution (which is
guaranteed to have no trapdoor)" because a trapdoored `A` "is not even detectable, since the two
distributions are statistically close" (4:8).

**The NISC statement (4:5), copied:** "PCE is related to the notion of non-interactive secure
computation (NISC) [35]. For constraint families 𝒞 where a constraint C ∈ 𝒞 authorizes a single
function f ∈ ℱ, PCE with SH-SAA security can be obtained from NISC. Unlike NISC, however, PCE can also
support constraint families where a constraint can authorize a large (potentially exponential-sized)
class of functions. In this sense, PCE is stronger than NISC."

### 1b. 2024/1294 — static PCE (sPCE) [READ]

**Syntax (p15–16, §3.1).** `Setup(1^λ, {f_1,…,f_Q}) → (pk, sk_{f_1},…,sk_{f_Q})`; `Enc(pk, x) → ct`;
`Dec(sk, ct) → y`; correctness `Dec(sk_{f_i}, Enc(pk, x)) = f_i(x)`. **Fixed before data arrives: the
whole function list.** "our sPCE does not have a delegation mechanism. Although we can generate
functional decryption keys, all functions are fixed at the setup phase" (p15).

**"Static" and the exact difference from ITCS'22 (p3):** "a weaker variant of PCE which removes the
dynamic key delegation functionality required by their definition and where the constraint acts on the
data rather than on the keys … a PKE scheme where a constraint C is embedded in the secret key created
during setup, the encryptor computes a ciphertext for any message x and decryption succeeds to recover
C(x) … these functions are now fixed and provided to setup, without allowing dynamic choice during key
generation." Why: to "sidestep the lower bound by Ananth et al." (abstract). The 2PC reading (p4): "PCE
can be seen as a special case of reusable 2PC by collapsing the setup and decrypt algorithms of PCE into
the same (first) party with input C and by considering encrypt as the second party with input x."

**Games (p16–17, p23).**
- Def 3.2 *Function-hiding*: `pk` for `{f_i^0}` vs `{f_i^1}`.
- Def 3.3 *SIM vs semi-malicious authority*: A outputs `{f_i}` and setup randomness `r`; challenger
  runs `Setup(…; r)`; then `Enc(pk, x)` vs `SIM(pk, 1^{|x|}, {f_i(x)})`. Def 3.4 relaxed-SIM: SIM also
  sees `{f_i, sk_{f_i}}`.
- Def 3.5 *SIM vs malicious authority*: "A outputs a public key pk and an input x. … If β = 1, it
  computes ct_1 ← Sim(pk, 1^{|x|}, f_1(x), …, f_Q(x)), where (f_1, …, f_Q) ← Ext(1^λ, pk). Here Ext is
  an extractor algorithm." Security: "there exists a PPT simulator Sim and an admissible (possibly
  inefficient) extractor Ext". Admissible = on *honestly generated* `pk` Ext returns the real list.
- Def 3.6 unconditional (unbounded A). Def 3.19 IND flavour: admissible iff `f_i(x_0) = f_i(x_1)` for
  the *extracted* `f_i`.

**Assumptions [READ].** Thm 3.15 (p21): general circuits, malicious authority, from DDH / (QR ∧ DCR)
/ LWE / (LPN ∧ NW-derandomization), via two-message statistically-sender-private OT + Yao. Thm 3.16:
unconditional for NC¹. Thm 3.18 (p22): **unconditional against a malicious authority for general
circuits from polynomially-hard LWE**, via maliciously circuit-private FHE (OPP14 + BD18 + GSW13,
Thm 2.21 p15). Thm 3.21 (p23): laconic pk (sublinear in Q or in function size) against a malicious
authority is impossible — Ext would decompress `Q·λ` random bits from an `O(Q^{1−γ})`-bit pk. Lemma
3.20: sPCE with succinct *ciphertexts* ⟹ iO. Laconic sPCE exists semi-maliciously from LWE in the ROM
(Thm 3.32, p35, via hash encryption + RDMPC + a maliciously circuit-private FHE lift, Thm 3.29).

## 2. Credential inventory [DERIVED]

| scheme | artifact | holder | survives setup? | derives |
|---|---|---|---|---|
| 1294 §3.2 OT+GC (p18) | `pk = {ot_{1,i}}` | public | yes | nothing (receiver privacy) |
| | `sk_f = {f[i], st_i}` (OT receiver state) | authority | yes | `lb_{i,f[i]}` from any ct ⟹ `f(x)`, statistically nothing else even for malformed pk (Thm 3.12) |
| | setup coins | authority | = `st_i` | same as `sk_f` |
| | Enc coins (garbling + OT sender) | encryptor, one-shot | must not | **all labels ⟹ `U[x]` on every `f`** — a read-all of `x`'s function table |
| 1294 §3.3 FHE (p22) | `pk = (FHE.pk, FHE.ct_f)` | public | yes | nothing |
| | `sk = FHE.sk` | authority | yes | **decrypts every ciphertext under `FHE.pk`**; the secret is safe only because it is never encrypted under `FHE.pk` — it is hard-wired in `G[x]` and `Eval`'s output is ≈ₛ `Sim(f(x))` (Def 2.18) |
| | Eval re-randomization coins | encryptor | must not | de-randomizes the circuit-privacy simulation |
| 1294 §3.5–3.7 laconic (p24–25, 35) | `pk = (r, h_str)`, `HE.key = H(PRG(r))` | public | yes | nothing; the HE "has a random matrix as its public key and does not have any master secret" (p8) |
| | `sk_{f_i} = (i, Δ^{(i)}, f̂_i)` | authority | yes | its share of labels ⟹ `f_i(x)`; semi-malicious only (Thm 3.21) |
| | §3.6 lift adds `FHE.sk` to every `sk_{f_i}` | authority | yes | opens `FHE.ct = Enc(SFE.pk)`; same "never encrypt the secret under it" discipline |
| ITCS IB/AB-PCE from LWE (4:8–4:9) | `PK_C = (A, {A_i = A·R_i − C_i·G})` | public | yes | nothing if `A` is trapdoor-free |
| | `MSK[C] = {R_i}` | authority | yes | trapdoor for `[A ∣ A_id]` iff `C(id) = 1` |
| | a trapdoor for `A` | *nobody, by distribution* | — | **read-all**; a semi-malicious authority could plant one undetectably (4:8) — hence the structured-`A` fix |
| ITCS AB-PCE from WE (4:9) | `PK = (c = Comm(C*; r), crs)` | public | yes | — |
| | `MSK[C] = (C*, r)` | authority | yes | NIZK proofs `π` = `sk_f` for `C*(f) = 1` only, **if the CRS is honestly generated** (fn 6) |
| | NIZK CRS trapdoor | authority in tier B | — | forge `sk_f` for unauthorized `f` — the reason §5's dual-PK + NIWI transform exists |
| ITCS malicious transform (4:10) | `(PK_0, PK_1)`, NIWI, `MSK_0, MSK_1` | authority | yes | at most one PK malformed ⟹ one HSS share hidden |

**The handoff's warning, tested.** Both games guarantee only that *some* constraint in the family is
embedded. ITCS 4:4: "Our formulation requires the existence of an inefficient 'constraint extractor'
and guarantees that the adversary embeds a constraint C from the constraint family 𝒞 in any
'well-formed' public key." 1294 p6: "We make this choice to separate the authentication of constraints
from the schemes." 1294 p41 (on PCGS vs Bartusek et al.): "their definition also includes the step of
authorizing the database while ours does not. We note that such an authorization can be performed via
a separate protocol (using zero-knowledge or multiparty computation protocols)." Nothing in either
paper lets a verifier check the *intended* constraint; constraint-hiding (ITCS Def 5, 1294 Def 3.2)
actively forbids reading it off `pk`. Sharper [DERIVED]: 1294's function family is general circuits and
its own applications use `U[C](x) = x if C(x) = 1` (p4); a malicious authority may run Setup on `f = id`
and Def 3.5 is satisfied vacuously (`Sim` receives `f(x) = x`). The malicious-authority game is a
statement about *the pk the authority actually made*, never about the policy anyone was promised.
The ITCS §5 NIWI proves "either PK_0 or PK_1 is well-formed" — membership in the family, not identity
of the constraint. Confirmed: an existential extractor is insufficient for the particular policy.

## 3. The closure question [DERIVED]

**sPCE (1294), one `learn` then one `infer`.** Roles are forced: the party with the secret is the
*encryptor*, who holds it in plaintext (`Enc(pk, x)` takes `x`; in §3.3 `x` is hard-wired into `G[x]`).
So the state must be `x`. Hop 1: `E_0` holds `(state_0, obs_0)` in the clear, sends
`ct_0 = Enc(pk, (state_0, obs_0))`; the authority computes `f(state_0, obs_0)`. To avoid revealing
`state_1 = learn(state_0, obs_0)`, set `f(x) = Enc(pk′, learn(x); r)` with `r` drawn from `x`; the
authority now holds `ct_1 = Enc(pk′, state_1)` and no plaintext. Hop 2: `learn(state_1, obs_1)` needs a
ciphertext of `(state_1, obs_1)`; sPCE has no algorithm that takes a ciphertext and a fresh input, and
`obs_1` cannot enter through the function side because "all functions are fixed at the setup phase"
(p15). The only way forward is a party holding `state_1` in plaintext running `Enc` — i.e. the holder
of `sk′`, a read credential. **Chain length is one.** `infer` is the same shape: `g_q(x) = (answer,
Enc(pk′, x))` reveals `answer` and re-encrypts, and the re-encryption cannot be continued. There is no
moment in sPCE at which an encrypted state sits with a keyless party. **The papers support "compute f
on a ciphertext and reveal f(x)", and only that.**

**PCE with delegation (ITCS'22).** Here the loop is *expressible*: `CT_t = Enc(PK, s_t)`; on `obs`, the
authority runs `KeyGen(MSK[C], f_obs)` with `f_obs(s) = Enc(PK, learn(s, obs); PRF_k(obs))` (`k` a
component of `s`), decrypts to `CT_{t+1} = Enc(PK, s_{t+1})`, and never sees `s_{t+1}`; `infer` likewise
with `g_q(s) = (infer_ans(s, q), Enc(PK, infer_st(s, q); PRF_k(q)))`. Who issues what: the authority
issues every key (from `MSK[C]`, which survives); every ciphertext after `CT_0` is produced *inside an
authorized function*, with randomness derived from the secret; the initializer of `CT_0` held `s_0` in
plaintext. Three things break: (i) **the security game is silent**: Defs 2–4 condition on
`f(x_0) = f(x_1)` for all authorized `f`, and `f_obs(x_0) ≠ f_obs(x_1)` for any `x_0 ≠ x_1`, so no
authorized pair is admissible; hiding `s_{t+1}` inside `CT_{t+1}` is a hop-`(t+1)` claim, the hybrid is
unbounded and circular, and the coins are secret-derived rather than fresh (the definitions encrypt with
fresh coins) — the self-re-encryption pattern whose known treatment is puncturable PRF + iO hybrids.
(ii) **The constraint is a general circuit**, and the paper proves PCE for general constraints ⟹ iO
(4:5, 4:11), with constructions from iO + NIZK. (iii) 4:11, copied: "we can obfuscate a circuit Γ by
computing (Enc(PK, Γ), MSK[C]), where the constraint C restricts the functions to be universal circuits
of the form U_x(Γ) = Γ(x)." So a state ciphertext plus the constrained master key *is* an obfuscated
program, and the closed loop is a self-re-obfuscating program: Route 1 with closure is the obfuscation
route with a different name. 1294 removed delegation precisely to escape this (p3) and shows even
succinct-ciphertext sPCE ⟹ iO (Lemma 3.20): every variant that could carry the loop is iO-strength,
and every standard-assumption variant cannot express it. **This is the finding.**

## 4. Threat tier [DERIVED]

- **A (honest init, then exposure).** Covered by SH-SAA (ITCS Def 2: the adversary receives `r`, hence
  `MSK[C]`) and 1294 Def 3.3 (adversary *chooses* `r`). No erasure is needed at the authority — that is
  the whole point (4:5–4:6: FE's "forgets the master secret key" is "not even compliant with semi-honest
  security"). Erasure IS needed at the encryptor: plaintext `x` and the one-shot Enc coins (garbling
  coins reveal every label; Eval coins break circuit privacy). For the protected process this is the
  initializer's `s_0` and its coins.
- **B (malicious setup authority).** Covered by M-SAA (ITCS Def 4; 1294 Defs 3.5/3.6), with the
  existential-extractor caveat of §2. Constructions: ITCS via §5 (proofs in the unlocated full version;
  general PCE needs perfect-correctness 2-server HSS "from sub-exponentially secure iO"); 1294 Thm 3.15
  (DDH/QR∧DCR/LWE/LPN) and Thm 3.18 (LWE, unconditional). Laconic pk impossible here (Thm 3.21). Tier B
  is exactly where a trapdoored `A` (4:8) or a trapdoored NIZK CRS (4:9 fn 6) becomes an undetectable
  read-all credential; the constructions are built to make such a credential non-existent by
  distribution, not to detect it.
- **C (threshold coalition).** Not modeled by either paper. ITCS 4:6 positions PCE *against* it:
  "Multi-authority models do not provide any security when all the authorities are dishonest while PCE
  aims for meaningful security even in 'full corruption' scenario." Tier C is subsumed by a single
  fully-corrupt authority; there is no t-of-n notion (grep `threshold` in both texts: 1294 only inside
  the RDMPC building block p11/p28; ITCS only in a reference title).
- **D (hardware).** Zero mentions (grep `hardware|enclave|TEE|SGX|trusted execution`: 0 and 0).

## 5. Bearing on our tree [INFERRED]

**§6 "custody is the part we already hold" — reclassify, don't delete.** What fhegg's threshold
ceremony holds is tier-C custody: no single party (host included) can read, and the FULL quorum is a
read-all credential held in shares. The tree already carries the witness, read the other way:
`/Users/ember/dev/breadstuffs-steplane/metatheory/Market/DarkBazaarCollectiveOpeningPoly.lean`'s
`collective_poly_decrypts` ("the REAL threshold.rs combine→decode path returns exactly each slot's
order code") *is* "the quorum reads." The IND-CPA-D hazard §6 names is the symptom: every quorum decrypt
is a read event with a budget; PCE's `Dec` leaks a fixed `f(x)` and has no per-decrypt budget. PCE's
tier-B property ("even full corruption learns only `f(x)`") is one we do not hold, and by §3 the
standard-assumption PCE cannot supply the learn-closure, so it is not a route to acquiring it.
Suggested edit to §6: keep "no single party — including the host — can read the weights"; add "the
quorum can, every threshold decrypt is a read, and this is tier-C custody, not credential absence;
credential absence with closure is iO-strength (notes/pre-constrained-encryption-read.md §3)."
Suggested §7 item 5: **state closure** — who holds the next state and under what credential — with
this note as the record; it is upstream of item 1 (iterative depth), because re-encryption "under a
threshold quorum between steps" (§4) is a quorum *read* of the state per refresh, which item 1's
low-rank route was meant to avoid and now must be priced as reads.

**The tree's real analogue of pre-constraining** is the escrow row's "Treat threshold release as a
distinct authorized effect" (`minidregg/Kernel/PrivateEscrowSettlement.lean`: `Settlement.intent` is
"a later, separately authorized mutation"). Make the release a typed effect whose statement is
`released = f(state)` for `f` in a Lean-owned constraint set, checked by the Shielded proof suite
*before* partial decryptions are combined. That is a policy-verified constraint — stronger than PCE's
existential extractor — but a custodian-agreement (tier C), and must be labeled so.

**The Lean-shaped Prop** (a provenance ledger; the crypto hiding stays class B as in `Bfv/Smudging.lean`):
```lean
structure Custody (Party Artifact : Type) where
  holds     : Party → Finset Artifact          -- what each party keeps after setup and after each hop
  derives   : Finset Artifact → Finset Artifact -- model closure: monotone, idempotent (the combine/decrypt algebra)
  opensState : Artifact → Prop                  -- plaintext of the state, or a key for its ciphertext
def NoSurvivingReadAll (c : Custody P A) (coalition : Finset P) : Prop :=
  ∀ a ∈ c.derives (coalition.biUnion c.holds), ¬ c.opensState a
-- tree-honest pair for the deployed threshold design:
theorem below_t_blind  (h : coalition.card < t) : NoSurvivingReadAll fheggCustody coalition   -- witness
theorem full_quorum_reads : ¬ NoSurvivingReadAll fheggCustody Finset.univ                   -- falsifier
```
The falsifier's derivation chain is `collective_poly_decrypts`; `below_t_blind`'s combinatorial half is
`short_quorum_breaks_opening` (a correctness refusal today, not hiding — hiding needs the RLWE side).
"No master-read capability anywhere" is exactly `NoSurvivingReadAll c Finset.univ`, which is FALSE for
every threshold design and, per §3, has no standard-assumption witness with closure. Carrying the pair
lets minidregg state which one it has instead of the slogan.

## 6. Absence claims, unverified reductions, instruments

- **ITCS'22 is not in the eprint mirror.** Corpus: `IACR-eprint-mirror/{2020,2021,2022,2023}` (1593 +
  1673 + 1745 + 1946 PDFs, mirror HEAD 6cb6c3ec 2026-09-04). Instrument: `pdftotext -l 1` (2021, 2022)
  then `-l 2` (2020, 2021, 2023) piped to `grep -iE 'pre-?constrained|Malavolta.*Jin|Jin.*Malavolta'`;
  sanity: 6 hits on `2024/1294.pdf` p1. Hits were only AJJM's other papers (2020/180 multi-key FHE,
  2021/431 unbounded MPC = ITCS ref [6]) and two zap papers. 1294's bibliography cites the LIPIcs venue
  only. Kagi (2 of 8 spent; one call was a malformed GET that errored) returns DROPS and NSF-PAR copies,
  no eprint id. The ITCS "full version" (constructions, §5 transform, all proofs) was not located.
- **No prior note in the tree** mentions pre-constrained encryption: `grep -ril 'pre-?constrained'
  notes/ docs/ forcodex/ SLVG_THOUGHT.md` → only this file. The task's `LANE-PREAMBLE.md` is absent from
  the scratchpad and the repo (`find -iname '*PREAMBLE*'`); rules followed as restated in the task.
- **Read but not checked line by line:** 1294 Thm 3.12 (two hybrids, SSP-OT + GC.Sim — read, plausible),
  Thm 3.17 (one hybrid via Def 2.18 — read), Thm 3.21 (Kolmogorov — read). **Not read:** 1294 §3.5.2 and
  §3.6 security proofs (Thms 3.23, 3.28, 3.29), §4 PCIO beyond the overview, §5's proofs (5.27/5.28 are
  "identical to [BGJP23]" and omitted by the paper). ITCS: every proof is deferred; the LWE IB-PCE and
  the §5 transform are read from the overview (4:7–4:11) only. The `f = id` vacuity in §2 is my
  derivation from the stated family, not a claim the papers make.
- Kagi total: 2. No commits, no edits outside this file.
