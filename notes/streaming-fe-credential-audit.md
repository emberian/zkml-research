# Streaming FE — the stream writer's state is a read-all credential (audit of the external handoff)

**2026-09-06. Audit lane against `docs/DARK-TRAINING.md` (the host is the adversary; weights never readable by the substrate).**
Sources read, all as extracted text (`pdftotext -layout`, scratchpad `sfe/`): the Korb dissertation *Streaming Functional
Encryption* (UCLA 2026-06-12, escholarship `qt8j13s3tb`, 189 PDF pages — fetched ONCE, HTTP 200, 4.27 MB), and from
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/`: `2022/1599.pdf` (GKS23), `2024/1213.pdf` (BKS25), `2024/355.pdf` (DGKS24),
`2025/330.pdf` (DGKS25). Page numbers are the printed folios; PDF page = printed + 13 in the dissertation (checked at the
figure: printed 94 ↔ PDF 107). Tags: [READ] = copied from the page named; [DERIVED] = mine, from the copied algorithms.

**Headline.** The handoff is right, and its page citation is exact. It is also *conservative*: the paper's own footnote says the
encryption state "must be kept secret" only to stop *mix-and-match* (learning `f` on interpolated streams); in the construction
the state holds `FPFE.msk`, a master secret of a secret-key FE, and its exposure recovers **every element of the stream, past and
future, with no function key at all** — in the bounded-collusion variant in one line, with no inner setup. This is not a break of
any theorem in the four papers (the challenger never hands out `Enc.st`); it is a deployment mismatch — but a structural one: in
these constructions **the capability to append to a stream is the capability to read all of it**, and the syntax gives the writer
no way to ratchet. For DARK-TRAINING that is fatal in the plain deployment, because the initial weights have nowhere to hide but
the stream (§5).

## 1. The construction, copied [READ]

**Where.** Dissertation Ch. 3 "Bootstrapping to a Public-Key Streaming FE Scheme", §3.2 *Construction*, printed pp. 88–96; the
algorithms are on pp. 93–96 (PDF 106–109); **Figure 3.2 (`H_{i,x_i,t_i}`) is on printed p. 94 = PDF p. 107**, Figure 3.3
(`G_{f,s,c}`) on p. 95. It is GKS23 §6.2 (2022/1599 pp. 57–58, Figs 8–9) verbatim up to renaming (`PRF→PRF1`, `Sym→SKE`), and
DGKS24 §7.2 (2024/355 p. 86) says of itself "identical to [GKS23]". Tools (p. 90): `One-sFE` (single-key single-ciphertext
secret-key sFE), `PRF1`, `PRF2`, `SKE`, `FPFE` (function-private secret-key FE), `FE` (public-key FE).

```
sFE.Setup(1^λ,1^ℓF,1^ℓS,1^ℓX,1^ℓY):  (FE.mpk, FE.msk) ← FE.Setup(1^λ);  MPK = FE.mpk, MSK = FE.msk.          [p. 93]
sFE.EncSetup(MPK):  PRF1.K ← PRF1.Setup(1^λ);  FPFE.msk ← FPFE.Setup(1^λ);                                       [p. 93–94]
                    FE.ct ← FE.Enc(FE.mpk, (FPFE.msk, PRF1.K, 0, 0^{ℓSKE.k}));   output Enc.ST = (FPFE.msk, FE.ct).
sFE.Enc(MPK, Enc.ST, i, x_i):  parse Enc.ST = (FPFE.msk, FE.ct);  t_i ← {0,1}^λ;  H_i := H_{i,x_i,t_i} (Fig. 3.2);   [p. 94]
                    FPFE.sk_{H_i} = FPFE.KeyGen(FPFE.msk, H_i);  i=1: CT_1 = (FE.ct, FPFE.sk_{H_1}); else CT_i = FPFE.sk_{H_i}.
Fig. 3.2  H_{i,x_i,t_i}(One-sFE.msk, One-sFE.Enc.st, PRF2.k, β):  if β=0: r_i ← PRF2.Eval(PRF2.k, t_i);            [p. 94]
                    output One-sFE.ct_i ← One-sFE.Enc(One-sFE.msk, One-sFE.Enc.st, i, x_i; r_i).  else ⊥.
sFE.KeyGen(MSK, f):  s ← {0,1}^λ;  c ← {0,1}^{ℓSKE.ct};  G := G_{f,s,c} (Fig. 3.3);  SK_f = FE.sk_G ← FE.KeyGen(FE.msk, G). [p. 94–95]
Fig. 3.3  G_{f,s,c}(FPFE.msk, PRF1.K, α, SKE.k):  if α=0:                                                          [p. 95]
                    (r_Setup, r_KeyGen, r_EncSetup, r_PRF2, r_Enc) ← PRF1.Eval(PRF1.K, s)
                    One-sFE.msk ← One-sFE.Setup(1^λ; r_Setup);  One-sFE.Enc.st ← One-sFE.EncSetup(One-sFE.msk; r_EncSetup)
                    One-sFE.sk_f ← One-sFE.KeyGen(One-sFE.msk, f; r_KeyGen);  PRF2.k ← PRF2.Setup(1^λ; r_PRF2)
                    FPFE.ct ← FPFE.Enc(FPFE.msk, (One-sFE.msk, One-sFE.Enc.st, PRF2.k, 0); r_Enc);  output (One-sFE.sk_f, FPFE.ct)
                    else output (One-sFE.sk_f, FPFE.ct) ← SKE.Dec(SKE.k, c).
sFE.Dec(SK_f, Dec.ST_i, i, CT_i):  i=1: (One-sFE.sk_f, FPFE.ct) = FE.Dec(FE.sk_G, FE.ct); One-sFE.Dec.st_1 = ⊥.     [p. 95–96]
                    i>1: parse Dec.ST_i = (One-sFE.sk_f, FPFE.ct, One-sFE.Dec.st_i).
                    One-sFE.ct_i = FPFE.Dec(FPFE.sk_{H_i}, FPFE.ct);
                    (y_i, One-sFE.Dec.st_{i+1}) = One-sFE.Dec(One-sFE.sk_f, One-sFE.Dec.st_i, i, One-sFE.ct_i);
                    output (y_i, Dec.ST_{i+1} = (One-sFE.sk_f, FPFE.ct, One-sFE.Dec.st_{i+1})).
```

**Persistent states named.** `MSK = FE.msk` (authority). `Enc.ST = (FPFE.msk, FE.ct)` (writer) — **static**: `Enc` reads it and
returns only `CT_i`; the syntax `Enc(mpk, Enc.st, i, x_i) → ct_i` (Def. 1.1.3, p. 6; Def. 1.3.3, p. 27) has no updated state.
`PRF1.K` is used once in `EncSetup` and is *not* retained in `Enc.ST` (it lives only inside `FE.ct`). `Dec.ST_i` (reader) carries
`One-sFE.Dec.st_i`. `One-sFE.msk`, `One-sFE.Enc.st`, `PRF2.k` are never in anyone's clear state — they exist only as `FE`/`FPFE`
plaintexts.

**The inner `One-sFE`** (dissertation Ch. 2 §2.2, pp. 50–52; = GKS23 §5.2, BKS25 §4): `Setup` outputs `MSK = (K, K', K_p)`,
three PRF keys from which every SKE key `sk_{i,j,b}` (function-label keys), `sk'_{i,ℓ,b}` (state-label keys) and every pad
`p_i` are derived (p. 51). **`One-sFE.EncSetup(MSK)` outputs `Enc.st = ⊥`** (p. 51). `Enc(MSK, ⊥, i, x_i)` garbles the circuit
`C[x_i, p_i, p_{i+1}, {sk'_{i+1,ℓ,b}}](f, s̃t_i)` — `x_i` is *hardwired* — and encrypts each input label under the matching SKE key
(pp. 51–52, Fig. 2.5). `KeyGen(MSK, f)` releases the label keys for `f` at every index and for `s̃t_1 = p_1 ⊕ ⊥` (p. 46).
`Dec` evaluates the garbled circuit and carries `Dec.st_{i+1} = (s̃t_{i+1}, {sk'_{i+1,ℓ,s̃t_{i+1}[ℓ]}})` — the state one-time-padded
(p. 47). Streaming functions start from `st_1 = ⊥` (Def. 1.1, footnote 1, p. 5; 2022/1599 Def. 1.1).

**The bounded-collusion variant** (BKS25 = 2024/1213 §5.2, pp. 49–50, Figs 8–9) swaps the FPFE roles: `Enc.ST = (FPFE.msk,
FE.ct, 1^Q)`; `CT_i = FPFE.ct_i ← FPFE.Enc(FPFE.msk, (i, t_i, x_i, 0^{ℓX}, 0^{ℓOne-sFE.ct}), 1^Q)`; `FE.Dec(FE.sk_G, FE.ct)` now
yields `(One-sFE.sk_f, FPFE.sk_H)` with the honest `One-sFE.msk` hardwired into `H`; `One-sFE.ct_i = FPFE.Dec(FPFE.sk_H, FPFE.ct_i)`.

## 2. Credential inventory and the attack path [DERIVED]

| artifact | holder | lifetime | what it derives |
|---|---|---|---|
| `FE.msk` (MSK) | key authority | permanent | any `SK_f`; with `f = projection`, a reader of every stream under this `MPK` |
| `FE.mpk` | public | — | `FE.ct` |
| `PRF1.K` | writer, transient | `EncSetup` only; then only inside `FE.ct` | with `s` (inside `SK_f`): the honest `One-sFE.msk`, `PRF2.k` |
| **`FPFE.msk`** | **writer, in the clear** | **whole stream, static** | any `FPFE.KeyGen` **and any `FPFE.Enc`** — the second is the hole |
| `FE.ct` | writer; public in `CT_1` | stream | nothing alone; with `SK_f`: the reader's `(One-sFE.sk_f, FPFE.ct)` |
| `t_i` | inside `H_i` (hidden by FPFE function privacy) | per element | encryption randomness `r_i` |
| `CT_i = FPFE.sk_{H_i}` | public | — | `H_i(·)` on any FPFE plaintext one can produce |
| `SK_f = FE.sk_{G_{f,s,c}}` | reader | permanent | `f(x)` only, under the theorem |
| `One-sFE.msk, PRF2.k, One-sFE.Enc.st = ⊥` | nobody in the clear | inside `FE.ct` / `FPFE.ct` | the honest inner stream |
| `One-sFE.Dec.st_i` | reader | per step | `s̃t_i = st_i ⊕ p_i`; pads derive from `K_p ⊂ One-sFE.msk`, never released |

**The path (dissertation / GKS23 / DGKS24 form).** Adversary holds `FPFE.msk` (from `Enc.ST`) and the stored `CT_1..CT_T`;
`FE.msk` erased; no `SK_f`.

1. `msk* ← One-sFE.Setup(1^λ)`, `Enc.st* = One-sFE.EncSetup(msk*) = ⊥`, `k* ← PRF2.Setup(1^λ)` — the "valid inner setup".
2. `FPFE.ct* ← FPFE.Enc(FPFE.msk, (msk*, ⊥, k*, 0))` — the redirect: an FPFE ciphertext the honest scheme only ever makes inside `G`.
3. For each `i`: `FPFE.Dec(FPFE.sk_{H_i}, FPFE.ct*) = H_{i,x_i,t_i}(msk*, ⊥, k*, 0) = One-sFE.Enc(msk*, ⊥, i, x_i; PRF2.Eval(k*, t_i))`
   — by FPFE correctness, the same equation the paper's own correctness proof uses (§3.3, p. 96) with the plaintext swapped.
4. `sk* ← One-sFE.KeyGen(msk*, f*)` with `f*(x, st) = (x, st)` (if `ℓY < ℓX`, several projections; multiple keys under one
   `msk*` decrypt correctly — "single-key" is a *security* restriction on One-sFE, not a correctness one).
5. `One-sFE.Dec(sk*, ·, i, ·)` over `i = 1..T` in order returns `y_i = x_i`.

Needs: `FPFE.msk`; the stored elements from index 1 (black-box `One-sFE.Dec` is stateful — the handoff's "consistent stream
prefixes"); an inner setup of the adversary's own. Does **not** need: `FE.msk`, any `SK_f`, `FE.ct`, `PRF1.K`, the honest
`One-sFE.msk`. Exposure at time `T` also reads every element written *after* `T` (same static `FPFE.msk`).

**Sharper with the concrete inner scheme.** `msk* = (K*, K'*, K_p*)` yields *both* SKE keys of every label wire and every pad,
so the adversary decrypts both labels of `C̃_i`, chooses labels for `f*` and any `s̃t`, and evaluates `C̃_i` alone: `x_i` from a
single element, no prefix. "Consistent prefix" is sufficient for the black-box path and unnecessary for the deployed inner scheme.

**BKS25 form (2024/1213).** `FPFE.sk_P ← FPFE.KeyGen(FPFE.msk, P)` with `P(i, t, x, x', v) = x` (padded to `ℓ_H`; output
length `ℓ_{One-sFE.ct} ≥ ℓ_X`). `FPFE.Dec(FPFE.sk_P, CT_i) = x_i`. One step, no inner setup, no prefix.

**The paper's own words, and the sharpening.** Dissertation Def. 1.1.3 footnote 2 (p. 6; same footnote at 2022/1599 Def. 1.3):
"The purpose of the encryption state is to tie elements of the stream together and must be kept secret in order to prevent mix
and match attacks. Suppose that the encryption state either did not exist or was made public. Then an adversary given a function
key for some streaming function f and ciphertexts ct_1, …, ct_n … could learn the value of f on any extension of the stream."
That is a statement about the *syntax* (harm = `f` on interpolations, and it presumes a function key). In the *construction* the
state is a secret-key-FE master secret, and the harm is total plaintext recovery with no function key. The handoff's "second
master secret" is `FPFE.msk`, exactly.

**Negative controls.** (i) Remove `FPFE.msk` — adversary gets `FE.ct`, all `CT_i`, any number of `SK_f`: that is precisely the
Def. 1.3.4/1.3.5 adversary, and Theorem 3.0.1 (p. 90; = GKS23 Thm 6.1, p. 54; BKS25 Thm 5.1, p. 47) says it learns `f(x)` only;
FPFE function privacy hides `x_i, t_i` inside `sk_{H_i}`; the path fails at step 2. (ii) Replace `FPFE.msk` by what the honest
reader derives (`FPFE.ct` here; `FPFE.sk_H` in BKS25): only the honest `H` with the honest `One-sFE.msk` is evaluable, so only
`One-sFE.ct_i` under a key the adversary lacks — `f(x)` again. (iii) Remove `CT_1..CT_{i-1}`: the black-box path fails
(`One-sFE.Dec.st_i` unavailable); the concrete-inner-scheme path does not — stated so nobody quotes (iii) as a mitigation.

## 3. The bound [READ] — 2024/1213

Def. 3.18 (p. 26), step 4(a): "**Function Query: The adversary can make at most Q such queries**"; step 4(b) *Challenge Message
Query* runs "for a polynomial number of rounds" with the index incremented each time — the stream is unbounded. Def. 3.17
(p. 25): streaming-efficient means sizes/runtimes "are poly(λ, ℓF, ℓS, ℓX, ℓY, Q)" — no `n`; "only sizes and runtimes of
EncSetup, Enc and Dec algorithms are allowed to grow with the key-bound Q." Def. 3.19 (p. 26–27, dynamic): the adversary
"first outputs the key-bound 1^Q" at the first message query and `Enc.st ← sFE.EncSetup(mpk, 1^Q)` — **Q is chosen by the
writer at EncSetup**, and the game outputs 0 "if the number of function queries made by the adversary exceed Q."
Theorem 5.3 (p. 47): "Assuming the existence of an identity-based encryption scheme with IND-CPA security (resp. one-way
functions), there exists a dynamic bounded-collusion, semi-adaptive-function-selective-IND-secure, public-key (resp.
function-selective-IND-secure, secret-key) sFE scheme for P/Poly." Semi-adaptive-function-selective (Def. 3.20, p. 27): all
function queries before any message query. Overview p. 12 confirms the design intent: "we only need to generate one FE key per
function key of our sFE scheme … only one FPFE ciphertext per (function, stream) pair."

**Consequence for a one-transition-program resident.** The handoff is right: `Q = 1`, fixed by the writer at `EncSetup`, with the
single key issued before the first element — which is exactly a program fixed at init; the semi-adaptive restriction costs
nothing. Assumption drops to IBE (public-key) / OWF (secret-key). Two cautions. (a) The bound never limited the stream, so it
never bore on §2: `Q = 1` leaves `FPFE.msk` in `Enc.ST` unchanged. (b) The inner `One-sFE` is itself a `Q = 1` secret-key sFE
from OWFs (BKS25 Thm 4.1, p. 28; dissertation Thm 2.1); using it bare is worse, not better — its `EncSetup` is `⊥` and `Enc`
takes `MSK` itself, so the writer holds the master secret outright.

## 4. Malicious encryptor [READ] — 2025/330

DGKS25 §1 (p. 3): "Unlike deterministic FE, where security primarily focuses on restricting the decryptor's view, rFE must also
defend against malicious encryptors … encryptors cannot produce malformed ciphertexts for a message x that, when decrypted under a
secret key for a function f, yield outputs that deviate significantly from the true distribution of f(x)." On the prior IND
definition (§1 "Limitations …", p. 4): "simply providing a decryption oracle in the IND security game — otherwise designed to
target malicious decryptors — fails to effectively capture security against malicious encryptors"; and ("Old vs. New IND
Definition"): the [GJKS15] oracle "merely runs the decryption algorithm of the underlying rFE scheme, allowing adversaries to
submit malicious ciphertexts and obtain biased or correlated outputs." Their fix (Def. 4.5, §4) is a two-mode oracle — real
decryption vs. an extractor-anchored ideal one — and their counterexample (§5 "Insecurity of the constructed rFE scheme") is a PRF
with a trojan key branch `(K', 1, r)` that lets the encryptor pin the function's randomness to `r` across ciphertexts. Footnote 1
(p. 3): some rFE works "omit protection against malicious encryptors, as it is unnecessary for their target applications."
The paper never mentions streaming (0 hits for "streaming").

**Does it apply to the host as the "learn" input issuer?** Three cases. (a) sFE's functionalities are deterministic (Def. 1.1:
`f : X × S → Y × S`), the IND games run `Enc` inside the challenger, and none of the four sFE texts defines a decryption oracle,
robustness, or malformed-ciphertext behaviour (0 hits each for "decryption oracle", "malformed", "robust"); a malicious host
encryptor in sFE can choose `x_t` (data poisoning — orthogonal; DARK-TRAINING §5's gradient-norm and membership proofs are the
answer) or emit garbage `CT_i`, about which the theorems promise nothing. (b) The moment the transition is randomized — minibatch
sampling, dropout, DP noise — it is an rFE functionality and the DGKS25 gap applies with the host as encryptor: in the sFE
construction the per-element randomness is `r_i = PRF2.Eval(PRF2.k, t_i)` with `t_i` chosen by the writer and `PRF2.k` seeded
jointly from the writer's `PRF1.K` and the authority's `s` (Figs 3.2–3.3), so the writer already co-controls the seed; the only
extractor-anchored construction in the corpus is DGKS25 §6 (iO). (c) For the credential claim itself the malicious-encryptor
axis is second-order: §2 says the writer can *read* the stream; whether it can *bias* a randomized `f` is a further, separate loss.

## 5. Verdict

**Mismatch with a stronger exposure model, not a break.** Every sFE theorem read (dissertation Thm 3.0.1, GKS23 Thm 6.1/6.3,
BKS25 Thm 5.1–5.3, DGKS24 §7) is proved in games where `Enc.st` is sampled and held by the challenger (Def. 1.3.4 step 4(b)(i),
p. 29; BKS25 Def. 3.18 step 4(b)(i), p. 26). The handoff's stronger requirement — no surviving read-all credential after exposure
of what the appender must hold — is outside those games, and the construction fails it as derived. The papers' footnote names the
secrecy requirement but understates its content.

**Which tier SFE-as-constructed addresses.** Only the *reader*: a party holding `MPK`, ciphertexts and any bounded (BKS25) or
unbounded (GKS23/DGKS24) set of function keys — but not `Enc.ST` and not `FE.msk` — learns `f(x)` and sees the running state only
as `st_i ⊕ p_i`. That is the "the host as decryptor learns only `y_t`" half of a learn/infer-only resident, and it is real.
- **A (honest init, then exposure): not addressed.** `Enc.ST` is static (§1), unratchetable by syntax, and a read-all credential
  for past and future elements (§2). No forward secrecy, no post-compromise security for the writer.
- **B (malicious setup): not addressed.** Two single points of trust: `FE.msk` issues a projection key for any stream; and the
  writer generates `FPFE.msk` itself in `EncSetup` — there is no setup between the writer and the credential.
- **C (threshold): absent.** Zero hits for "threshold" in all five texts (Kagi: no threshold/decentralized sFE surfaced). A
  quorum `FPFE.KeyGen` per element (or per-element `FPFE.Enc` in BKS25) is the shape of a repair; nothing in the corpus builds it.
- **D (hardware): absent.** Zero whole-word hits for TEE/enclave/hardware in the sFE texts (the single hit is DGKS25's bibliography entry [BKMT21] "Steel: Composable hardware-based stateful and randomised functional encryption", p. 74 — cited, not used).

**The DARK-TRAINING bite.** Streams start at `st_1 = ⊥` (Def. 1.1 fn. 1). So `W_0` lives either in `f` or in the stream. The
outer scheme promises no function hiding (Def. 1.3.4 hands `sk_f` for chosen `f`; "function-hiding" 0 hits in the dissertation
and 2024/1213; FE is not function-private), so `W_0 ∈ f` is readable by the reader — the host. Hence `W_0 = x_1`, encrypted by
an initializer under `Enc.ST` — and then **whoever appends `x_2, x_3, …` must hold `Enc.ST`, and by §2 reads `x_1 = W_0`** and
recomputes every `S_t` (deterministic in `f, x_1..x_t`, all now known). Appending and reading are one credential. The only
SFE-shaped deployment that keeps `W_0` from the host makes a separate custodian the writer (host sends `x_t` in the clear to it):
a single custodian with a static read-all secret — the custodian DARK-TRAINING §6 replaced with a quorum. Verdict for the pillar:
SFE supplies the *reader-side* guarantee and the *state-carrying* syntax; it does not supply the writer-side one, and the writer
is the host.

## 6. Absence claims, instrument, and what was not verified

- **No sFE paper in the corpus discusses `Enc.st` exposure beyond the mix-and-match footnote.** Instrument: `grep -n -i
  'leak|expos|compromis|forward secre|corrupt'` over the five texts — the dissertation's four hits are all inside security proofs
  (lines 2246, 2368, 4736, 5652); "forward" hits are "put forward"/"straightforward" only; "ratchet" 0.
- **No forward-secure / state-evolving / threshold / decentralized sFE exists in the corpus or surfaced on the web.** Instrument:
  the greps above plus Kagi, 3 of 6 queries ("forward secure streaming functional encryption evolving encryption state";
  "streaming functional encryption \"encryption state\" compromise OR leakage OR exposure Guan Korb Sahai"; "threshold OR
  decentralized \"streaming functional encryption\"") — results were the four known sFE papers, their Springer pages, and
  unrelated STE/threshold-signature hits. The Springer snippet for GKS23 reproduces the footnote quoted in §2 verbatim.
- **The dissertation's §3.2 is the CRYPTO'23 construction**, not the CRYPTO'25 one (chapter map: Ch. 2 = One-sFE, Ch. 3 =
  bootstrapping to public-key sFE, no bounded-collusion chapter); the BKS25 role-swapped form was audited from 2024/1213 directly.
- **Not verified.** The FPFE function-privacy transformation ([BS18]) and the function-size padding for the projection key in the
  BKS25 path (§2) were taken from the parameter section (dissertation pp. 91–92; BKS25 §5.1), not re-derived. The dissertation's
  §3.4 proof was not read line-by-line — the verdict does not depend on it, only on the game definitions (read) and correctness
  (read). No page of 2025/330 beyond §1, §4 Def. 4.5, the §5 counterexample, and §6.3–6.4 headings was read. Nothing in this note
  was executed; every step in §2 is an application of a correctness equation the source states.
