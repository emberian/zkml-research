# dark-learning gen 6, deploy lane (xbox): the three-machine deployment and the run orchestrator

Owns: native/darkstep src/net.rs, src/node.rs, src/bin/*, src/coins.rs, src/bfv.rs and src/he.rs (taken over from the
retired gen-5 zkpopk lane for the coin fix), the multi-step party loop, TLS, deployment scripts under native/deploy/.

## The coin break and its fix

[EXECUTED] Found 2026-11-07, reading the production party path: a `darkstep party` process (no `test-det`) drew
every secret HE coin from PUBLIC seeds:
- the ungated key, `OwnKey::new(rns, 100 + i)`: s, a, e and every later encryption coin from random.Random(100 + i);
- the ceremony key's encryption coins, `OwnKey::from_ceremony(rns, 100 + i, ..)`: random.Random(100 + i). This is
  MT19937, and a is published in every ciphertext, so the stream is recoverable even with a secret seed;
- every HE return, `bfv::make_return`: the mask M, u, e0, e1 and the 2^F flood from random.Random("hm|11|call|
  transpose|me|j|o") (matvec) and random.Random("ho|13|call|me|j|ab|b|kind") (outer).
Attack [DERIVED]: recipient j recomputes sender i's M and decrypts i's return to the plaintext W_i x_j (for matvec)
and the outer products, in every call. That recovers i's share of W1 and W2. Done to both peers, it gives one
corrupted custodian the whole model. In the ungated mode j also recomputes s_i.

Fix (a996539e..; see commit below):
- `darkstep::coins::Coins` = `Py(PyRandom)` (the harness's reference streams) | `Prf` (SHA-256 counter mode under a
  32-byte OS key, one stream per label; uniform samplers by rejection, the same distributions).
- `OwnKey.rng: Coins`, plus `OwnKey.return_key: Option<[u8; 32]>`. HE returns take `key.return_coins(label)`: the PRF
  under return_key with the same label, or the reference stream when it is None.
- New constructors: `OwnKey::new_secure(rns)` and `OwnKey::from_ceremony_secure(rns, s, b, a)`. They draw every coin
  from the OS, and `refresh_return_key()` is called per step. The old `new(seed)` and `from_ceremony(seed, ..)` stay
  as the reference.
- `Prof::secure_coins`: the `party` subcommand always sets it. Only `run_local`, the in-process test harness where
  all three custodians share one process anyway, keeps the reference streams, so vs_reference stays bit-exact.
- `deal` (public-seed ideal dealer) and `reveal` (reassembles the model) now exist only with the cargo feature
  `test-harness`; a deployed party binary has neither.

Tests [EXECUTED, Mac]:
- `cargo test --release -p darkstep --features test-harness --test party_coins`: 2 passed (ungated and gated T = 309,
  N = 4096, d = 64). Each test runs two production runs of the real `darkstep party` binary, three processes each,
  on the same reference tapes and inputs. In both runs all three ACCEPT, agree on one transcript, and refine the
  spec. The share digests differ from the reference's and between the two runs, and so do the transcripts.
- Negative control: with `secure_coins = false` in the binary, the test fails at "broadcast shares carry fresh masks"
  (the transcript equals the Python reference).
- Correction to what I first told the coordinator: the transcript does NOT stay equal to the reference under fresh
  coins. It holds each party's broadcast share, which carries the masks, and the Freivalds/MAC coins are drawn from
  it, so later opened values change too. A public-value check of the run therefore has to be on the step's outputs
  (the plaintext rerun against the released output, and the per-step proofs), not on a transcript digest.
- Unchanged: `--test vs_reference` 6 passed, `--test bfv_vs_python` 1, `--lib` 1 (the PRF samplers' ranges and
  spread, stream separation), `--features test-det --test vs_reference_gated` 3 passed.

## Randomness audit: every source a production party binary reaches

(a) = public by design, (b) = OS / CSPRNG unless test-det.

| source | where | kind |
|---|---|---|
| HE return M, u, e0, e1, flood | bfv::make_return via he.rs matvec/outer | (b) PRF under OwnKey.return_key (fixed here; was public seed) |
| BFV key s, a, e (ungated) | OwnKey::new_secure | (b) PRF under an OS key (fixed; was random.Random(100 + i)) |
| BFV encryption coins (a, e of each sender ct) | OwnKey.rng | (b) PRF (fixed; was random.Random(100 + i)) |
| ceremony r, salt | dzkpopk Custodian::new, hex32_os | (b) /dev/urandom |
| ceremony key s, e | dzkpopk Custodian::make_key, OsHiding | (b) /dev/urandom (seeded only under test-det) |
| ceremony seed, a_j = public_a(seed/j) | dzkpopk Ceremony | (a) public by design (joint commit-reveal) |
| ZKPoPK hiding (masks, salts) | dzkpopk rng::OsHiding | (b) /dev/urandom; DetHiding only under test-det |
| ZKPoPK challenges | dzkpopk transcript | (a) Fiat-Shamir |
| Freivalds rho (matvec check) | he.rs, random.Random(hash of transcript) | (a) Fiat-Shamir, after the openings it checks |
| outer-check coins | he.rs, after the G commitments | (a) Fiat-Shamir |
| MAC-check rho | party.rs mac_check, random.Random(hash of openings + transcript) | (a) Fiat-Shamir, after the openings |
| MAC-check sigma commitment nonce | party.rs, getrandom | (b) OS |
| SPDZ tapes (alpha_i, triples, masks) | tape.rs Dealer, PyRandom(DEALER_SEED = 5) | TEST ONLY: `deal` needs `test-harness`; the deployment's tapes come from darkprep (MASCOT, prep lane) |
| owner input masks r | tape.rs owner PyRandom(OWNER_SEED = 9) | TEST ONLY, as above; deployed: darkprep owner.rs (r = a of a checked input triple) |
| inputs | step::inputs(d) = random.Random(d) | TEST data; the train lane's data-owner feed replaces it |
| TLS keys and certificates | (to come: rcgen + ring SystemRandom) | (b) |

Notes:
- MV_SEED = 11 and OU_SEED = 13 survive only as parts of the PRF labels, so the streams stay separate. They are not
  key material.
- The test dealer is MT19937 under one seed: a custodian holding its own tape could recover the stream and with it
  the other tapes, whatever the seed. That is why it is test-only and not merely re-seeded.
- darkprep: no randomness is drawn natively. Tapes and owner masks are assembled from MP-SPDZ's MASCOT output
  (MP-SPDZ seeds its PRNGs from the OS) [SOURCE: prep lane; to be confirmed by it].
- darkhand (handover lane): `new_side` used `OwnKey::from_ceremony(seed)`, an MT stream; the replacement is
  `OwnKey::from_ceremony_secure` (told to the handover lane).
