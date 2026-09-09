# What controlled and keyed HE contribute to the resident

[DERIVED decision] These inspected constructions separate permission to evaluate from permission to decrypt. None supplies the missing repeatedly usable, computation-bound release capability with every surviving credential exposed. Controlled HE restricts the circuit but deliberately terminates its ciphertext after one evaluation. The newer keyed constructions allow arbitrary circuits on eligible inputs and retain keys that decrypt those inputs. This is a scoped deployment mismatch, not a refutation of controlled encryption or a break of their security games.

## Controlled HE: a real restriction with a terminal output

[SOURCE: construction] Desmedt–Iovino–Persiano–Visconti, [2014/989](https://eprint.iacr.org/2014/989), Definition 1 and “Composing tokens,” PDF pages 6–7; §4 and Theorem 1, pages 9–10. Public encryption encodes `(M,r,0,sk)`. The token for `C` is a general-FE key for a circuit whose regular-input branch encrypts `(C(M),0,⊥,0)` under the same FE public key. A token presented with the resulting `⊥`-tagged plaintext returns `⊥`. The definition expressly requires only that an evaluated string can be decrypted, not that it can be evaluated again. A fixed constant number of compositions is mentioned as an extension but not constructed there.

[SOURCE: credential and game] `Msk` includes `FE.Msk`; `Dec` derives a key for the first-coordinate identity function. Theorem 1 uses FE for all circuits and requires encryption queries before token queries. We inspected the actual algorithms and theorem statement, not the full reduction.

[DERIVED] Deleting `Msk` removes this ordinary reader, but it does not change the terminal tag or create a restricted outward read. Replacing `⊥` by a reusable tag is a new scheme and security problem. It cannot inherit this theorem by changing the representation alone.

## Keyed FHE: evaluation authority is itself a surviving credential

[SOURCE: construction] Sato–Emura–Takayasu, [2022/17](https://eprint.iacr.org/2022/17), §3.1, pages 12–13. Encryption uses two FHE ciphertexts plus a consistency proof. `sk_d = sk_1` decrypts the first component. The evaluation key is a dual-system NIZK simulation trapdoor; it creates the proof accompanying an arbitrary evaluated circuit. Its security construction explicitly handles exposure of that special trapdoor. We read §3.1, the syntax/game and overview, not the complete reduction.

[DERIVED] This is a useful example of a precisely specified proof-generation credential. It is not permission to treat an ordinary NIZK simulator as a secure reusable release key. Exposing this evaluator does not constrain its circuit, while retaining `sk_d` retains full plaintext access.

## Attribute-based keyed FHE: attributes qualify inputs, not computations

[SOURCE: construction and game] Emura–Sato–Takayasu, [2024/226](https://eprint.iacr.org/2024/226), §3.1 pages 20–21, §4 Definitions 17–19 pages 28–30, and §6.1 pages 38–39. The basic construction has `dk=(IBE.msk,mk)` and `hk=mk`, where `mk` authenticates evaluated ciphertexts. Encryption generates a fresh multi-key FHE key and encrypts its secret under IBE. Decryption recovers that secret.

[SOURCE: construction] The attribute-based version has `dk_y=DABE.sk_(y,0)` and `hk_y=DABE.sk_(y,1)`. For matching input attributes, `Eval` accepts an arbitrary circuit `C`; `Dec` recovers each original FHE secret through delegated DABE keys. Correctness explicitly includes decrypting pre-evaluation inputs. Challenge security forbids revealing a matching decryption key. The abstract claims a standard-model LWE instantiation; we did not audit its lattice reduction or concrete parameters.

[DERIVED] Even if a protocol labels an output “answer,” an eligible evaluator can compute an extraction circuit and authenticate its result. A matching `dk_y` already reads the underlying eligible inputs directly. Attribute access alone therefore does not implement the exact-program gate required here. Giving a recipient only a separately restricted read function would introduce the missing construction rather than obtain it from this keyed-HE theorem.

## Consequence for the construction work

[DERIVED] Keep the actual arithmetic/proof pipeline and the release mechanism as separate obligations. These sources can support private computation with controlled participants. They do not remove the need for a mechanism that binds private continuation and outward release while exposing neither a full reader nor reusable extraction authority. The bounded authentic-parent iO construction in [HIO.md](HIO.md) remains a conditional positive baseline; this source pass does not justify another weaker resident implementation.

[EXECUTED discovery] Eight web search queries, one Scry SQL query, zero direct page opens and zero PDF downloads. Scry returned fifteen records from its bounded OpenAlex snapshot and located the 2024 attribute-based paper. All three algorithm reads used the local eprint mirror. Exact hashes, query strings, inspected locations and raw SQL result are recorded in [SOURCES.json](SOURCES.json). No cryptographic attack, encryption implementation or parameter estimate was executed.
