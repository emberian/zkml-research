# A working 384-bit seeded semantic ring service

[EXECUTED shared run] The new transport completed one fresh candidate_full setup and a continuing two-class learner service: six accepted teaches, two exact expiries, and 16 recipient-specific deliveries. All 32 scalar scores and 16 decisions matched the plaintext reference. Public transition work finished before every recipient read. Total elapsed time was **202.715739 seconds**, including **163.940719 seconds** through public closure. The one run belongs to the journal's `seeded_ring_successor/results/seeded001/`; RUN.json pins its public outputs. No second setup or old-run replay occurred.

[EXECUTED storage] The final public issuer bundle is **9,471,117 bytes**. Including the required fixed semantic registry gives **9,592,617 bytes**. The A descriptor used during registration is 798 bytes; it is reconstructible from the final public header and need not accompany each issuer invocation. The public bundle's explicit product payload is 9,469,952 bytes, compared with 379,389,952 bytes for expanded A and all P coefficients at these dimensions—a **40.0625× payload reduction**. This comparison is exact coefficient arithmetic; it does not include ciphertext storage in either quantity.

[EXECUTED saved actor measurements] The maximum standalone actor RSS across 53 backend receipts was **497,270,784 bytes** on macOS. Each fresh ciphertext file was **37,901,458 bytes**. Recipient key files were 3,801,794–3,801,795 bytes each, totalling 60,828,710 bytes for 16 recipients; each private row payload was 3,801,088 bytes. These sizes come only from public receipt metadata; the collector neither opened nor statted any private artifact. Ciphertext and recipient-key storage were not compressed by the public-seed change.

| Operation | Calls | Per-call seconds, min–max | Total receipt seconds |
|---|---:|---:|---:|
| Recipient registration | 16 | 3.534989–3.659988 | 57.167395 |
| Fresh encode | 6 | 10.956190–12.165805 | 67.612273 |
| Designated query | 16 | 1.898388–2.158070 | 32.386712 |

[EXECUTED timing scope] These are internal backend receipt times. The 202.715739-second complete path also includes public recomputation, journal operations, interpreter startup, source/context checks and orchestration. Peak actor RSS is not a concurrent whole-machine memory sum. RUN.json pins all 53 public receipts and retains unrounded values.

[DERIVED/EXECUTED change] The new `RINGSSM2`/v3 format requires two independent 48-byte public seeds and the explicit policy `honest-dual-seed-384-qrom-v1`. Its headers bind the fixed semantic basis, exact registered-product commitment, setup context and final public bundle. A is reconstructed from its seed; each absent P row is reconstructed and consumed one at a time. All 16 registered products remain explicit, and no absent-recipient secret is created. Old seed lengths and headers are rejected rather than accepted through a compatibility fallback.

[EXECUTED credentials and continuing state] Each recipient generated and retained its own row in a separate private artifact/process. No universal reader was constructed and public actors read no private payloads. The service fully recomputed each canonical `acc+fresh−old` candidate before accepting it, reopened the accepted state in a fresh process at revision 4, refused changed candidates and stale parents, and served the final accepted revision 6. An exact identified-delivery retry reused the receipt without a new key invocation; reusing that identity with changed contents was refused. These are local journal/visibility guarantees, not a succinct proof or cryptographic history-bound key restriction.

[DERIVED theorem application] THEOREM_APPLICATION.md proves the fixed public message transform `Enc_B(x)=Enc_I(Bx mod p)` and maps `Y_J x0=Y_J x1` exactly to the coordinate security game. The actual basis is fixed before A sampling. Secret Gaussian rows are not transformed. The whole two-input integer score bound is 2,520,950<p/2. The ring arithmetic, q, Delta, finite sampler law and integer decoder are unchanged.

[DERIVED conditional QROM scope] At the declared Q_0,Q_1≤2^64 pre-disclosure quantum-query budget, 384-bit seeds give programming term `2^-158+2^-319`. The full up-to-384-input theorem adds `768 epsilon_QR` and finite terms below `2^-168`, with all oracle-simulation/advice costs charged to the exact QPT power-basis Ring-LWE assumption. This execution does not measure epsilon_QR or certify PQ security. Concrete SHAKE256 remains a heuristic instantiation of the oracle model.

[SOURCE/EXECUTED verification] New checks were limited to mandatory header/context rejection, exact descriptor hashing, unchanged postprocessing functions, and the sole shared service run. The byte-identical copied ring/sampler/codec and semantic registry are pinned by SOURCE_PINS.json. The source owner performed no private-file reads or extra cryptographic executions while collecting results. Search count: zero.

[OPEN scope] This is the completed known-public cached linear semantic fixture, not a new accuracy estimate. Each retained ordinary key remains a per-input projection capability outside the journal; coalitions obtain their corresponding span. Malicious setup, timing protections, secure erasure and concrete-XOF security are not established.
