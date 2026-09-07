# Independent preregistration review

[DERIVED / contract review, 2026-09-07] The four-bin signed-byte EMA contract is mathematically consistent. No arithmetic or role-boundary blocker was found. The implementation is not yet frozen; this note reviews the contract and preserved earlier probe only. It makes no claim about an executed new encrypted run.

[DERIVED / exact range] For arbitrary signed bytes `s,u∈[-128,127]`, `8s∈[-1024,1016]`, `7s∈[-896,889]` and `7s+u∈[-1024,1016]`. Every value fits signed 11 bits. The contract's numerator interval is thus a correct conservative bound. Restricting u to ±120 tightens the one-step numerator interval to `[-1016,1009]`. On the stated invariant `s∈[-120,120]`, the numerator lies in `[-960,960]`.

[DERIVED / exact circuit meaning] Sign extension from eight bits to eleven preserves s and u. An eleven-bit word formed by three low zero bits followed by the original eight s bits represents 8s. The two's-complement sum `8s + NOT(sign_extend(s)) + 1` represents 7s modulo 2048, with its signed value exact because 7s is in range. Adding the sign-extended u is likewise exact. Selecting bits 3 through 10 and reading them as a signed byte computes floor division by eight, including negative values. It is not signed division rounded toward zero. The final range is again `[-128,127]` for arbitrary signed-byte inputs.

[DERIVED / invariant and fixture] The weighted average `(7s+u)/8` remains in `[-120,120]` when s and u do. Taking its floor preserves that integer-bounded interval. Starting from zero, the preregistered selected bin therefore moves `0→15→−2`; the second step uses `floor((105−120)/8)=−2`. The other bins remain unchanged. The selected sign changes from false to true, with zero classified as nonnegative.

[DERIVED / address convention] With least-significant-bit-first addresses, let `b=b0+2*b1`. A per-bin conjunction of the corresponding bit or complement selects exactly that bin. TFHE's `mux(condition,then,else)` chooses the candidate when selected and the old byte otherwise. For sign inference, `low=mux(q0,s1_sign,s0_sign)`, `high=mux(q0,s3_sign,s2_sign)`, followed by `mux(q1,high,low)` selects exactly the addressed sign using three MUX calls. The author reports this intended source arrangement; immutable code still needs checking.

[SOURCE / preserved earlier code] The earlier `he_closure_costs/tfhe_ema_probe/src/main.rs` was read in full. Its adder makes two AND and three XOR calls per bit, with eleven NOT calls for subtraction. One candidate therefore makes 44 AND, 66 XOR and 11 NOT calls. It creates three public zero bits and two carry constants, for five `trivial_encrypt` calls. The earlier retained log reports four arithmetic updates and 176 AND / 264 XOR / 44 NOT calls; this is earlier executed evidence, not an independent rerun.

[DERIVED / expected new top-level counts] Four candidates, two shared address complements, four per-bin conjunctions and 32 output-bit MUX calls give:

| Learn API | Calls |
|---|---:|
| AND | 180 |
| XOR | 264 |
| NOT | 46 |
| MUX | 32 |
| trivial_encrypt | 20 |

[DERIVED] The expected Infer tally is three MUX calls. These numbers count explicit top-level calls, including calls whose inputs contain public trivial constants. They are not measured programmable-bootstrap counts or operation-independent timing weights.

[SOURCE / cached TFHE 1.6.3] `src/boolean/server_key/mod.rs:147` establishes the condition/then/else order. `src/boolean/engine/mod.rs:411` implements the fully encrypted MUX with two bootstrap calls, while allowing shortcuts for trivial inputs. The same engine's `not` method at line 327 negates encrypted ciphertext coefficients without a bootstrap. `src/boolean/ciphertext/mod.rs:14` derives serialization for the `Encrypted`/`Trivial` representation. These source facts support the contract's API-count distinction and the proposed replay comparison. They do not prove whole-program byte determinism.

[DERIVED / roles and interpretation] The retained ClientKey is an unrestricted read credential. Separate binaries and directories under one OS account establish a testable file-flow boundary, not isolation from that account owner. The normal fixture's bin and labels are already public in the contract, so this experiment can demonstrate encrypted addressing at the host API while making no claim that its preregistered values are unknown to an observer of the research note. Value-free host arguments, filenames and logs still matter for accurately reporting that API boundary. The author has agreed to preserve this distinction.

[DERIVED / replay scope] Comparing full serialized results from identical serialized server key, state, request and binary inputs in separate processes is a useful concrete byte-replay test. New encryption randomness must not be compared with old ciphertexts. Success would apply to the tested environment and sample; a failure would block the tested exact-byte path. Output envelopes must exclude per-run timestamps or other varying metadata if their entire bytes are compared. Evaluation-only time must be separated from server-key read/deserialization and process overhead.

[OPEN / next review] After source freeze, inspect arithmetic and address order, envelope lengths/types, CLI file reads, reader-only key use, instrumentation and the replay driver's comparison/gating logic. Check immutable source/report hashes. Do not open private keys, fixture requests, plaintext audit files or protected ciphertext artifacts, and do not execute encryption or routing/adversarial tests. Parameter security, setup correctness, selected-output enforcement and no-master-read remain outside the claim.
