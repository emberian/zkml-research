# Actual fixed-span encrypted window learner

[EXECUTED / DERIVED] A small DDH inner-product FE learner now runs end to end:
private honest setup, public-key input issuance, encrypted insertion and expiry,
and fixed-key score reads. The master is not a runtime input or exported file.
This is an actual group-arithmetic reference with privacy **modulo a fixed
observable span**, conditional on its stated assumptions. It is not the full
private resident, production cryptography or a post-quantum construction.

[EXECUTED] Replay from the repository root:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/fixed_span/audit.py > research/learn_infer_only/experiments/private_construction/fixed_span/stdout.txt
```

The audit calls only positive algorithms from the previously approved DDH
control. It never invokes that control's `main()` or earlier negative tests.
No state-recovery/extraction or ideal-window disclosure experiment is included.
All input fixtures are synthetic and public in the audit record.

## Interface and exact algebra

[DERIVED definition] An observation is a three-coordinate integer vector in
`[-2,2]^3`, encrypted by its issuer under the public key. The learner maintains
an encrypted sum of the most recent four observations. The fixed inference
vectors are `y0=(1,1,0)` and `y1=(0,1,1)`. Their two released scores determine a
public class: one if score1 exceeds score0, otherwise zero. This is a moving
feature-statistic learner with a fixed classifier, not neural training or a
secret variable inference policy.

[SOURCE] The existing audit was read first. ABDP,
[*Simple Functional Encryption Schemes for Inner Products*, 2015/017](https://eprint.iacr.org/2015/017),
local revision October1,2015, Fig.2 p.7 and Construction3.1/Theorem3.2 pp.7–9:
for group order q, master vector s, public `h_i=g^s_i`, the function key is
`key_y=<s,y> mod q`; encryption is `(g^r,(h_i^r g^x_i)_i)`. Combining ciphertext
coordinates multiplicatively adds their plaintext vectors and randomizers.
Projection gives `g^<x,y>`; recovering the integer requires discrete-log decoding.
The paper's stated theorem is selective IND-FE-CPA under DDH.

[DERIVED window invariant] Let `C_t` denote each exact issued ciphertext. The
aggregate is the coordinatewise product of the ciphertexts in the active queue.
Appending multiplies by the new ciphertext; expiry multiplies by the inverse
of the same old ciphertext. Thus

```
A_t = product(C_j for j in the current four-item window)
    = Enc(sum(x_j), sum(r_j) mod q).
```

The implementation checks byte equality with a freshly multiplied current queue
after every update. The same-size group algebra has no encryption noise to
accumulate. Exact-byte expiry gives this strong identity; unlike the BFV noise
case, exact old bytes are not necessary merely for DDH plaintext correctness
if an independently encrypted copy of the same plaintext were available.
No such alternative-expiry experiment is performed here.

[DERIVED range] Each window coordinate is in [-8,8]; each fixed projection is
in [-16,16]. A 33-entry lookup table therefore gives an unambiguous integer
readout. Its range is independent of the number of window turnovers. The group
algebra supports continued operation; the source proof covers polynomial-time
experiments, and the concrete checkpoint uses a 64-bit step counter. No infinite
execution or arbitrary-size efficiently decoded output is claimed.

## Complete exposure and lifecycle

[DERIVED threat model] The host receives the public key, both fixed function
keys, every issued ciphertext it handles, checkpoints and all score outputs.
It can compute every key in the span of y0,y1 and use those keys locally. Thus
the full permitted information includes **individual input projections**, group-
valued projections, public linear combinations and retained past artifacts.
The interface is not acknowledgment-only learning or a proof-bound release gate.
The integer decoder is an application convenience, not a restriction on the
information obtainable from an exposed projection key.

| Role / phase | Material available | What must remain private or be erased |
|---|---|---|
| Honest private initializer | Master vector, public key, fixed Y, issued keys | Master vector, setup coins and any copies after setup |
| Input issuer | Public key, its own observation and fresh input coins | Raw observation/coins from host observation; erasure if later exposure is modeled |
| Host evaluator | Public key, two fixed projection scalars, ciphertext queue/aggregate | No master or issuer plaintext/coins are supplied |
| Released output | Both fixed integer scores and public class | No private recipient-only output claim |

[EXECUTED] Initialization, issuance and evaluation are separate subprocesses.
The initializer exports exactly `public.bin` (768 bytes) and
`projection_keys.bin` (512 bytes), then exits before issuance. The issuer's CLI
receives only the public-key path and its observation stream on stdin. Normal
issuer output contains only public byte/record counts. The evaluator receives
only the two fixed keys, ciphertext stream and optional prior window checkpoint.
It continues after a checkpoint in another process without a master argument.

[DERIVED boundary] Separate processes make this API and artifact boundary
reviewable; isolated Python mode is not protection against the machine's
operator. Private initialization and private issuance must occur outside the
host's observation, or under an explicitly adequate boundary. Python process
exit does not prove erasure of memory, swap, backups or copies. The reference
uses variable-time arithmetic. Its synthetic issuer timing diagnostics are
kept separate from the deployed ciphertext interface; source security does not
cover leaking private setup/issuance timing or execution state. Public runtime
computations use ciphertexts and function keys already exposed to this host.

[DERIVED missing policies] There is no mechanism for arbitrary later function
keys after master erasure, single-history finality, origin authentication,
private recipient release, enforced deletion or private nonlinear updates.
The host may retain past ciphertexts and the same fixed projection keys.
Normal checkpoint consistency checks are not authentication. No experiment
attempts to obtain an unissued projection or reconstruct a raw state.

## Privacy statement and nonvacuity

[DERIVED source-backed scope] For histories fixed before setup whose
corresponding inputs agree on both projections, the source selective theorem
and a polynomial ciphertext hybrid cover the whole exposed package. Public
window operations and reads are postprocessing of that package. This is an IND
statement, not an ideal-simulator theorem. Equality of current window totals
alone is insufficient as a history-level admissibility condition.

[DERIVED specialization] `ADAPTIVE_FIXED_SPAN.md` gives a separate direct DDH
reduction for this exact fixed span, allowing admissible message pairs chosen
adaptively after the public key and prior history. The proof chooses the hidden
master direction along the fixed kernel before seeing messages. For T challenge
ciphertexts its strict-PPT padded hybrid gives `Delta <= 2M epsilon_DDH`, where
`M=next_power_of_two(max(1,T))`; at T=12 the coefficient is 32. This new derivation
was sent for independent mathematical review. It is not attributed to the
paper's selective theorem and does not provide quantum or malicious-setup
security.

[DERIVED / EXECUTED nonvacuity] The common kernel is generated by `(1,-1,1)`.
All 15,625 ordered pairs in the bounded 125-state input domain were checked:
equal fixed projections iff their difference lies in that kernel. There are
61 observable classes and 325 equivalent ordered pairs, including 125 diagonal
pairs. The two executed histories differ at every observation by `(1,-1,1)`;
each pair remains inside the bounded input domain. This establishes nonidentical
admissible examples. It does not say every bounded input is ambiguous after
its permitted projections are known.

[DERIVED functional limit] Kernel distinctions cannot affect any permitted
future answer under this fixed interface. A plaintext implementation using
only the two projected input values would realize the same observable learning
functionality. The DDH version retains the full raw vectors encrypted; it buys
representation privacy and encrypted retention, not demonstrated private
cognition from those invisible distinctions. Expanding the query family would
change the security condition.

## Executed behavior, costs and provenance

[EXECUTED] Two independently randomized 12-input histories, each processed in two
six-input phases, give the same changing scores. The first six windows produce
`(0,2),(2,4),(4,4),(5,7),(6,6),(7,5)`. Both classifier outcomes occur.
Checks passed: 48 fixed projection values against a plaintext oracle,
24 exact aggregate/queue byte identities,16 ordinary expirations and two normal
checkpoint continuations. These correctness checks do not empirically prove DDH
or computational indistinguishability; the privacy arguments are separate.

| Item | Actual raw bytes / work | Scope |
|---|---:|---|
| Public key | 768 bytes | Three 256-byte group elements |
| Exposed fixed keys | 512 bytes | Two 256-byte scalars |
| Each encrypted observation | 1,024 bytes | Four group elements |
| Active queue | 4,096 bytes | Four ciphertexts |
| Aggregate | 1,024 bytes | One ciphertext |
| Framed checkpoint | 5,140 bytes | Queue+aggregate+20 public framing bytes |
| Per-history traffic | 12,288 bytes | Twelve input ciphertexts; no transport/authentication framing |
| Addition | Four modular multiplies | Before expiry |
| Expiry | Four inverses + four multiplies | After the queue fills |
| Two fixed reads | Two general modular exponentiations plus small products/inverses | Input membership validation measured separately |

[EXECUTED local timing] Preflight five-call medians, saved in
`micro_preflight.json`, were 518.895ms public encryption, 0.070ms addition,
1.606ms expiry and 1285.516ms for two reads using the old wrapper's repeated
membership checks. In the final end-to-end run, observed medians were 121.731ms
public encryption, 127.263ms ingress validation, 1.562ms update and 64.989ms for the
two reads. These were different runs under changing shared-machine load, with
validation separated in the latter; they are not an equal-load speedup claim.
Interpreter startup, checkpoint loading and private setup are excluded from
those per-operation values. Python 3.14.7 on macOS 26.6.1 arm64; the RFC 3526
2048-bit group comes from the approved control. No calibrated security-bit,
production throughput or post-quantum claim is made.

[EXECUTED provenance] `results/results.json` stores all exact process commands,
outputs, measurements, role inventory and source hashes, including the absolute
2015/017 mirror path and approved control. `stdout.txt` preserves the summary.
The saved public key, projection keys and final ciphertext window are synthetic
replay artifacts, not user credentials. Full master vectors and input coins
are not serialized. The earlier source/control files were read and imported
unchanged, with their guarded negative-test entry point never invoked.

[REPORTED] No searches, downloads, packages, commits or shared-ledger edits in
this tranche. Lane counts remain SQL10/schema1/web30/Kagi0.
