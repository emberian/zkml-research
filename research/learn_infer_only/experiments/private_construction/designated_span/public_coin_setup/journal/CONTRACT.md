# Public-coin setup joined to the normal durable journal

[DERIVED contract, 2026-09-08] This isolated successor joins the reviewed honest
public tau/U setup to the unchanged designated journal. It runs exactly forty
Learn, four Infer (rows 0–3 after Learn 10, 20, 30, 40), and eight FIFO expiries
on route zero with capacity 32. Route one remains empty. The fixed 16-by-577
matrix remains unchanged. Known deterministic int8 vectors use
`x[n,j] = ((n+3)*(j+5) mod 17)-8`; this is arithmetic integration, no utility claim.

[DERIVED interface] `setup_join.py` invokes a byte-identical `adapter/setup.py`
copy for registration, recipient-owned scalar sampling, public construction and
full transcript verification. It invokes only params, validate-context,
recipient-finalize and encode-query in the unchanged crypto backend during
setup. No scalar-master generation, initializer or scalar projection delivery
command is part of this path. It constructs journal signing-role configurations
and a genesis extension `public_coin_setup` binding the accepted public transcript,
registry, each announcement, successful verification record, setup source and
source inventory. The standard genesis digest already binds every action,
state, signed transition and installed head to that extension. The extension is
a trusted setup declaration; unmodified services check the pinned genesis digest,
not a new in-service proof of honest sampling.

[DERIVED code boundary] All eight journal/service modules, four crypto files,
and persistent host are copied without edits and hash-checked before use. The
new Run subclass consumes the prepared genesis instead of calling legacy
`roles.setup`; it inherits normal issuance, authorization, acceptance and replay.
The host retains its existing inspection cache and full blob hashing. New wrapper
source and immutable dependencies are pinned before launch. There is one fresh
normal run; no automatic resume or repeat after a failure.

[HYPOTHESIS acceptance gates] All 44 authority envelopes must equal the independent
acceptor's ordered history; all 44 arithmetic transitions must pass full independent
public replay. Every expiry names the exact original FIFO input, the final route
zero queue holds inputs 9–40, and its admissions are 40. Orderly authority/acceptor
reopen at revision 22 and two authorized exact historical retries must preserve
the head and signed envelopes. These are normal functional operations. No
adversarial, routing, extraction, malformed-input or crash-injection test is run.

[DERIVED phase boundary] Full setup verification, all history/RPC operations,
independent replay, log omission checks and public storage/source inventories
finish before private recipient drain. Every host/authority/acceptor process
closes before the private phase. The public completion artifact is written at
that boundary. A separate private oracle compares all four exact signed integers;
a second private drain must add zero decodes. Aggregate comparison success is
published outside the host protocol; private scalars, score/hash material and
private durations remain ignored and uncommitted.

[DERIVED scope] Honest direct public sampling and independent honest registration
remain assumptions. The 16 recipient credentials expose their entire fixed
per-input query span, including retained/expired ciphertexts; software finality
is not a cryptographic restriction on their coalition. Known inputs and zero
initial state allow fixture reconstruction. Shared Unix-account processes supply
no OS isolation or operator confidentiality. Classical DDH, separate Ed25519
registration/journal authentication and SHA-256 addressing remain distinct
assumptions. No malicious setup, selected-only release, private lifetime,
nonlinear learning, hardware finality or PQ result is claimed.

[OPEN checkpoint] Contract saved before implementation/run. The parent owns
shared STATUS/NEXT and commits; this directory will retain execution and a
resumption note. Search accounting: no network or metered queries.
