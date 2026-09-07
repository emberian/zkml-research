# One executable encrypted learner with an explicit trust boundary

[OPEN task contract, 2026-09-06 evening EDT] This is the next authorized night's
integration target, not a report that the target already passes. The run ends at
2026-09-07 10am EDT / 14:00 UTC. The starting evidence is commit `6c56170`;
the existing encrypted-window fixture and repaired persistent journal are
separate experiments there.

## What this demonstration must do

[DERIVED design] Run one actual history through public-key input encryption,
encrypted rolling-window learning, public-query encrypted inference, independent
authorization of the exact transition, durable installation, and delivery of the
selected scalar to the designated recipient. Reuse the frozen W32-per-route,
577-coordinate learner and its exact numerical contract. Run both existing
held-out histories when the complete path is stable; distinguish the number of
encrypted answers from known empty-route zeros.

[DERIVED design] A keyless authority may check the public ciphertext transition
by recomputation. This is an explicit verification algorithm and cost; it is not
a succinct proof, a new cryptographic receipt theorem, or an automatic refinement
of the proposed Lean patches. The authority must accept valid newly encrypted
inputs, not only a precomputed allowlist of approved fixture transactions.

[DERIVED design] The single full-key reader is **benchmark R: trusted reader**.
It is not the handoff's tier C, which additionally specifies distributed trust
and a noncollusion assumption. It is not tier A's absence of every surviving
read-all credential. The reader's restricted API and its internal full decryption
capability must both appear in the credential ledger.

## Roles, artifacts, and observations

| Role | Needed artifacts | Exposure and obligation |
| --- | --- | --- |
| Initializer | OS randomness, BFV parameters and key generation | Creates public key and full reader secret; honest setup is assumed. |
| Observation issuer | Plaintext feature/label, public encryption key, input authorization credential | Host receives a ciphertext. An authorized issuer assertion is not a proof that a hidden feature came from the model or has the stated range. |
| Host | Public parameters/key, encrypted current state and original input queue, public commands/query | No reader secret or plaintext observation is a command input. Host may propose altered transitions and restore its own state. |
| Continuity authority | Public policy, current revision/state commitment, journal, verification/signing credential | Recomputes ciphertext arithmetic and enforces admission. Has no BFV decryption key. Its own rollback/compromise remains a separate assumption. |
| Reader | Full BFV secret, authority verification material, finalized selected output | Checks finalization and recipient/command binding before returning the scalar. Can read arbitrary BFV state if this trusted role is compromised. |
| Recipient | Selected output and finalized context, independent delivery memory as needed | Duplicate transmission may occur; logical delivery is deduplicated. |
| Test oracle | Frozen plaintext reference and expected scores | Used to check results outside the host/authority path. It is explicitly excluded from a confidentiality experiment. |

[DERIVED authority trust] A reader that trusts a finalization signature without
independent arithmetic/history verification also trusts the authority's
validation. A compromised signer could endorse a substituted output ciphertext;
its credential may then confer indirect decryption through the reader. The
benchmark must inventory this capability explicitly. Absence of a BFV secret at
the authority is not a security claim against active authority compromise.

[OPEN realization] These are data-flow roles on one research machine. Separate
processes/directories do not establish isolation against that machine's operator.
Authentication primitives, actual serialized credentials, and any transport
assumptions must be recorded after implementation. No PQ composition is inherited
from BFV or from the public proof system's separate analyses.

[DERIVED fixture boundary] The frozen utility history is already public. Its
state is reconstructible from those observations and the known update rule;
OS-random encryption does not change that fact. A separate small fresh-input
smoke run must exercise the same integration with issuer-only OS-random vectors
and a trusted oracle. Retain only aggregate comparator outcomes in public
reports, keeping raw vectors, keys and oracle state in ignored private runtime
files. This checks the implemented role data flow, not physical isolation or a
cryptographic security theorem.

## Admission and output contract

[DERIVED requirements] Each authenticated request/finalized record binds genesis,
parent revision and encrypted-state digest, fixed parameter and program version,
Learn/Infer command, route, original encrypted input or public query, recipient,
unique request identifier/nonce, resulting state and selected output ciphertext.
Any randomness field must describe what is actually checked. Binding a ciphertext
does not prove honest encryption coins, plaintext range, or hidden source policy.

[DERIVED requirements] Genesis also pins the BFV public-key digest and the
authorized signing/verification keys. The issuer's trusted configuration selects
that key/genesis; the host cannot supply an arbitrary replacement public key.
Infer authorization covers the exact query, recipient, parent and request nonce.
Merely accepting any correctly shaped query vector is not a privacy policy.
The authorizer's power to approve further informative queries remains a named
credential capability.

[DERIVED requirements] Learn adds the exact admitted input ciphertext, evicting
the exact original oldest ciphertext on that route after capacity is exceeded.
Infer leaves the encrypted learner state unchanged but is a real journal event:
the global revision advances and the window-admission projection does not. Empty
states have an explicit canonical representation; no serializer sentinel is
mistaken for an ordinary ciphertext. A replay must reconstruct the same state
without a secret key.

[DERIVED requirements] Exact retry returns the installed record. Reusing its
identifier with any changed bound field fails. A host-only restore cannot make a
stale parent current. A finalization signature alone must not be confused with
live monotonicity after rollback of its signer. Publication occurs after durable
commit; crash/retry may retransmit the same logical packet. Costs include the
verification, persistence and retained history added by this integration.

## Evidence needed before calling it complete

[OPEN acceptance checks]

1. One documented command builds/runs the complete path from fixed fixtures;
   actual OS-random encryption is distinct from deterministic oracle reproduction.
2. The host and keyless authority execute without receiving any BFV secret or
   plaintext observation. Audit their concrete command arguments and file inputs.
3. Mixed Learn/Infer, actual expiry and exact signed output checks pass through the
   same admission/release path, with source and artifact hashes retained.
4. Altered ciphertext updates, wrong expiry, stale parent, wrong genesis/program,
   recipient/query substitution, unauthorized input and conflicting retry fail at
   their named boundary. An issuer credential only establishes the authority it
   actually has; malformed hidden features are not silently certified.
5. Crash-before-commit, crash-after-commit, retry, competing admissions and host
   restore have recorded outcomes. Rollback of the independent authority is an
   explicit negative control or an explicitly untested assumption.
6. Report setup/update/query/verification/release timing, current encrypted state,
   retained ciphertext/history and credential bytes. Do not reuse standalone HE
   timings as end-to-end costs.
7. Independent review checks that the positive path and rejection controls test
   the claimed relation, and that the trusted reader limitation remains visible.

## Separate masterless comparison

[OPEN] Review the existing finite encrypted continuation tree and the classical
FE ladder. A full authorized trace table can be an exact finite interface
implementation after erasing the original state; its ability to enumerate every
authorized branch must be represented in the ideal interface too. Determine its
actual lifetime, setup cost, hidden distinctions and lack of fresh private ingress.
Do not call a precomputed table an indefinitely adapting encrypted learner, or
call an unimplemented iO assumption an executable restricted-release mechanism.

[DERIVED decision rule] Completing benchmark R is meaningful integration
evidence. Completing a nonvacuous finite masterless comparison is a different
result. Their existence side by side does not prove their cryptographic
composition. The missing construction remains a first-class outcome tonight.
