# Session, verifier and notary decisions

2026-11-06. Recommendations, not implementation changes. Paths below are in
`/Users/ember/dev/breadstuffs/` unless absolute. `[READ]` means source or code inspected;
`[MEASURED]` means this review ran the named read-only check; `[INFERRED]` means judgment.
No paid searches were used. Lane transcripts were consulted, including Lane A's final
report (`cv show --frozen 78fef112-a52f-425f-8503-f3fa24ff087c --agent ad5c9bb4 --last 20`).

## 3. Should the published session projection stay public?

**Options:** keep it; remove the current files while preserving history; rewrite history.

**Recommendation — remove it from the current tree, including its revealing derivatives;
do not rewrite history on the evidence inspected.** [INFERRED] Make the already-built
synthetic variants the public default. Preserve the real experiment privately and its
aggregate findings in public prose. This does not undo the disclosure: old commits,
clones and previously published pages may retain it. Audit derived facts, certificates,
receipts and page payloads rather than removing only `transcript.json`.

[READ] `demo/datalog-governance/project_transcript.py:39` retains tool-use identifiers,
timestamps and file paths; `:69` also publishes the session identifier and hashes of
full redacted exports. [MEASURED] A schema-only Python read of
`demo/datalog-governance/data/transcript.json` counted 73 transcripts, 3,382 calls and
871 calls containing paths; no message contents or individual paths were printed.
[INFERRED] Paths disclose workspace structure, project relationships and subjects named
in files; names can be sensitive even without contents. Timestamps expose activity
patterns. Session, agent and call identifiers are correlation handles, not automatically
credentials; together with spawn edges they expose the work graph. Export hashes let a
holder of another copy confirm a match.

**Salted commitments deserve a different answer.** [READ]
`grain-session/src/lib.rs:265` derives each call's secret salt from a 32-byte owner
secret and call identity; `:278` hashes the salt with length-delimited input and result.
But `CallPublic` at `:73` still publishes paths, timestamps and identifiers, and `:315`
binds those fields into each window leaf. [INFERRED] The hiding commitment does not hide
those accompanying fields. Publish a deliberately minimal commitment artifact only
after reviewing its metadata; retain a fresh per-session master secret privately.
Leaking that master exposes every derived salt; reusing it and call identities permits
cross-publication linking. A window root does not establish that the original host log
was truthful.

**Are synthetic data enough for every demo?** No. [READ]
`demo/datalog-governance/README.md:6` already has deterministic violating/fixed examples.
[INFERRED] They suffice for the policy checker and tamper demonstrations, but cannot
substantiate a real `cv` integration or real HTTPS transport. Run a new, intentionally
public session and real GLM call tree with harmless inputs for those claims; keep the
historical session as private integration evidence.

**What changes my mind / wrong-cost:** keep a particular real artifact if it adds a
specific result synthetic data cannot and ember deliberately wants that disclosure.
Rewrite history if review identifies exposed credentials, private third-party data or
especially sensitive filename contents; rewriting alone cannot recall clones. Removal
costs convenient reproduction of this exact historical run. Keeping unnecessary
metadata imposes a lasting privacy cost.

## 4. Should R3 use a single-tick grain descriptor and new verification key?

**Options:** keep the honest model-head demonstration; change executor nonce semantics;
build a descriptor that proves the executor's actual transition.

**Recommendation — build the faithful descriptor and rotate its verification key.**
[INFERRED] The approved flag day removes the reason to treat this as a preference
question. Keep old receipts explicitly versioned as model-head receipts, not as proofs
of the new relation. Do not change executor semantics merely to fit the old prover.

[READ] `grain-turn/src/finalize.rs:28` explains the mismatch: one executor turn updates
several fields but advances the nonce once; the EffectVM advances it per effect.
`turn/src/executor/execute.rs:661` places fee debit and nonce advancement in turn-level
Phase 1. `finalize_session_threaded` at `finalize.rs:286` threads the modeled state,
yielding a foldable chain whose nonce differs from the ledger (`:277`). It therefore
solves continuity, not state fidelity.

[INFERRED] Specify the grain transition once: permitted field updates, preserved
fields, authority/capability and fee invariants, exact pre/post commitment encoding,
and a single nonce increment with its actual overflow behavior. Generate the
descriptor and witness from that specification, bind it to the new key, and test a
multi-turn sequence against captured executor states. Refuse mutations of the nonce,
each changed field, unchanged state, ordering and descriptor/key identity. A passing
fold alone is insufficient.

**One adjacent gap must be included.** [READ] `grain-turn/src/lib.rs:274` assigns the
call-tree commitment to `ATTESTATION_SLOT = 8`; `finalize.rs:96` and `:209` explicitly
refuse that slot because the old AIR state carries only eight field slots and the rest
falls into its authority residue. [INFERRED] The new descriptor must faithfully carry
slot 8 or its residue update before claiming call-tree R3 composition. Fixing only the
nonce would leave the attested call-tree route unable to finalize.

**What breaks:** [INFERRED] descriptor identities, verification-key pins, shape-dependent
setup results, old aggregates and their golden fixtures. Reissue the new version's
receipts and renter anchors. Reuse the verify-only interface from
`grain-session/GROUNDING.md:66`, with a key independently derived or pinned by the
verifier, never accepted merely because it appears in the bundle. Fewer legs might
reduce proving cost; this review did not measure that.

**What changes my mind / wrong-cost:** if the product intentionally attests only to a
derived EffectVM execution, the current model is an adequate named claim. That is
weaker than the stated real-ledger R3 goal. The risk of the change is circuit and
integration work plus invalidated fixtures; the risk of postponement is advertising a
proof about a different state machine.

## 5. Should a Linux Lean seed be published, and how?

**Options:** require each verifier to build from source; publish a current-source
Linux seed on demand; restore automatic publishing on every change.

**Recommendation — publish a current-source Linux seed on demand, with authenticated
build provenance; keep source rebuilding available.** [INFERRED] Do not restore the
cron or push trigger. The seed is an ordinary platform-specific compiled verifier
archive, not secret setup material.

**The stated absence is stale.** [MEASURED] An unauthenticated GET of
[`releases/tags/lean-seed`](https://api.github.com/repos/emberian/dregg/releases/tags/lean-seed)
returned HTTP 200 with 154 assets, all named for Linux, on 2026-11-06. The newest archive
listed was `libdregg_lean-Linux-x86_64-v4.30.0-0cf8f1b585f6a18f.a.zst`, updated
2026-08-11, 39,569,367 compressed bytes. Thus `grain-session/GROUNDING.md:16`'s
“No Linux seed is published” cannot be carried forward. A missing current-source
asset is a different problem from a missing release.

[MEASURED] Running `bash scripts/lean-seed-key.sh` read-only, then recomputing its
four-line SHA-256 key with platform `Linux-x86_64`, found 365 in-tree closure modules
and expected asset `libdregg_lean-Linux-x86_64-v4.30.0-c5b665e744919694.a.zst`.
That name was absent from the release API's asset list. This is a working-tree
snapshot while other lanes are editing; recompute at the chosen release commit.

[READ] `scripts/lean-seed-key.sh:9` keys assets by platform, Lean version, mathlib
revision and the FFI source closure; `:28` deliberately hashes working-tree contents.
`.github/workflows/lean-seed.yml:80` preserves ember's explicit removal of automatic
builds and provides manual dispatch at `:85`. Its existing pipeline rebuilds the
closure, checks required exports and runs a strict Lean-backed smoke test before
publishing. Reuse it on the designated build host under its resource controls.

[INFERRED] Pin the source commit, complete dependency manifest, native compiler and
archive-tool versions, build flags and platform; publish these with full artifact
SHA-256. Add GitHub/Sigstore build attestation, verified against the expected repository
and workflow identity, or a release signature under a separately pinned maintainer
key. [READ] GitHub's
[artifact-attestation guide](https://docs.github.com/en/actions/how-tos/secure-your-work/use-artifact-attestations/use-artifact-attestations)
documents signed build provenance and `gh attestation verify`. [INFERRED] A checksum
downloaded beside an archive is not independent authentication; signing does not prove
source equivalence. Demonstrate that a second build reproduces the bytes, or publish
the exact differences and avoid claiming bit reproducibility.

[READ] `scripts/fetch-lean-seed.sh:165` has a missing-checksum warning path that proceeds.
[INFERRED] Publication consumers should fail closed on missing/mismatched checksum or
provenance and on absent Lean exports. Test a fresh Linux consumer with
`DREGG_REQUIRE_LEAN=1`, including one real accept and one refusal through the FFI, not
just symbol presence. Never silently fall back to the Rust-only marshal path.

**What changes my mind / wrong-cost:** a small standalone Lean verifier with equally
strong provenance could replace the large archive later. For now, withholding it
makes stranger verification unnecessarily expensive. Publishing a stale or substituted
archive is worse than an explicit build failure; an uncontrolled publication schedule
also repeats the documented host-contention problem.

## 11. Whose notary should the call-tree demo use?

**Options:** ember's separate bb2 process; an independently controlled operator;
let the recipient run the MPC verifier themselves.

**Recommendation — target an independent operator for the public evidentiary demo;
use bb2 to develop and reproduce it, labeled “ember-operated notary.”** [INFERRED]
Independence is control of the signing key and execution, not a second hostname.
Choose an operator the intended verifier accepts, who keeps the key outside ember's
accounts, does not let the prover upload arbitrary signing code, and runs the
agreed MPC mode. Alternatively the recipient can participate directly as verifier.
No unsolicited operator contact is authorized by this recommendation.

[READ] `calltree/GROUNDING.md:12` reports that the old roundtrip helper spawned the
notary inside the prover process; moving it to bb2 removes that immediate co-residence.
`GROUNDING.md:28` and the primary
[TLSNotary introduction](https://tlsnotary.org/docs/intro/#tls-verification-with-a-general-purpose-notary)
say a transferable notarization is accepted by parties who trust that notary.
The protocol's soundness requires the notary not to collude with the prover.
[INFERRED] On bb2, a stranger still trusts ember not to fabricate both sides. Separate
processes improve deployment fidelity and accident isolation but do not establish
independent testimony about ember. An independent operator removes that common
controller, but the stranger still trusts that operator's key custody, implementation
and non-collusion; this is not trustless verification.

Keep today's decisions: GLM through the coding-plan endpoint and verifier-pinned
self-signed certificates. [INFERRED] A pinned certificate authenticates the chosen
tool server, not the truth of its replies. GLM transport evidence authenticates the
provider endpoint's returned bytes, not the model identity or correctness of an
inference. The notary key and server pin must arrive through an authenticated channel
outside the proof bundle. Keep authorization secrets redacted.

[READ] `calltree/GROUNDING.md:65` distinguishes transport authenticity and tree binding
from completeness: the agent can bypass the recorder. [INFERRED] Neither operator
choice proves no omitted outside calls, external factual truth or freshness without
an explicit time/challenge rule. The public claim should be “these authenticated
responses and checked dataflow edges form this committed tree,” with the named
notary assumption. It should not be “every action was captured.”

**What changes my mind / wrong-cost:** if the immediate demo's only claim is that the
components run, bb2 suffices and need not wait for an operator. If the recipient wants
actual third-party evidence, independent operation is part of the experiment, not
cosmetic polish. The cost is coordination and availability dependence; the cost of
using bb2 without the qualification is a persuasive-looking proof that adds no
independent witness against the party producing it.

## Read-only measurement record

The following output was kept from this review. The first command printed only
schema and aggregate counts; individual session identifiers and paths were not
printed or copied into this report.

```python
import json
p = '/Users/ember/dev/breadstuffs/demo/datalog-governance/data/transcript.json'
d = json.load(open(p))
rows = [c for t in d['transcripts'] for c in t['calls']]
print(len(d['transcripts']), len(rows), sum('path' in c for c in rows))
# 73 3382 871
```

Release inventory (Python `urllib.request.urlopen`, unauthenticated, no files downloaded):

```text
GET https://api.github.com/repos/emberian/dregg/releases/tags/lean-seed
HTTP 200 assets 154 linux_assets 154 published_at 2026-07-16T22:12:59Z
latest archive: libdregg_lean-Linux-x86_64-v4.30.0-0cf8f1b585f6a18f.a.zst
size: 39569367; updated_at: 2026-08-11T21:53:01Z
```

Current-source match check (read-only; same key construction as the script):

```python
import subprocess, hashlib, urllib.request, json
r = subprocess.run(['bash', '/Users/ember/dev/breadstuffs/scripts/lean-seed-key.sh'],
                   capture_output=True, text=True, check=True)
d = dict(line.split('=', 1) for line in r.stdout.splitlines() if '=' in line)
k = hashlib.sha256(('Linux-x86_64\n' + d['LEAN_TOOLCHAIN'] + '\n' +
    d['MATHLIB_REV'] + '\n' + d['DREGG_CLOSURE_HASH'] + '\n').encode()).hexdigest()[:16]
a = 'libdregg_lean-Linux-x86_64-' + d['LEAN_TOOLCHAIN'].split(':')[-1] + '-' + k + '.a.zst'
u = 'https://api.github.com/repos/emberian/dregg/releases/tags/lean-seed'
v = json.load(urllib.request.urlopen(u))
print(d['DREGG_CLOSURE_MODULES'], a, any(x['name'] == a for x in v['assets']))
# 365 libdregg_lean-Linux-x86_64-v4.30.0-c5b665e744919694.a.zst False
```
