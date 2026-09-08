# Public-seed ring transport: smaller files, separate security assumption

[EXECUTED] The candidate issuer bundle is now **9, 471, 269 bytes**:
`public.json` is 974 bytes and `registry.ring` is 9, 470, 295 bytes. The earlier
ideal-uniform public file was 379, 390, 500 bytes. This is a **40.057 x reduction**
in required public bundle size, or **97.504% fewer bytes**. The full seeded
workflow passed in 138.788 seconds across 45 fresh processes, with all 20
designated outputs matching. Peak actor RSS was 490, 242, 048 bytes.

[DERIVED security boundary] This is a new conditional SHAKE256 seeded
instantiation. It is **not** an information-theoretic compression of the
earlier uniform public setup, and it does not inherit its privacy theorem
merely by invoking hidden-seed PRG security. Both seeds are public. Anyone
can recompute their rows; changing the rows while retaining the seeds changes
an efficiently checkable relation. `SECURITY.md` identifies the complete
seeded-setup proof obligation, including the absent rows.

## What is stored and reconstructed

[DERIVED implementation] The initial605-byte `a.json` descriptor fixes the
parameter profile, public setup identifier, deterministic sparse basis,
recipient indices and a fresh32-byte A seed. A is reconstructed by row index
with domain-separated SHAKE256 and exact rejection into q. Each recipient
generates a fresh private Gaussian row and publishes its actual product.
These16 products remain explicitly packed in `registry.ring`.

[DERIVED implementation] After the complete registry is fixed, finalization
samples a separate fresh32-byte absent-row seed. Its domain binds the exact
A-descriptor hash and the exact registry-file hash. The 974-byte public
manifest embeds the A descriptor and records the absent seed and these
bindings. Thus the final issuer needs only `public.json` and `registry.ring`;
the separate initial `a.json` is not an additional final-bundle dependency.

[DERIVED dependency order] A cannot be bound to the products that depend on
A. Its context therefore binds the fixed policy/parameters before key
generation. Absent-row expansion is bound to the completed registry later.
SHA256 digests implement these bindings; collision resistance is an explicit
computational binding assumption, not an injective encoding of arbitrary
registry bytes. The SHAKE address itself is canonical and length-delimited.

[EXECUTED/DERIVED] The issuer retains reconstructed A and the explicit
recipient registry, then reconstructs one absent P row at a time while
forming its scalar ciphertext component. It discards that row before
expanding the next. No expanded A file or absent-row file is written. No
absent private row is sampled. The reusable expander supports random row
access without expanding earlier rows, using separately addressed fixed
chunks and exact first-accept rejection. It aborts explicitly on its finite
cap; it does not substitute a fallback row.

## Run or reuse

```sh
cd research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_transport
../ring_implementation/.venv/bin/python -B workflow.py --profile toy --run local_toy
../ring_implementation/.venv/bin/python -B workflow.py --profile candidate_full --run local_candidate
```

[DERIVED] Run names must be new. `workflow.py` creates separate OS-sandboxed
actor processes and mode 0600 recipient keys under ignored
`.runtime/<run>/private/recipient_<i>/`. Public actors are denied that
experiment's private tree; each recipient is denied the other recipients'
directories. Actual canary reads exercise the denial rules. Public receipts
record only metadata and output-match Booleans. The orchestrator never opens
private payloads.

[DERIVED CLI] `seed_transport.py --receipt <path>` supplies these verbs:

| Verb | Required main arguments |
|---|---|
| `init` | `--profile candidate_full --out a.json` |
| `register` | `--public-a a.json --coordinate i --key-out key.ring --registration-out registration.ring` |
| `finalize` | `--public-a a.json --registration R ... --registry-out registry.ring --out public.json` |
| `encode` | `--public public.json --registry registry.ring --input X.json --out ciphertext.ring` |

[DERIVED compatibility] Signed combination, exact window expiry and
designated decode use the unchanged sibling `../ring_transport/transport.py`
CLI. The packed ciphertext/key formats and exact integer decoder are
unchanged. Ciphertexts bind the seeded public-manifest hash, which commits
to the registry; the public manifest's format identifies this seeded security
mode. A ciphertext body alone does not assert ideal-uniform setup security.

[DERIVED fresh setup decision] The previous uniform A cannot be recreated
from a compact seed after the fact. Reusing previous recipient rows with a
new A would also publish auxiliary products outside the one-setup proof.
This experiment therefore generated one fresh setup and 16 fresh recipient
rows. It did not change or silently reuse the retained earlier credentials.

## Measured path and limits

[EXECUTED] The full candidate uses N16384, w64, d577, r16 and the same modulus,
Gaussian widths, flood, scalar window and encoding denominator as the earlier
implementation. Three fresh encodes took 11.162–11.439 seconds each;20
separate-process decodes took 1.144–1.268 seconds each. Setup initialization
took 0.133 seconds, 16 registrations70.101 seconds and finalization0.248
seconds. All signed/expiry outputs matched. See `SUMMARY.json`, `REPORT.md`
and `results/candidate001/WORKFLOW.json`.

[EXECUTED scope] Bundle sizes are actual written file sizes and the two
files read by the issuer. This run uses local filesystem transport; it does
not claim measured network bytes or latency. Intermediate registration files
and ciphertexts remain retained separately and are not included in the
final public-key bundle count. Ciphertext and private-key sizes are unchanged.
No benchmark grid, estimator or attack run was added.

[OPEN] The earlier ideal-uniform proof does not automatically cover this
public seeded view. A full joint programmable-XOF reduction, with quantum
oracle programming if QPT/QROM is claimed, or a new direct proof covering
the whole seeded setup is still needed. Correctness and byte savings were
executed; computational privacy was not established. OS/host assumptions,
variable time, expected-time private uniform sampling, authenticated
transport and secure memory remain as in the prior prototype.
