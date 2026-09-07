# Parameter review completion

[DERIVED completion; 2026-09-07] The independent
[review](../../adversarial_review/private_ingress_parameters/REPORT.md) is
folded into `PARAMETER_CLOSURE.md` and its existing audit. Nonempty disjoint
L-bit supports give `|support(P)| <= 2^L-1` and sample-collision gap
`>= 1/(2^L-1) > 2^-L`. Thus L=E also fails: the necessary separating-width
condition is **L>E**. The h=E and rho+lambda_next=E equality caveats remain
limited to those lower bounds. No condition is sufficient for compatibility.

[EXECUTED preservation] `parameter_review_original/` contains byte-identical
copies of the five reviewed files and their original `parameter_hashes.json`.
The original manifest at this directory's top level is retained unchanged as
historical evidence; its original paths now have archived counterparts in
`parameter_review_completion.json`. The reviewed note's identity remains
`f7bce8ced8c8460c13a7fe43dfaffbad8bd644f698303f62dc9497b790858fca`.
Neither the independent review evidence nor the frozen REVIEW/DUAL_MODE
artifacts was rewritten.

[EXECUTED verification] Reran the existing `parameter_audit.py`, retaining
stdout and results. The saved collision example now asserts
`25/32 >= 1/3 > 1/4`. Both sizing-result groups and the other two unchanged
control groups equal their archived originals exactly.
`parameter_review_check.json` records these comparisons and verifies the
prior review/dual-mode manifests. This is a correction to finite distribution
arithmetic, with zero new attack, recovery or extraction experiments.

## One next theorem target

[HYPOTHESIS recommendation] Prove the **terminal joint-output lemma for one
final parent-bound private observation**, using the existing candidate's
binding current parent and a separately switchable next commitment/proof
CRS. Fix one genuine prefix, its possibly unknown state s, its current
commitment C, and one final input pair x0,x1 with distinct next states but
equal terminal answers. For the saved byte-addition/high-bit example,
s=32 and x0=0,x1=1 is a nonvacuous pair. The target compares the final
function's next ciphertext, commitment, public proof and answer jointly
with the entire issued prior/current/terminal key package and the common
prefix snapshots. It is an output lemma for a subsequent current-FE switch;
the differing fresh-input challenge ciphertext is not silently treated as
common auxiliary data.

[DERIVED scoped compatibility obligation] Keep the current C binding and
make F validate the supplied full history relation internally, including
the saved proof/authorization checks. For this single-parent, single-pair
target, an accepted state replacement must have the same semantic s;
invalid states fail against both well-formed challenged observation packets.
An observation-slot replacement is identical across worlds and sees the
same challenged state. Enumerate all four U subsets and all malformed
packets explicitly. This avoids the saved equivocal-current-parent alternate
history witness. It does not compare differing current states or establish
the multiple-parent/multiple-query H=2 theorem.

[HYPOTHESIS concrete reduction to attempt] First switch only the next CRS,
generating every exposed FE program/key from the challenged public CRS and
one honest history. In hiding mode, couple the two distinct next states to
one next commitment by the Groth--Sahai opening transformation. Use its
proof-mode theorem for the same true statement, accounting for the encrypted
history and independent proof coins. Now request the two next plaintexts
in an actual terminal **single-input** FE message game whose only terminal
function is the fixed high-bit reader: its challenge outputs agree exactly.
Generate all earlier FE instances and their issued functions from the
terminal public encryption key and independent local setup coins; the
terminal master secret must never be needed to produce that auxiliary
package. Restore the proof/CRS modes. The same-context ciphertext switch and
this explicit auxiliary-package generator are the proposed theorem's work,
not assumptions named “joint compatibility.”

[SOURCE / OPEN exact proof targets] Groth--Sahai
[2007/155](https://eprint.iacr.org/2007/155), Definitions 4--5 pp.9--10,
the scalar commitment in section 9 pp.24--25, and Theorem 18 pp.34--36
provide the candidate CRS/proof steps for the actual compiled relation.
Datta--Guan--Korb--Sahai
[2025/330](https://eprint.iacr.org/2025/330), Definitions 4.3--4.4 pp.22--23,
Theorem 6.1 p.50 and Lemmas 6.2--6.8 pp.64--66 are the concrete terminal
FE game/reduction to specialize. These sources are pinned in
`dual_mode_sources.json` and `parameter_sources.json`; no theorem in either
source is credited here with this composition.

[OPEN quantitative deliverable] Derive an explicit absolute-gap bound for
that sequence, including CRS switches, proof/sampler errors, all terminal
FE hops, auxiliary-generation costs and the PKE advantage convention.
Ordinary CPA negligibility in Lemma 6.2 will require an explicitly quantified
strengthening to compare the resulting bound with current `2^-E`; the
terminal FE's own exact-output compatibility does not provide that rate.
Specify the general-ellR parameter completion and actual encodings before
claiming it fits the saved sizing family. This single lemma would test the
first concrete joint-package route while leaving the current-state switch,
full H=2 schedule and malicious issuance outside its conclusion.

[EXECUTED accounting] This correction/recommendation used zero web, Scry,
Kagi or schema queries; zero new PDF extracts/downloads; and no new lane,
companion edits, shared-ledger edits or commits.
