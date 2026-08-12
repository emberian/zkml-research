# The parts that aren't the prover

2026-08-11. A correction to my own triage: I read Relect, said "not zkML," and
moved on — having earlier derived a bound with a term that Relect is a candidate
answer for. Recording the connection and the general point.

## The beacon is a term in our own bound, not a deployment detail

From `notes/audit-sampling-prior-art.md`, the composition nobody in the
literature writes down:

```
q = p·(1 − ε_snd) − ε_bind − ε_beacon
```

`q` is the *effective* detection probability, `p` the nominal audit rate, and
**`ε_beacon` is the adversary's advantage in predicting the audit selection given
the whole transcript through the commitment.** My own note says: *"If the beacon
is a datacenter-local PRNG the adversary can bias, `ε_beacon` swamps `p` and the
theorem is vacuous at any audit rate."*

So the beacon is not infrastructure around the theorem. It is **inside** it. A
verifiable-inference deployment with a great prover and a predictable audit
selector has `q ≈ 0` and proves nothing about exfiltration.

## Relect as a candidate

**Relect** (eprint 2026/1619, Liang, Liu, Wang, Xie, Yu, Zhang — SJTU / Yale /
Yale IC3, 2026-08-06). Single Secret Leader Election via FHE under RLWE.

The property that matters: in an SSLE protocol parties **collectively and
obliviously** elect one leader, and *"parties other than the selected leader
should not be able to learn the identity of the leader unless it is revealed by
the leader itself."* That is exactly the unpredictability `ε_beacon` needs —
selection that the selected party cannot anticipate and others cannot observe.

Why this one rather than the prior art:

- **Removes the trusted setup.** Qelect (USENIX Sec'25), the prior concretely
  feasible lattice SSLE, needs one. Relect does not — and for "everyone deserves
  verifiability," a trusted setup in the audit selector is exactly the wrong
  place to have one.
- **Removes the strong environment assumption** Qelect carries, and allows
  **dynamic leader selection each round** — which an audit beacon needs, since
  the selector set changes.
- **Post-quantum** (RLWE), consistent with the rest of the stack.
- Concretely: 32–2048 parties, **7.15–42.4× faster** than Qelect single-thread
  (7.10–48× at 16 threads), communication **1.14–2× smaller**, end-to-end
  **2.77–345× faster on LAN**, 1.94–17.2× on WAN — *while* removing the trusted
  setup.

Prior art in our own notes that this connects to: **VeriLLM** (from the
audit-sampling lane) already uses a VRF for unbiased node selection and
hidden-state sampling in a decentralized inference design. So the primitive is
already being reached for in this application; Relect is a stronger version of
it with transparent setup.

## The general point

A verifiable-inference system is not a prover. It is at minimum:

| part | what breaks without it | candidate |
|---|---|---|
| prover | nothing to verify | the bf16 block-float plan |
| **audit selection** | **`ε_beacon` swamps `p`; the bound is vacuous** | **Relect / SSLE, VRF beacons** |
| commitment to weights | Hollow-LLM: proofs bind the relation, not the effort | public weight registry |
| commitment to I/O | the adversary picks which outputs to be judged on | Merkle inference ledger |
| the seed | seed-grinding: every proof verifies, payload rides the choice | committed-before-generation |
| distributed verification | one verifier is a single point of trust | federation |

Four of those six are not proof-system work. I have been treating the prover as
the project and the rest as deployment, and that is the wrong shape — the
soundness argument runs through all of them, and `q` is the number where they
meet.

**Nothing here changes the plan's phasing.** Phase 0 is still the prover
measurement. But the threat model should name these as first-class, and Relect
goes in the reading pile as the current best answer to one of them rather than
as an off-topic paper.
