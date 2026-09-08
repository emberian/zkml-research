# Reusable bit-reversal query transport

[EXECUTED] Two modules, 167 source lines and 15 theorem declarations. Every theorem/helper has an exact `#guard_msgs` axiom pin. The final clean checks are `logs/lean_009.json` and `logs/selvage_005.json`; patch replay and import-boundary checks pass in `verification.json`. Dependencies were reused from the companion cache; this is not a fresh build of that closure.

[DERIVED] `src/Theory/BitReverseFriTransport.lean:13` states `ProjectionTransport`, and `:20` states `QueryTransport`, before proving them. `query_transport` at line 46 establishes

```
reverseIndex (bits-dropped) (index / 2^dropped)
  = reverseIndex bits index % 2^(bits-dropped)
```

[DERIVED] Its premises are `dropped ≤ bits` and `index < 2^bits`. `reverseIndex` is a numeric projection of the existing `BitVec.ofNat` and `BitVec.reverse`; no second bit-reversal implementation is added. `query_transport_composition` at line 55 composes drops, and `binary_coherent_index` at line 63 exposes the exact first-pair seed relation. A bit-reversal equivalence uses the existing involution. The bounded concrete witness maps the 8-bit index 181, after dropping three low bits, to reversed 5-bit index 13; the false raw-modulo answer is refused.

[DERIVED] `src/Selvage/P3FriQueryTransport.lean:16` defines the transported pair seed in the existing `PowerTwoFriLevels` type. The named `ExistingCoherentTransport` at line 19 precedes `existing_coherent_transport` at line 24, which proves the existing `powerTwoRoundIndex` has the runtime shifted/reversed value for every valid dimension, round and full-word query. The actual `ell=20,m=19` premises are inhabited and the wrong untransported natural index is refused. No new tower, field, code, distance or sampling semantics are defined.

[SOURCE / OPEN] The subject is Lean fixed-width/index arithmetic calibrated to the inspected p3 source. A Rust machine-primitive semantics proof, challenger distribution, MMCS opening transport, acceptance-event equivalence, folding arithmetic and security composition are not supplied by this patch. Those boundaries and the finite field checks are in the parent README.

[EXECUTED] Patch: `minidregg-p3-query-transport.patch`, SHA-256 `a853d61feffbe71802b46ddaf086b93a378246116abf429feef5fed870d48bca`. It adds only these two modules and their Theory/Selvage umbrella imports. Source hashes:

- `Theory/BitReverseFriTransport.lean`: `f546b123f49632cbe3284baa23c3f12943529f7c2b8231e87f7ac71b2c2399cf`.
- `Selvage/P3FriQueryTransport.lean`: `9cfbb720613e77e3652c7de8ddf7ebac9e39322ad36e49bf7c43ff6b09f3c176`.

[EXECUTED isolation] Work checkout: `/tmp/minidregg-p3-folding-transport-20260908`, detached at companion baseline `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. New oleans are owned files; existing companion dependencies are read-only inputs through symlinks. Only the selected `src/` modules enter the patch. Failed arithmetic proof attempts, diagnostic-print iterations and the initial missing-olean-path attempt remain in `logs/`. The initial tool-run failure has an explicitly marked transcribed record; all subsequent Lean runs retain exact stdout/stderr and source copies. Frozen tower and companion sources were not edited.
