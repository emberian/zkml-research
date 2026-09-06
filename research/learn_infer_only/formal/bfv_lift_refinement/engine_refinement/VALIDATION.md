# Checked source-arithmetic refinement

[EXECUTED] Run from the read-only companion environment:

```sh
cd /Users/ember/dev/minidregg
lake env python3 /Users/ember/dev/zkml-research/research/learn_infer_only/formal/bfv_lift_refinement/engine_refinement/validate.py
```

[EXECUTED] `validation.json` retains commands, stdout, stderr, exit codes and elapsed times. All pass: original first module, new module with **33 exact axiom pins**, isolated Compiler umbrella importing both, the companion's existing import-boundary script, individual patch applicability and applicability of the two patches together. This is not a full Minidregg build. The companion trees are never written. Failed exploratory builds remain in numbered `build-*.json`; the passing validation is authoritative for the final patch.

[EXECUTED] `validation-summary.json` records final hashes. Source SHA-256: `486e63dc09d79c10858f9b1e37cbf6b7a5b63841c23e8cbb914cc0e2b8b49167`. Patch SHA-256: `de9490c464d332810bd5de79d21fd9b8db03c6bd29f2a28d8de26a78d41114b0`. The first module remains byte-identical at `1abe56f822ba911e85b0697887cf2317eecc990433f460dedc95a3085ccab2fd`.

[DERIVED] Apply `../minidregg-bfv-lift-refinement.patch` first, then `minidregg-fhe-rns-scale-decomposition.patch`. The latter imports the former and places its umbrella import near the top to avoid colliding with the former's appended import. The patch introduces no custom axiom, sorry, native_decide or compiler-evaluation shortcut.

[DERIVED] The new statement proves exact source integer decomposition, fixed-word arithmetic under proved ranges, and the deterministic actual-parameter scalar formula. It also proves the sharp nearest-or-nearest+1 envelope relative to the **source-selected lift**. It does not prove Rust's Shoup arithmetic, slice indexing, NTT implementation, constructor/serialization interpretation or compiler lowering. The retained Rust fixtures test those seams at finite public inputs. The arithmetic envelope must not be used as a verifier that allows either result.
