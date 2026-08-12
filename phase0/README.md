# Phase 0 — de-risking the bf16 exact-table thesis

Measurement harness. **Authors no AIR, no constraint, no gadget, and links no
proof system.** Anything that eventually emits constraints is authored in Lean;
nothing here is a circuit.

```
python3 bf16_tables.py                       # census, domain escape, rank
cd product_exact && cargo run --release      # exhaustive 2^32 product census
python3 cost_model.py                        # two-protocol cost model
```

Captured output is in `results_*.txt`. Substrate accounting is read out of
Plonky3 `p3-lookup` at the rev pinned by `~/dev/breadstuffs`
(`82cfad73cd734d37a0d51953094f970c531817ec`), file `lookup/src/logup.rs`.
