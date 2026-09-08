# Full unique decoding: radius gain, unchanged budgets, and a fair sampled-query proposal

[DERIVED] The useful change is a wider radius with the same algebraic failure term. It does not change the inherited `ErrorBudget` number or the current IR-v2 query ledger. A concrete benefit does appear in the existing ideal coherent-sampling theorem: at the same initial radius, fields, domains and number of folds, a wider tail band supports a larger per-round radius gap and therefore fewer sampled paths. That benefit remains conditional on instantiating the full-UD theorem and the existing theorem's actual premises.

[SOURCE] All declaration addresses and configuration provenance are in `SOURCE_MAP.md`; `source-pins.json` records the inspected bytes. Existing companion source is read-only. VERDICTS remains authoritative and unedited. In particular, the source object named `deployedBudget` is a separate algebraic accounting model from the IR-v2 query column in VERDICTS; this audit does not replace one with the other.

## The threshold changes only one condition

[DERIVED] Put `rho=d/n`. The old generator threshold is `B=(2+rho)/3`; the proposed full-UD threshold is `B=(1+rho)/2`. Thus the open admissible direct radius grows from `(1-rho)/3` to `(1-rho)/2`. At rate `1/2`, these are `1/6` and `1/4`: `delta=1/5` becomes admissible. The full-UD proof still requires positive degree and its integer-radius premise; no endpoint is silently included.

[SOURCE] `ErrorBudget.lean:105–140` uses

```
errStar = n/F
E = (t+k)*k*(n+1)/F + k*v*d_sc/F + q_hash*(q_hash-1)/2^(h+1) + n/F.
```

[DERIVED] Delta appears in none of these summands. Changing its admissibility does not change `t`, which is adversarial FS query/work budget, or any error term. The separate minimum-distance condition in `soundnessError_bound` at line 316 also remains; at `n=2^20,d=2^19`, its exact RS half-distance is `1/4+1/(2n)`, so `delta=1/5` fits if the caller supplies the existing RS distance theorem.

[EXECUTED] `derive.py` reproduces the following fixed-parameter arithmetic exactly; the displayed decimal is a descriptive conversion of an exact rational. Both radius choices give the identical rational expression. BabyBear prime is `p=2013265921`; all points use `n=2^20`, rate `1/2`, `t=q_hash=2^40`, `k=2^8`, `v=20`, sumcheck degree `3`, and hash bits `248` as pinned in the source records.

| source model | fields / existing PoW price | floor of computed bits | dominant summand | effect of full-UD radius |
|---|---|---:|---|---|
| `deployedBudget` | all `p^4`, no PoW discount | 55 | FS grinding | none |
| `secureBudget120` | all `p^6`, existing 20-bit discount | 137 | FS grinding | none |
| `baseGateExt4Fri` | RBR/proximity `p^4`, gate/sumcheck `p`, existing 20-bit discount | 16 | sumcheck | none |
| `ext6GateExt4Fri` | RBR/proximity `p^4`, gate/sumcheck `p^6`, existing 20-bit discount | 75 | FS grinding | none |
| `unifiedExt6` | all `p^6`, 23 gate constraints, existing 20-bit discount | 137 | FS grinding | none |

[SOURCE] The Ext6/PoW rows are arithmetic/resource-model targets, and the mixed base-gate row is explicitly a prospective succinct replacement in its source. Existing field-realization, binding, ROM, PoW and shared-execution obligations are unchanged. This table is not a deployment security upgrade.

## Whole-word and whole-opening consumers

[SOURCE] `proximity_sound_halfThen_UD` first maps radius `Delta` to `Delta/2`, then preserves that tail radius. `committedFri_sound_halfThen_UD` transfers the same result under all-position binding. Both return the unchanged accepted-challenge count

```
m * n0 * F^(m-1), hence probability <= m*n0/F for m>0.
```

[DERIVED] At rate `1/2`, the old whole-word half-then-tail band is `0<Delta<1/3`; full UD widens it to `0<Delta<1/2`. The existing source example uses `Delta=3/10`, tail `3/20`; the proposed example uses `Delta=2/5`, tail `1/5`. Neither theorem contains a sampled-query count to reduce. The source's `friEvent_fsOracle_iff` is syntax transport and does not supply a new FRI ROM theorem.

## Sampled paths require a radius budget at every round

[SOURCE] The actual independent and coherent sampled theorems require, for every round `j`,

```
radius(j+1) + tau <= foldRadius(j),
radius(m) >= 0,
FoldDistanceTransition(..., radius(j), foldRadius(j), b).
```

[SOURCE] Their ideal-binding probability bound is `m*b/F + (1-tau)^qCount`; coherent paths sample initial pair indices independently and uniformly with replacement and use the proved modulo projections. Merkle and FS terms are outside this theorem. No query-PoW discount is present here.

[DERIVED] For one halving followed by preserving tails, use `foldRadius(0)=Delta/2` and `foldRadius(j)=radius(j)` for `j>0`. If every round must afford the same `tau`, the inequalities imply `m*tau<=Delta/2`. The tail also forces `(m-1)*tau<R`, where `R` is its open admissible radius. These are necessary constraints within this particular theorem instantiation; they are not an attack or a lower bound for every FRI analysis.

[DERIVED] Choose the inherited `n0=2^20,d0=2^19`, a binary tower with `m=19`, and final code length `2` / positive degree bound `1`. Nineteen is the maximum number of exact degree-halving rounds with a positive final degree for these inputs. It is a proposed concrete tower instantiation, not an observed runtime setting. Keep initial farness `Delta=2/5` fixed in both comparisons. Set

```
radius(0)=2/5,
radius(j)=(19-j)*tau for 1<=j<=19.
```

[DERIVED] The old band gives `tau<1/108`; the full-UD band permits `tau=1/95`, with first tail radius `18/95<1/4`. The old theorem can spend extra slack at round zero, so it is incorrect to conclude that an initial radius `2/5` was altogether impossible before this port. A simple old interior choice is `tau=1/109`, tail `18/109<1/6`. The script also finds exact interior old choices that attain the best integer query count allowed by its open ceiling, so the primary comparison does not charge the old theorem for a loose radius choice.

[EXECUTED] With the same common challenge bound `b=n0`, exact minimal sample counts for `m*n0/F+(1-tau)^q<=2^-lambda` are:

| challenge field | ideal target lambda | optimal old-band q | full-UD q | paths saved |
|---|---:|---:|---:|---:|
| `p^4` | 55 | 4,099 | 3,603 | 496 |
| `p^4` | 99 | 7,535 | 6,624 | 911 |
| `p^4` | 100 | impossible for this bound | impossible for this bound | 0 |
| `p^6` | 120 | 8,942 | 7,861 | 1,081 |
| `p^6` | 137 | 10,209 | 8,974 | 1,235 |

[EXECUTED] Every chosen q passes an exact rational inequality; q minus one fails even at the old open ceiling or at the new maximum gap, respectively. For the 55-bit old row, `tau=8191/884736<1/108` attains q=4,099. Interior witnesses for every row are retained in `fixed_initial.csv`. The 496-path saving is approximately 12.1% of 4,099, conditional on this fixed ideal theorem and its premises.

[EXECUTED] At `p^4`, the unchanged nineteen-round challenge term has descriptive bit value `99.379634871857`; it alone exceeds `2^-100`. At the 55-bit row the sampling term dominates; at the 99-bit row the challenge term dominates. At `p^6`, its value is `161.193416064507` bits, so sampling dominates the 120/137-bit rows. No query change can cross the fixed challenge ceiling.

[EXECUTED] The artifact also preserves the source-example comparison, changing initial radius `3/10` to `2/5`: 4,810 to 3,603 queries at the 55-bit target. This changes the farness premise and is not the intrinsic same-input improvement. Its one-round rows are controls: with no tail, increasing that radius was already supported by the half-threshold theorem, so those savings cannot be credited to full UD.

## Why existing query headlines do not improve

[SOURCE] `TwoRegimeQueryBudget.survivalSq` already uses full-UD survival `(1+rho)/2`. The current companion constants still match its IR-v2 `(6,19,16)`, recursion `(3,38,14)` and production `(3,38,16)` records. The proposed low-blowup `(2,57,16)` point is recorded separately.

[EXECUTED] The exact current UDR floors remain 34, 45, 47 and 54 bits for those four respective points. At IR-v2, the existing full-UD formula already requires 86 queries for a 100-bit query-only target with 16 query-grind bits. A hypothetical one-third-radius column would require 147, but that was not the current ledger: 147-to-86 is not a new saving. Both endpoint formulas are separate from the strict-band, per-round-gap sampled theorem above. The external zkdtvm calibration row is also unchanged and is not a local deployment point.

[DERIVED] A smaller qCount can preserve the ideal sampled-tower certificate while reducing the number of paths, as the exact rows demonstrate. It does not alter `ErrorBudget` because qCount is absent there. Joining the sampled theorem to that algebraic budget requires matching actual events and executions; summing or taking a minimum of unrelated columns would not perform that proof. No change to shipped query constants follows from this audit.

## Concrete next proposal

[DERIVED] Complete the full-UD consumer first, then instantiate `friAdaptive_coherent_sampled_sound` with the explicit nineteen-round schedule, `Delta=2/5`, `tau=1/95`, and q=3,603 over the `p^4` field at the inherited domain. This is a useful ideal 55-bit sampled-acceptance candidate with a same-input 496-path reduction over the best old-band uniform-gap instantiation. It preserves field size, challenge-count term and every independent budget term; it does not claim the existing prover uses this schedule.

[OPEN] Before treating it as a concrete protocol certificate, supply the actual positive-degree full-UD fold transitions, the complete `FoldingTower`/field/domain and matching query layout, the initial `2/5`-far premise for the intended reduction, ideal-binding or deployed commitment reduction, and the applicable FS/shared-execution theorem. None is replaced by a numerical premise. For the 120-bit route, the source's Ext6/PoW realization and field-split obligations remain additional work. No runtime benchmark, companion edit, VERDICTS edit, or security-label change was made.
