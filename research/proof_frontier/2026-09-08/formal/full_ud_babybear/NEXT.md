# Integration handoff

[OPEN] Root loads `integration_entry.json`, applies `babybear-full-ud.patch`
after frozen full UD, and imports `Selvage.BabyBearFullUD` in the umbrella.
The source already imports the existing `Selvage.BabyBearExt4` and the frozen
`Selvage.ProximityGapFullUD`; no old module needs modification.

[OPEN] Sampling-budget lane can import the module and use
`Minidregg.Selvage.BabyBearExt4.ext4_card` to replace the actual Ext4
cardinality by p^4. The installed `ext4Fintype` and `ext4DecidableEq` instances
refer to the existing quotient carrier.

[OPEN] Review the remaining premises in README before applying the
probability head: actual domain/tower, failure of correlated agreement or
initial farness, and any commitment/query/random-oracle reduction. No further
work is scheduled within this frozen bounded carrier bridge.
