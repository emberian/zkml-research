# Native AIR → quotient → PCS facts for canonical001

[SOURCE] Read-only source inspection; no native execution in this note. Plonky3
paths below are relative to
`/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/`;
the actual patched FRI source is
`/Users/ember/dev/breadstuffs/vendor/plonky3-fri-82cfad73/`.
The IR2 interpreter is
`/Users/ember/dev/breadstuffs/circuit/src/descriptor_ir2.rs`.

**Critical scope gap.** The approved query template has 2,744 ordinary `gate`
bodies. The actual interpreter multiplies every one by `is_transition`
(`descriptor_ir2.rs:4086`), so none constrains the final base-domain row. The
exact-public lookup runs on **every** row with multiplicity one
(`descriptor_ir2.rs:4340`). There is no row-order gate in this template. An
acceptance-to-all-8,192-arithmetic-rows theorem therefore needs a repaired
whole-domain emission or a restricted conclusion. An honestly generated trace
satisfying every row does not remove this gap.

[EXECUTED subsequently] The separately authorized
[`native_terminal_control`](../native_terminal_control/README.md) confirms this
with one last-row output-digit mutation and a fully verified old-backend proof.
The generated whole-domain repair refuses that row in the actual native gate
evaluator. The original source/proofs were not modified.

## Exact admitted shape

[SOURCE/DERIVED] `instance_airs` at `descriptor_ir2.rs:7108` creates, in order:

1. `Ir2Air::Main`, descriptor `bfv_actual_query_two_products_subtraction`, width
   2,509. Its template contains one arity-57 exact-public lookup followed by
   2,744 gates (2,244 quadratic bodies and 500 linear bodies, counted by a
   standard-library JSON expression-degree walk). No hash sites, ranges,
   challenge gates, public values or other instance families are present.
2. `Ir2Air::LeanTable`, emitted member `dregg-ir2-exact-public-a57-v1`, main
   width 1, preprocessing width 59. Its one whole-domain gate is
   `main[0] - prep[58] = 0`; it provides `[prep[0],...,prep[57]]` with negative
   multiplicity `-main[0]` on bus `ir2_exact_public_a57`.

The family is selected from
`breadstuffs/circuit/descriptors/table-airs/dregg-ir2-exact-public-v1.json`, member
index 56; `exact_public_lean_instance` at `descriptor_ir2.rs:7055` checks its
width and supplies the descriptor-rebuilt matrix `[table_id, tuple57, mult]`.
Here table ID is 11 and all 8,192 rows are distinct through their public row ID,
so each multiplicity is one. Public values are `[]` for both instances; output
binding is through this rebuilt exact-public manifest, not a public-value slot.

[EXECUTED previously] The saved canonical transcript encodes two instances,
each with committed degree bits 14, base degree bits 13, and eight quotient
chunks. Their constrained trace domain is `H13` (8,192 rows). Hiding randomizes
the main and auxiliary polynomials to degree below 16,384 and the corresponding
LDE has 131,072 values. Native `validate_degree_bits` and the shape checks are
in `batch-stark/src/verifier/mod.rs:90–274`; the general IR2 verifier rebuilds
AIRs from the descriptor but normally obtains heights from the proof
(`descriptor_ir2.rs:7714`). The separate canonical profile additionally fixes
the observed heights.

The symbolic maximum constraint degree is three (transition-filtered quadratic
gate / LogUp constraint); the quotient sizing adds the hiding adjustment one,
then uses `ceil_log2(4-1)=2`. The total chunk count is `2^(2+1)=8` per instance.
See `batch-stark/src/symbolic.rs:44–94` and `verifier/mod.rs:118–138`.

## Acceptance equation and ordering

[SOURCE] Name the native batch constraint-folding challenge **gamma**, to avoid
confusing it with the later PCS reduction alpha. Each call to `assert_zero`
updates `A := gamma*A + C`. Main AIR constraints are evaluated in descriptor
order, followed by the LogUp constraints (`lookup/src/protocol.rs:64`;
`uni-stark/src/folder.rs:215`; `lookup/src/folder.rs:174`). Thus for emitted
constraint list `C_0,...,C_(m-1)`, `A=Σ gamma^(m-1-j) C_j`.

There is one global lookup in each instance. With lookup challenges `a,b`,
tuple compression is Horner order `Σ tuple[j]*b^(57-j)` for the 58-field
`[table_id,tuple57]`; denominator `D=a-compress_b(tuple)`. Main signed
multiplicity is `+1`; serving-table signed multiplicity is `-main[0]`.
For local/next auxiliary values `s,s_next` and declared global sum `c`, the
three appended constraints are, in order:

```
L_first(zeta) * s
T(zeta) * ((s_next-s)*D - multiplicity)
L_last(zeta) * ((c-s)*D - multiplicity)
```

There are therefore 2,747 folded constraints for main and four for the exact
table. For `H=H13`, native selectors are
`Z_H(z)=z^8192-1`, `L_first=Z_H/(z-1)`,
`L_last=Z_H/(z-g13^-1)`, and **`T=z-g13^-1`**. These selectors are not normalized
to equal one on their support. See `commit/src/domain.rs:262` and
`lookup/src/logup.rs:158–251`.

For each instance the native final check is exactly

```
A_i(zeta) / Z_H(zeta) = Q_i(zeta).
```

It runs **after** successful PCS verification. After both instance equations,
the verifier checks that the two global cumulative sums add to zero.
See `batch-stark/src/verifier/mod.rs:500–658` and `verifier/data.rs:65–122`.
These are sampled OOD equalities, not an unconditional proof that every
constituent constraint vanishes. A full implication still needs the relevant
polynomial, lookup-denominator, challenge and PCS assumptions.

Quotient recomposition uses eight cosets `D_j=31*g16^j*H13`, `j=0,...,7`,
partitioning `31*H16` (65,536 points). Each chunk's four base-coordinate
polynomial evaluations are themselves Ext4 values at zeta. If `u` is the
extension basis generator (`u^4=11`), native recomposition is

```
q_j(zeta) = Σ_{k=0}^3 u^k * q_jk(zeta)
w_j(zeta) = Π_{l != j} Z_Dl(zeta) / Z_Dl(first_point(D_j))
Q_i(zeta) = Σ_{j=0}^7 w_j(zeta) * q_j(zeta).
```

Here `Z_D(z)=(z/shift_D)^8192-1`. It is coset-Lagrange recomposition, not
simple coefficient-chunk powers. Source: `uni-stark/src/verifier.rs:59–95`,
`batch-stark/src/verifier/mod.rs:356–406`, `commit/src/domain.rs:180–210`.
The hiding PCS commits randomized degree-below-16,384 chunk polynomials while
correlating their masking terms to preserve this recomposition; see patched
`fri/src/hiding_pcs.rs:189–281`. The verifier applies the same recomposition to
the opened randomized chunks.

## Values already retained; no rerun needed

[EXECUTED previously] Canonical data are in
`research/vfhe_2026_09_08/query_runtime/acceptance_bridge/replay001/fri_view.json`,
SHA256 `54603401e8b4271d191800897fae65165c29afb0a8bca43c16317ebf1c0adc41`.
The fresh `canonical001` event stream is byte-identical to that replay. In the
view, `transcript[].seq` identifies these canonical Ext4 coefficients:

| Value | Source sequence | Canonical coefficients |
|---|---|---|
| Lookup a | 46–49 | `[632971636,1531015613,781877436,732917928]` |
| Lookup b | 50–53 | `[755350058,322011459,899795022,301613717]` |
| Gamma | 63–66 | `[798864378,1010459368,194653140,1062467055]` |
| Zeta | 69–72 | `[299587264,1986025030,1329228027,1315399545]` |

Main and preprocessing roots are observed at 36 and 45 before lookup sampling;
permutation root and cumulative sums at 54–62 precede gamma; quotient and
randomization roots at 67 and 68 precede zeta. The later PCS alpha is sampled at
21160–21163 after all claimed evaluations. Exact scheduling source is
`batch-stark/src/transcript.rs:27–144`.

`batches[2].matrices[8*i+j].points_and_values[0].values[0:4]` are the four
quotient coordinate openings for instance `i`, chunk `j`; the remaining four
values in each row are hiding codewords. Main openings are `batches[1]`, public
table preprocessing `batches[3]`, and permutation coordinates `batches[4]`.
The two cumulative sums are transcript 55–58 and 59–62. All needed values are
already present; new proof deserialization is unnecessary.
