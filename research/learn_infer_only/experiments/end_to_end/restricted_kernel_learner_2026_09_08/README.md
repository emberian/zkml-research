# Restricted quadratic-kernel learner: fixed utility result

[EXECUTED] The one fixed 32-coordinate map gave **8/16, 9/16 and 10/16**
correct decisions after two, four and six teachings on the unchanged public
slice. The predecessor scored 16/16 at each checkpoint. This successor has
**zero cryptographic runs**: the fixed map's weak utility did not justify a
fresh setup. No feature-map tuning, query reselection or model forward occurred.

[DERIVED] The construction itself fits the unchanged ideal-uniform ring FE
transport. The trusted plaintext issuer applies a 528-coordinate symmetric
quadratic lift, padded to 577. Each registered query row satisfies the exact
integer identity `<φ(x),ψ(q)>=(x·q)²`. Public encrypted class memories still
update by addition and exact expiry. See [CONTRACT.md](CONTRACT.md) for the
identity, complete range argument, setup lifecycle and precisely conditional
privacy claim.

[EXECUTED] [PREPARATION.json](PREPARATION.json) records the sole utility
evaluation, 96 exact kernel identities, rank16 and six basis roundtrips.
[ALGEBRA.json](ALGEBRA.json) records 6,561 additional cross-term controls,
tight boundary cases and a synthetic plaintext issuer CLI check. Those controls
did not reevaluate benchmark utility or run cryptography.

The honest plaintext adapter is reusable:

```sh
python3 -B issuer.py --registry registry.json \
  --input ORIGINAL_SIGNED_INT8_VECTOR.json --out LIFT_RESIDUES.json
```

The source input is the existing 577-coordinate final-zero vector, with 576
cached embedding/projection coordinates. The output is the canonical field
vector for the unchanged transport's `encode` interface. `kernel.py` also
exports `compact`, `lift`, `query_coefficients` and `kernel` as exact integer
functions. `prepare.py` deliberately refuses a second fixture evaluation.

[SOURCE] Owned `basis.py`, `transport.py`, `workflow.py`, `source/fast/` and
`codec/` are byte-identical public source/build copies from the predecessor.
`workflow.py` is an **unexecuted template** for a fresh independent run; this
packet does not authorize launching it. It never points to predecessor private
keys or ciphertexts. A changed registry always requires fresh setup and keys.
`SOURCE_PINS.json` records those origins and the inherited parameter values.

[SCOPE] This is plaintext degree-two feature engineering with encrypted linear
class updates. It neither multiplies ciphertexts nor provides unrestricted
text queries. Every exposed query key remains usable on each retained issued
input; the whole key coalition gets its full registered score span. The data
and expected scores are public, and neither semantic ambiguity nor a concrete
Ring-LWE security level is established here. The observed degradation applies
to this complete fixed projection/quantization/quadratic pipeline; it does not
identify which component caused it or rule out other 32-dimensional maps.
