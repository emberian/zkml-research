# Semantic successor expander v2

[SOURCE: implementation copied and byte-compared] This is a new version of
`../../ring_seed_transport/expansion/public_expander.py`, frozen SHA256
`ab175083b2a38e382776f07a52a0d8b84e8886085f40f083117de273f0d0aba4`.
Five exact replacements change the protocol to
`b'ring-seed-semantic/public-rows/v2'`, require exactly 48 seed bytes,
update that constructor message/docstring, and point its module note here.
`__init__.py` is byte-identical to the predecessor. Rejection into q, the
finite cap, indices, canonical length-prefixing, word layout and streaming
rows are otherwise byte-identical. The old package was not edited.

[DERIVED interface] Import `PublicExpander` from `expansion`; its constructor
accepts exactly 48 seed bytes and 32 binding bytes. Seeds of 32 or 64 bytes
are rejected. The parent owns the `RINGSSM2`/version-3 container and fixed
`honest-dual-seed-384-qrom-v1` policy. This helper enforces its seed width and
domain; it does not parse or validate that container policy. Public seeds
remain public deterministic expansion inputs, with the predecessor's
security distinctions described in its `SECURITY.md`; changing seed width
alone is not a new cryptographic proof.

[EXECUTED] `check_version.py` checked package imports, constructor widths,
canonical domain bytes, rejection of seed downgrades, version/family/index
separation, and the exact five-replacement source relationship. SHAKE and
chunk generation were guarded against invocation: zero calls, zero expanded
rows and zero setup runs. `CHECKS.json` and `RUN.log` retain the command,
output and hashes. The journal owns the one shared actual full setup; no
private artifact or previous expanded row was read here.
