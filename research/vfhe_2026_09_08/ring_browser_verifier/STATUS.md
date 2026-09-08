# Ring public-bundle consumer

[SOURCE] Building a fixed degree-4096 wrapper around the existing saved
`matvec::protocol::public_wire` codec and unchanged `Verifier::preprocess/verify`.
The caller supplies matrix, encrypted input and selected expected output through
the complete statement bundle. All three PCS openings remain required.

[EXECUTED] Complete. WASM built without source-verifier or configuration edits.
The actual saved 64×8192 fused proof passed in 107.983 ms under Node WebAssembly;
changed caller-selected expected output was refused in 31.052 ms at the existing
output-equality gate, before cryptographic verification. Module initialization
was 13.627 ms; module size 575,831 bytes. One genuine/negative pair only; no
proof generation, native fallback or additional verification cycle.

[SOURCE] Upstream WHIR uses ConjectureList; configured level 100 is not
certified security bits. Exact codec/header, all three PCS openings, and fresh
public preprocessing are retained. `BROWSER_PACKAGE.json` freezes the assets;
root owns site integration. Existing browser_verifier and microsite unchanged.
