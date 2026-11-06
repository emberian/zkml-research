# Initiative 13 grounding: the model-identity receipt

Lane: initiative 13 (eval provenance / model identity), opened 2026-11-06. Home of all work:
`/Users/ember/dev/zkml-research/research/model_identity_receipt_2026_11_06/`.
FlashProve read from `/Users/ember/src/FlashProve` at 9e2bdd8f (0.16.0-rc.26, the public release), the one Mac
clone; initiative 8 should read the same clone and not clone again.

## 1. What exists, and what it settles

| thing | where | what it gives this lane | kept / replaced |
|---|---|---|---|
| registry v1 | `registry/registry_tool.py`, `MANIFEST-FORMAT.md`, `gates.sh` G1-G10, 8 checkpoints | range-streaming fetch, canonical-JSON + domain-tag discipline, tamper teeth, rerun byte-identity | **kept**: the fetch layer and canonicalisation; extended to GGUF (v1 knows only safetensors, and the only checkpoint with a FlashProve commitment is GGUF) |
| v1's own verdict | `registry/WHAT-THIS-IS-NOT.md`, VERDICTS §5 | a flat SHA-256 over bytes is a checksum no prover opens; a usable commitment needs the prover's encoding, layout and leaf granularity | **taken as the bar** for v2 |
| v2 design | `notes/moe-router-binding.md` §5.3 (per-expert roots R_{l,e}, verifier-side O(E) MLE over the root vector), D4/D9 | why per expert: expert-swap binding without paying the dense opening | **kept**; re-targeted from DeepSeek/BabyBear to the model and field FlashProve actually commits (below) |
| house hash ruling | `minidregg/board/RULINGS.md` l.22: cSHAKE256 for roots, no algebraic hash for roots | the root hash | **followed** (section 3) |
| hollow-LLM microsite | `dregg-microsites/which-model/index.html` | the public framing: "a public name for the weights" | to be **updated** with a real receipt, and corrected (section 5) |
| dossier 04 §2 | `whatember/sources/04-...md` | the summary of all of the above | read; nothing new |
| Lucid AI Passport | `whatember/LUCID-INTERVIEW-BRIEF-2026-11-05.md` l.21, 45, 115, 133 | their "model identity" is a Tinfoil release digest (an image hash, not a weight commitment); their own post asks for "model/eval provenance graphs rather than single weight hashes" | the receipt is the concrete object that sentence asks for |

Prior art read (2026-11-06, Kagi + arXiv):
- **Hollow-LLM** (Gong, Liu, Li, arXiv 2607.28884): ghost weights keep the declared architecture and size but
  collapse the computation; the proof is valid because it binds *committed private* weights, not effort.
  Consequence for us: a registry binding defeats it **only for published weights** (ghost weights are not the
  published integers). For private weights the receipt can bind "the proving model is the evaluated model", which
  defeats a swap *after* evaluation but not a hollow model that was itself evaluated. Said in the receipt's
  not-claims and in the Lean docstring of `hollow_refused`.
- **OpenSSF model signing** (sigstore/model-transparency, `model-signing` on PyPI): signs an in-toto manifest of
  file digests. Byte identity of files with a signature; no proof-system consumer, no eval binding, no
  quantization edge. We reuse its shape (a signed statement over a manifest digest), not its trust root.
- **Brundage et al. 2026, AVERI** (arXiv 2601.11699): AI Assurance Levels AAL-1..4; higher levels need evidence the
  auditor can check rather than developer assertion. The receipt's legs are typed by who can check them (section 2),
  which is the AAL question asked per edge.
- HF signed commits: GPG signatures on git commits of a repo; they sign a repo state, i.e. the GGUF bytes at a
  revision. One edge of our graph at most.

## 2. The central finding: what "same bytes" means for FlashProve

FlashProve's commitment ID (protocol.md §3, R4.11) is a hash of the configuration (`policy.txt`, `KL.bin`,
`layout.txt`), of the anchor weight table's root and shape, and of the anchor's OOD answers with their seeds. The
anchor table is a **randomised** encoding of the integer weights (random elements added, salted tree leaves). So the
ID is not a function of the weights: two honest commitments to one model differ. There is no shared preimage in the
sense "hash the same bytes, compare digests". What there is, for Maverick, is a chain of three edges, each a
documented deterministic function:

| edge | from -> to | rule | who can check it, at what cost |
|---|---|---|---|
| E1 | HF repo `unsloth/Llama-4-Maverick-17B-128E-Instruct-GGUF` @ 41032e54, folder UD-Q4_K_XL -> 5 GGUF files | SHA-256 per file; FlashProve publishes them in `examples/maverick/weights.sha256` | anyone, CPU, a 232 GB stream |
| E2 | GGUF tensors -> committed integers w (int16, \|w\| <= 4095; embedding int32 at e_res = 10) | FlashProve `docs/model.md` §11, float32 op by op; `weight_sums/` writes per tensor `name elements e bits sha256(ints)`; FlashProve publishes **sha256(wsums.txt) = 689cd1d0...b519** in `expected.txt` | anyone, CPU; we write a second, independent implementation and must hit that digest byte for byte |
| E3 | integers + public seed (`public-seed.bin`) + config -> commitment ID **c7982f8a...7c38** | `cp_commit -public-weights` | only by recomputation, on one H100 with **330 GB host memory**, 43 min; FlashProve reports 1 + 7 reproductions in `examples/maverick/README.md` |

So the binding between our roots and their ID is: **our v2 roots are computed over exactly the integers whose
digest FlashProve published (E2), and those integers are what cp_commit commits (E3)**. E2 is checked by us
byte-exactly; E3 is recomputation-only. Until a machine with an H100 and 330 GB exists for this (ember's decision,
it is money), the receipt carries E3 as an **attested edge**: FlashProve's published expected values plus their
reproduction record, typed in the receipt as "recomputable, not recomputed by us", never as checked. With a secret
seed (the hiding mode), E2's digest is itself secret (`wsums.txt` is "as secret as the weights") and E3 cannot be
recomputed by anyone but the provider: the binding then degrades to the provider's signature. The receipt types
every edge by who can check it, and the Lean theorem quantifies over that typing.

"Same bytes" across quantization: what FlashProve commits is not Meta's bf16 checkpoint and not even the GGUF bytes;
it is the §11 integers of a third party's (unsloth's) 4-bit conversion. Each step is a separate node of the
provenance graph: Meta bf16 (gated) -> unsloth UD-Q4_K_XL (lossy, unsupervised by Meta) -> FlashProve integers
(lossy again: requantised to 13 bits per tensor exponent) -> commitment. An evaluation of Meta's bf16 model does
not transfer along a lossy edge, and the receipt refuses one that names a different node than the committed one.

## 3. Decisions (mine; ember can overrule)

1. **Checkpoint: Llama 4 Maverick UD-Q4_K_XL**, streamed on bb2, not gpt-oss-20b. Reason: it is the only real
   checkpoint with a published FlashProve commitment; gpt-oss is refused by the §11 conversion (the constants hold
   for d = 5120, dh = 128 only), so a gpt-oss root would bind to nothing. Streaming needs no disk: curl -> the tool's
   stdin, file by file; peak memory one tensor (largest ~3.5 GB raw) times the worker count.
2. **v2 root object: the committed integers, in FlashProve's matrix layout**, not the GGUF bytes. Leaf = one row
   (fixed i1, i2) of int16 little-endian two's complement; the map to the prover's field is w -> w mod p,
   p = 2^64 - 2^32 + 1 (Goldilocks), injective since \|w\| <= 4095, so the byte leaf is a field-element leaf.
   Per expert e of MoE layer l: R_{l,e} = node(gate_e, up_e, down_e). Every other committed tensor gets one root.
3. **Hash: cSHAKE256** (SP 800-185) with a customisation string per node kind, per the minidregg ruling. Poseidon2
   rejected: FlashProve computes in Goldilocks but its trees hash with BLAKE2b, so no stack we have opens a Poseidon2
   root over these integers; the ruling's reason (the root hash fixes the opening circuit; open with a boolean proof
   over Keccak) applies unchanged. Nothing opens R_{l,e} in-circuit today: its consumers are the verifier CLI and the
   house's expert-swap binding. Said in the not-claims.
4. **Gates extended:** G11 v2 roots and per-tensor integer digests reproduce from tensors whose raw bytes match the
   GGUF manifest (a second run over a random sample of tensors by range request); G12 our wsums.txt digest equals
   FlashProve's published one; G13 file SHA-256 equals `weights.sha256`; G14 tamper teeth (flip one weight byte,
   one exponent, swap two experts: each changes the named root and is refused).
5. **Lean home: a new Lean-core package** under this directory (`lean/`), no Mathlib, its exe is the verifier CLI.
   Not minidregg `Assurance/`: an umbrella build needs the root's go and 32G, and the receipt needs nothing from it.
   Hashes in the theorems are arbitrary functions; soundness is stated as "the conclusion, or an explicit collision
   in a named hash", so no cryptographic axiom is needed. The executable computes SHA-256 and verifies Ed25519 in
   pure Lean (Nat is GMP-backed) over the receipt's small objects; the 232 GB recomputation is the streaming tool's,
   and its outputs enter as data that G11-G13 check.
6. **The eval record** is an Ed25519-signed statement over (commitment ID, v2 root-set digest, provenance-graph
   digest, the evaluated node, the benchmark spec digest and scores). No lab has signed anything for this model, and
   we cannot run Maverick (no GPU): the L3 receipt's eval signer is a demonstration key, named as such. The real
   case the receipt must handle is shown with Meta's published bf16 scores: an eval over a different node, refused.

## 4. The bar, restated (peer correction)

The bar as written asks for "a FlashProve commitment ID and our roots for the same checkpoint" as if one could
compare them. One cannot: the ID hashes randomness. The bar I set instead: the receipt binds the ID to the roots
through typed edges E1-E3, of which E1 and E2 are checked by a stranger on a CPU against digests FlashProve itself
published, and E3 is either recomputed (H100, 330 GB) or carried as attested and refused by a strict-mode verifier.
`identity_sound` is stated over that typing. L3 = E1+E2 checked on the real 232 GB stream; L3 strict = E3 recomputed.

## 5. What the which-model microsite gets wrong today

It says the registry is the missing public name. By WHAT-THIS-IS-NOT.md, the v1 registry is a checksum no proof
opens, and by hollow-LLM, a name only helps for published weights. The update shows the real receipt, the three
edges, and which of them a reader can check.
