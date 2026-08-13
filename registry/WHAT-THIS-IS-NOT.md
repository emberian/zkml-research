# This commitment is not usable by any proof system

2026-08-13. Written after ember pointed out, correctly, that the shipped
registry is a checksum with a canonicalization spec — and that I described it
as "the anchor everything else references" in the same message where I quoted
its own not-done list saying **"no consumer."**

## The defect

The commitment is SHA-256 over a canonical manifest of per-tensor SHA-256s.
**No prover can open it.** To prove "the weights I used are the ones committed
to `3218eb92…`" a circuit would have to hash ~14 GB of raw bytes internally.
It binds bytes to a name for a human with a downloader; it binds nothing to
any computation a proof could reference.

In our own vocabulary: the artifact is fine on the producing side and
**uninhabited on the consuming side.** The lane flagged this ("no consumer")
and I read past it while calling the thing load-bearing.

## What a proof-consumable weight commitment actually requires

1. **The proof system's own hash and field** — Poseidon2 over
   BabyBear/KoalaBear, not SHA-256 over bytes.
2. **A specified byte→field encoding.** How does an MXFP4 block (E2M1
   elements + E8M0 scale) become field elements? That is a real design
   decision the registry must FIX, not leave implicit, and it interacts with
   the arithmetization: E2M1 values are multiples of ½ and a k=32 block dot is
   an exact ≤13-bit integer, so the natural encoding is not "reinterpret the
   bytes."
3. **A Merkle structure at the granularity the circuit opens** — per row? per
   tile? per block? — because the prover must exhibit *"this row of W is these
   values, against the root"* in-circuit, cheaply, thousands of times.
4. **The same layout the prover reads**, so the committed order and the
   evaluation order agree. Any mismatch is a silent wrong answer.

That is a different artifact. It shares only the streaming/fetch layer with
what was built.

## What survives from the shipped work

- **The range-streaming fetch layer** — real, tested, reusable, and it did
  1.56 TB of structure-mode work without downloading anything.
- **The canonicalization discipline** — a documented, reproducible
  serialization is the right habit and transfers to the real commitment.
- **The gate/teeth methodology** (7 corruption teeth, byte-identical
  reproduction across runs, a stranger's audit with no credentials).
- **A human-facing integrity check**, which is a genuine but much smaller
  thing than what was claimed.

## The correction to make everywhere

**Do not describe the registry as closing, anchoring, or being a prerequisite
for Hollow-LLM until a proof-native commitment exists.** The current artifact
is a checkpoint-integrity tool. Whether the SHA manifest even remains useful
depends on whether anything ever chains bytes → field encoding → Merkle root
through it; if the real commitment is computed directly from the stream, the
manifest is vestigial.
