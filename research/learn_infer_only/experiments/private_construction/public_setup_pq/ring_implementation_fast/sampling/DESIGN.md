# Native proposal screening for the finite Gaussian sampler

[DERIVED implementation, 2026-09-08] The API is unchanged:
`from sampling.sampler import GaussianSampler`; then
`s = GaussianSampler(); coefficients = s.sample(sigma,count)`.
The result is a Python integer list. `s.last_stats` retains the baseline
aggregate fields and adds `native_calls`; `table_seconds` is retained.
The native version accepts positive power-of-two widths through `2^59`,
including the ring widths `1024` and `33554432`. This is variable-time
research code, not a private execution boundary.

## What changed

[SOURCE: implementation, fully read and copied] `reference.py` is a
byte-identical copy of the frozen baseline `../../ring_implementation/sampling/sampler.py`.
Its SHA256 is
`2258da232fb6a3459f58c9842f9560baef7796bacaedfd757a4ae27b37c033dd`,
checked before loading. It supplies the same exact integer Machin/Taylor
thresholds and certified squeeze table. The baseline files were read only.

[DERIVED] `proposal_screen.c` parses blocks of OS random bytes and applies
the 32-bit prefix squeeze in native integer code. It consumes proposals
sequentially, emitting accepted coefficients and enforcing the 4,096-attempt
cap with zero fallback. It pauses at each gray proposal with the coefficient,
prefix and attempt count recorded in caller memory. Python resolves that
proposal using the pinned 256-bit threshold and, only if necessary, a fresh
224-bit OS-random suffix. Native screening then resumes at the next proposal.
No coefficient-dependent threshold cache is retained after sampling.

[DERIVED] The native code has no RNG, clock, floating arithmetic or file I/O.
Python obtains all production random bytes through `os.urandom`. Proposal
blocks contain up to 65,536 words: six bytes at error width or eight at key
width. All random words, coefficients, intermediate state and output lists
remain in process memory; only public source compilation produces files.

## Finite-law refinement argument

[SOURCE/DERIVED] The frozen sampler's `DESIGN.md` proves its prefix thresholds
conservative for its exact finite law, relative to independent unbiased
input bytes. Those arrays and the exact gray fallback are reused here.
For a fixed sequence of proposal words and suffixes, the C branches match
the baseline decisions: reject the negative boundary; accept zero; compare
the prefix with the same lower/upper bounds; otherwise pause for the same
exact threshold test. Both paths increment the current attempt before
deciding, reset it after acceptance, and emit zero after rejection at attempt
4,096. This includes gray rejection at the cap. Attempt state persists across
buffer boundaries. The last accepted/fallback output stops consumption.

[DERIVED] C's signed coefficients fit in 64 bits for `sigma<=2^59`:
`-2^62<=k<2^62`. After rejecting the negative boundary the table index
`floor(|k|*512/sigma)` is in `[0,4096)`. The implementation computes it by
safe shifts, avoiding an overflowing intermediate product. Proposal parsing
uses explicit little-endian byte loads and a power-of-two mask, so it adds
no modulo bias. The 32-bit prefix thresholds are stored in 64-bit words
because their upper endpoint may equal `2^32`.

[DERIVED scope] Increasing the buffer size changes prefetch/discarded bytes,
not the conditional distribution of fresh independent bytes. Thus this
implementation has the same finite output law as the baseline under that
ideal random-bit model, subject to the source/refinement argument. The
baseline statistical certificate transfers on that condition. This argument
is not a formal machine-code proof or a claim that a finite-seed OS generator
is statistically identical to an unbounded independent tape. OS randomness
security, side channels, private memory protection and construction security
remain separate assumptions/work.

## Executed comparison

[EXECUTED] `benchmark.py` and `MEASUREMENTS.json` retain exact source pins,
commands, aggregate test results and timing. Eight public synthetic-tape
cases compare complete outputs and consumption/decision counters against
the frozen Python baseline, including both production widths and the
minimum/maximum native widths. Five forced controls exercise cap exhaustion,
suffix acceptance/rejection, and a gray decision on proposal 4,096. All
passed. The deterministic test tape is confined to the test driver and is
never a production random source. Sample moments only detect gross errors.

[EXECUTED] Four million actual random coefficients were measured: one
million per implementation at each width. The native and baseline calls
were timed in the same process on the same shared machine. Table setup
and compilation were outside each sampling timer; output-list allocation
and conversion were included. No raw samples were persisted.

| Width | Baseline seconds | Native seconds | Measured speedup |
|---|---:|---:|---:|
| `sigma_e=1024`, 1,000,000 coefficients | 7.6447 | 0.7440 | 10.28x |
| `sigma_K=33554432`, 1,000,000 coefficients | 8.2876 | 1.1469 | 7.23x |

[EXECUTED] These are single-run sampling measurements, not whole-construction
speedups. The native calls needed 3,879/4,026 direct threshold evaluations
and 4,124/4,271 native invocations at error/key width respectively. No natural
cap fallback or suffix draw occurred. An earlier 2,000-coefficient native
smoke run also passed; its output aggregates are retained in `RUN.log`.

## Build and handoff

[EXECUTED] The first constructor auto-built `proposal_screen.c` with the
system C compiler, `-O3 -std=c11 -fPIC -Wall -Wextra -Werror -dynamiclib` on
the measured macOS environment. Build output goes only to ignored `_build/`.
`s.library_path` and `s.build_command` expose the native binary and a
reproducible rebuild command. `MEASUREMENTS.json` pins the binary bytes and
source bytes. The first compile used a temporary output filename and atomic
rename; that transient filename was not logged, so `build_command` is not
claimed to be the exact historical argv. Later constructors reuse the binary.

[OPEN] A C compiler is required if the local artifact is absent. Native
memory safety and generated machine code have not received a formal audit.
There is no application memory quota for the requested output list. No
constant-time, secure-erasure, hostile-host or whole-ring security claim
is made. The parent owns the integrated ring run and its result ledger.
