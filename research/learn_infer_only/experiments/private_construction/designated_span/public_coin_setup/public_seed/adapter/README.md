# Deterministic public seed setup: positive primitive adapter

[EXECUTED] The single source-reviewed attempt passed 33 Learn, four Infer,
one exact expiry and all four integer comparisons in 342.18 seconds. Complete
public replay and evidence closure preceded recipient decoding. See the
[result report](REPORT.md), [public seal](reports/normal_001/public/PUBLIC_COMPLETE.json),
[STATUS.md](STATUS.md) and [NEXT.md](NEXT.md). No retry was performed.

[DERIVED] The adapter instantiates the public derivation with SHAKE256 over
an injective encoding of the complete fresh recipient registry, parameters,
fixed seed, coordinate, role and counter. It uses capped exact bit rejection,
then squares nonzero field elements and reuses the frozen public matrix
completion. This public algorithm creates no scalar master or private
projection delivery. All 16 recipient-owned keys are deliberately generated.

[DERIVED] The [contract](CONTRACT.md) specifies the one33Learn/fourInfer/
one-expiry workload. A separate public process replays all state and output
bytes; complete setup replay and evidence closure precede recipient decoding.
The vectors are known public integers, so this is functionality and setup
provenance evidence, not an encrypted utility or secret-state experiment.

[SOURCE] The [source manifest](SOURCE_PINS.json) pins the new helper/wrapper/
driver, exact copied predecessor files and accepted mathematics. The
[pure helper log](helper_check.log) records the prelaunch public checks.
[SOURCES.md](SOURCES.md) records official references and query accounting.

[DERIVED] The mathematical guarantee remains conditional classical ROM/DDH;
running SHAKE256 does not prove that idealization or QROM security. All
recipients retain their entire fixed per-input projection span, including
expired inputs. Physical timing, shared-OS privacy, selected-answer-only
release and malicious registration remain outside the claim.
