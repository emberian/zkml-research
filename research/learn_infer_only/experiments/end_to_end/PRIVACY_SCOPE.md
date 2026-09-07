# What the trusted-reader demonstration could establish

[DERIVED scope, 2026-09-07] The integration contract deliberately retains one
full decryption key in a trusted reader. The useful confidentiality target for
this benchmark is the public transcript of an honest validating authority,
visible to an adversarial host or passive observer. Issuers, command authorization,
authority validation and the full-key reader are trusted in this realization.
The stronger all-role exposure game in
`../../SECURITY_GAME.md` remains separate. No execution result is claimed here.

## A conditional transcript argument

[DERIVED proposition] Fix a polynomial-length public command/authorization
schedule, or an adaptive policy whose public choices use only its view so far.
Consider two equal-length streams of private input vectors, with the same public
metadata, sizes, route schedule and admission outcome. Assume:

1. The input encryption scheme has multi-message IND-CPA security for the actual
   parameters, with independent correctly sampled encryption coins. Public
   evaluation and canonical serialization are algorithms on public ciphertexts.
2. All public authorization and finalization objects can be generated from those
   ciphertexts and common public data using setup randomness independent of the
   plaintext challenge. Honest issuer validity/range/feature assertions hold in
   both worlds; they reveal no world-dependent plaintext metadata. Timing,
   resource measurements and side channels from all private-processing roles
   are omitted from this view or have a common efficiently simulatable law.
3. The trusted reader leaks exactly the selected authorized output and common
   public success/failure metadata. Its full secret, decryption timing, internal
   polynomial and rejected-input behavior are outside that idealized view.
4. For every permitted continuation of the adaptive policy, both challenge
   histories produce the same authorized plaintext outputs and admission outcomes.
   Correctness of encrypted evaluation and decryption holds on these admitted
   inputs. Forks, restores, quotas and recipient visibility are the same in the
   two experiments.
5. The plaintext semantics and common output simulator are efficient at the
   declared state width and polynomial operation count. Output equality alone
   does not supply an efficient simulation algorithm.

[DERIVED conclusion] Under these premises, public ciphertext recomputation,
commitment hashing, journaling and independent signing do not themselves add a
plaintext distinguisher. The host/authority transcripts in the two experiments
are computationally indistinguishable, with the underlying multi-message
encryption advantage and correctness failures left explicit.

[DERIVED argument] A reduction given the challenge input ciphertexts can execute
every host/authority operation, hash the same canonical bytes, and sign each
public request/finalization using independently generated authentication keys.
It answers the ideal reader using the common permitted output computed from the
known challenge histories. This produces each endpoint's real transcript when
the correctness and output-compatibility premises hold. A ciphertext hybrid
switches the encrypted inputs while retaining that same output simulator; the
hybrid reader need not decrypt a mixed-world state. Intermediate transcripts are
analytical experiments, not assertions that mixed plaintext histories have equal
outputs. With a one-challenge IND-CPA theorem and m input ciphertexts, the usual
telescoping argument charges at most m appropriately resource-bounded gaps;
the endpoint correctness failures add separately. This reasoning names an
encryption assumption; it does not instantiate it for the current BFV library.

[DERIVED scope] For adaptive fresh-input challenge streams, the premise must
specify an efficient coupled pair generator and establish compatibility on every
reachable public transcript. Pointwise equality on the frozen 96 test questions
is insufficient. If private randomness or correlated private observations are
part of that generator, their joint law belongs in the premise. This note does
not supply that stronger generator or a distributional composition theorem.

## Why the premises matter to the actual code

[OPEN implementation correspondence] Public recomputation is promising because
the authority needs only current encrypted state, the admitted input/query and
the public arithmetic program. It can reconstruct the same output without a
reader secret. The role/path audit must verify that the implementation actually
uses just those artifacts. A signature authenticates the issuer's assertion; it
does not prove plaintext bounds, honest encryption noise or model provenance
against a malicious issuer.

[DERIVED] The reader is an assumption in this argument. Possession of its raw
secret allows decrypting queued inputs and state outside the prescribed API.
Likewise, a public ciphertext key identifier is an assertion until an appropriate
proof or trusted issuance rule relates that ciphertext to the selected key.
Neither a signed receipt nor public recomputation removes these capabilities.

[DERIVED authority credential] If the reader accepts an authority signature
without independently checking the arithmetic and admitted-state history, a
compromised authority can sign a substituted ciphertext as the requested output.
Its signing credential can thereby become an indirect decryption capability.
The current benchmark must assume honest authority validation. Calling this
authority keyless refers only to the absence of the BFV secret, not to security
against its active compromise. A reader that independently verifies the public
computation and input/history authorization would need a separately checked path.

[DERIVED] Authorizing more queries changes the challenge relation. A fixed
shape/range for a query vector is not an information-disclosure policy, and
equality on the illustrative queries is not equality under all queries accepted
by an API. The deployed command authorizer's authority must appear in the same
credential inventory as the full reader.

[DERIVED] The published fixture has no private input uncertainty: anyone with
its vectors can replay the integer update. Fresh OS-random encryption is useful
for exercising real key generation and data flow, but cannot hide a state already
known from that fixture. The separate fresh-input smoke test exercises a stricter
role boundary; it still does not prove operating-system isolation, side-channel
resistance or security against the trusted reader.

## What would improve the vision rather than just this benchmark

[OPEN] A restricted release construction must replace premise 3's trusted
reader with an exposed artifact having a proved restricted computational
capability. Its theorem must compose with admitted private inputs, context,
recipient and continuation. A threshold service would change the trust assumption
to noncollusion; it would still leave a read-all coalition. A hardware reader
would introduce a hardware trust boundary. The finite extensional table and the
conditional FE ladder are separate narrower candidates; neither can be inserted
here without proving the resulting interface and credential lifecycle.

[OPEN evidence] No security bit count or formal security reduction is claimed
for this note. Its purpose is to expose the exact conditional argument that the
concrete benchmark would need, and the stronger obligation it leaves untouched.
