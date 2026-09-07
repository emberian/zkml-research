# Designated-recipient fixed-span continuation

[DERIVED objective, 2026-09-07] Build an actual fixed-policy learner whose
host can encrypt, add and expire contributions and transform a permitted
projection into a recipient ciphertext after the initializer's master has
been erased. The recipient holds dedicated projection credentials, not the
vector master. Join this computation to the existing durable journal and
independently recomputing receiver in a separate implementation. This is a
classical, conditional research demonstration, not a general private resident.

[DERIVED reviewed basis] The [construction review](review/REVIEW.md), SHA256
`a5e199591179cf81a4eb9b3754108eb68a7b1b3d8ba921c4d8b84fb42278d840`,
proves an exact static-coalition view equivalence and identifies setup and
correlated-key obligations. It is the mathematical specification for this
tranche. It makes no novelty claim. The prior-art lane will identify which
source algorithms actually implement numeric projections rather than
inner-product predicate tests.

## Computation and credentials

[DERIVED] Use the existing prime-order DDH group, 577 coordinates, 16 fixed
public query rows, two routes and windows of at most 32 signed contributions.
Keep the actual recorded utility queries unchanged. For each fixed row y_i,
the private initializer derives k_i=<s,y_i> from a freshly sampled master s
and privately delivers that scalar to its recipient. The initializer publishes
h_j=g^s_j and exports no master. Its private erasure, including all copies,
is an assumption; process exit and file permissions do not establish it.

[DERIVED] Each recipient independently chooses a fresh dedicated scalar a_i
and publishes A_i=g^a_i and tau_i=k_i-a_i. Check the public consistency equation
g^tau_i A_i=product(h_j^y_ij). This requires neither a discrete logarithm nor
an undisclosed setup protocol. The private delivery and recipient registration
are trusted authenticated setup actions. The redundant k_i may be retained:
the recipient can already recover it from a_i+tau_i.

[DERIVED] Fresh honest encryption is C=(g^r,h_j^r g^x_j), using independent
private randomness for each input. Exact componentwise multiplication and
division implement insertion and original-ciphertext expiry. The host's
designated output is

```
(C_0, product(C_j^y_ij) / C_0^tau_i)
  = (g^r, A_i^r g^<x,y_i>).
```

[DERIVED] The recipient divides by C_0^a_i, then decodes the fixed bounded
integer interval. For the recorded query rows, the existing public bound is
14,219,936 in absolute value. This bounds honest outputs, not arbitrary
group-valued information obtainable with the exposed credentials. Distinct
state and output envelope types, context hashes, row identity, exact widths,
canonical encodings and subgroup checks must be explicit in the implementation.

## What the privacy statement means

[DERIVED] Host-only input privacy has no fixed-projection compatibility
restriction: its entire token/key package can be simulated from the ordinary
public encryption key. For any fixed recipient coalition J, privacy is modulo
the span of Y_J for **each individual issued input**, including later-expired
inputs. All surviving recipients together recover the full fixed query span.
The reviewed fixed-key adaptive-message DDH reduction applies without extra
advantage loss from the designated transform. Adaptive recipient disclosure
has a separate explicit subset-guess loss, not a free extension of this claim.

[DERIVED] Recipient credentials are dedicated to this construction. If one
recipient's query lies in a coalition's span, that coalition can derive its
scalar a_i. These are not independently protected general-purpose ElGamal
keys. Outputs or timing later disclosed to the host are additional leakage.
The actual demo's role processes share one operating-system account; no
operator-resistant isolation or physical secret erasure is demonstrated.

[DERIVED] The fixed linear learner has a plaintext implementation maintaining
ordered queues of projected records with identical permitted behavior. Its hidden kernel never
affects any of these fixed answers. Matrix rank 16 and ambient kernel dimension
561 do not establish ambiguity on the actual text encoder's image, useful
private cognition, sign-only leakage or unrestricted future private learning.
The full input fixture is public in the useful-workload run. A separate fresh
private illustrative input can demonstrate data flow, not a utility estimate.

## Bounded first implementation tranche

1. [OPEN implementation] `crypto/` owns the dedicated public CLI, private
   initializer/recipient setup steps and a small normal-flow computation check.
   Preserve source/dependency pins, commands, sizes and exact integer outputs.
   No previous crypto or journal implementation is edited.
2. [OPEN integration] `integration/` copies and pins the completed journal and
   independently verifying reader. Adapt their public crypto context and
   recipient credentials explicitly. Genesis binds public rows, tokens,
   recipient, group, context, program and role authentication keys. The receiver
   recomputes the complete accepted history before using only its designated
   scalars to open an output.
3. [OPEN execution] Run a normal 40-Learn/four-Infer/eight-expiry history,
   compare recipient answers with an independent private integer calculation,
   then exercise orderly close/reopen continuation and exact authorized retry.
   Public host logs omit plaintext inputs and recipient answers. Freeze the
   small run before deciding whether to run all 384/96 utility events or live
   text through this new path.
4. [OPEN review] Inspect actual surviving credentials and imports, distinguish
   mathematical construction privacy from implementation evidence, and verify
   pinned artifact inventories. The authority and recipient persistence remain
   separate continuity resources. This tranche does not run new adversarial
   routing, extraction or malformed-input experiments; earlier stopped tasks
   remain stopped.

[DERIVED continuity limit] Journal acceptance and recipient verification bind
the selected execution when those services follow the protocol. A recipient
holding a_i can compute its fixed projections outside its local software gate.
The cryptographic package does not itself enforce finality, quotas or a
single communication channel against a recipient coalition. Removing that
capability requires a different restricted-release construction.

[OPEN broader targets] Post-quantum instantiation, nonlinear protected
learning, changing independent query policies, quantitatively proved private
ingress, actual encoder-image nonvacuity and enforcement of restricted release
against all surviving credential holders remain separate research obligations.
