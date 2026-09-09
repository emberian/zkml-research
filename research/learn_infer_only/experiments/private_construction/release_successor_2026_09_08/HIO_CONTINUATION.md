# Trying the ACE splice: an exact retained-boundary obstruction

[DERIVED, 2026-09-08] This continues the frozen `HIO.md` construction attempt.
A direct input-side splice using the inspected HIO paper's actual ACE wrappers
has polynomial total size and correct bounded continuation behavior. It fails
the retained-parent/child privacy target on the concrete margin witness: an
exposed old boundary is a deterministic, publicly computable fingerprint of
the private new command. This is a complete algorithm-level obstruction for
the splice below, not another counterexample to an abstract implication and
not an attack on a fully specified construction in the paper's Section7.
The paper sketches input composition without specifying that retained-view
construction. Public certificates can authenticate this splice but cannot make
its honest transcripts private. The separate provenance result applies instead
to the bounded ordinary-iO wrapper whose old internal wires remain private.

## 1. Exact source properties used

[SOURCE] In eprint2023/925, Section3.1, printed p7, ACE `Enc` and `Dec` are
deterministic; setup and key generation are randomized. Decryption correctness
is perfect. Section3.1 p8 additionally requires unique valid ciphertexts.
Section5.1, pp12–13, defines the concrete HIO blocks. A first block evaluates
its underlying circuit on input `x` and emits

```
A(x) = ACE.Enc(EK, (x, C(x))).
```

[SOURCE] An intermediate block decrypts `(x,v)`, evaluates the next circuit,
and encrypts `(x,vprime)` under the next boundary key. The raw final block
decrypts and returns `(x, final_value)`. Public `Eval` subsequently discards
`x`. These input fields support the input-by-input security proof in
Section5.2. Section7 p29 sketches input composition and chain merging but
does not specify the algorithms below or a retained-parent/child game.

[DERIVED injectivity] For any fixed honestly generated unrestricted ACE key,
`Enc(EK,m0) = Enc(EK,m1)` implies `m0=m1`: applying the corresponding
deterministic correct decryption yields both messages. Consequently, because
the first field is `x`, `A(x0) != A(x1)` whenever `x0 != x1`, regardless of
whether `C(x0)=C(x1)`. Deterministic encryption makes this fingerprint
reproducible. The source's additional unique-ciphertext property is not needed
for this particular inference.

## 2. Full polynomial-size splice attempted

[DERIVED setup] Fix the same canonical Step, command codec, horizon `T` and
replay circuit `R_s^T` as in `HIO.md`. For a concrete nontrivial source parent,
initialize

```
Parent_0 = HIO.Compose(HIO.Obfuscate(R_s^T), Identity).
```

Its two public blocks are the source's obfuscated first encryption block
`Dhat_0` and final decryption block `Dhat_1`. Ordinary evaluation returns
`R_s^T(h)`. In particular this initialization does not give out raw ACE keys
or plaintext state. Pin the root bytes and public policy as genesis.

[DERIVED public object] Represent a later object by a depth `d` and its list
of public block encodings. The final source block still returns a pair whose
second field is the replay trace from the root. The public evaluator runs
the list, takes that second field and drops its first `d` releases. Inputs
must be canonical tapes of length at most `T-d`. The removed releases are
the already authorized releases on this object's ancestry.

[DERIVED private issuance algorithm] Given an authentic depth-`d` parent
`(Dhat_0,...,Dhat_k)`, `d<T`, and one valid private command `cmd`:

```
Splice(parent, cmd; fresh_coins):
    validate parent context, depth and canonical command
    y = first release of EvalParent(parent, [cmd])
    SKnew = ACE.Setup(lambda)
    EKnew = ACE.GenEK(SKnew, empty_constraint)
    DKnew = ACE.GenDK(SKnew, empty_constraint)

    F_cmd(h):
        reject invalid h or len(h) > T-d-1
        x = canonical_prepend(cmd, h)
        return ACE.Enc(EKnew, (h,x))

    G_parent(c):
        (h,x) = ACE.Dec(DKnew,c), or reject
        return iO.Eval(Dhat_0,x)

    Fhat = iO.Obfuscate(padded(F_cmd))
    Ghat = iO.Obfuscate(padded(G_parent))
    child = (depth=d+1, blocks=(Fhat,Ghat,Dhat_1,...,Dhat_k))
    publish (y,child)
```

[DERIVED correctness] On a valid `h`, the first two new blocks produce
`Dhat_0(cmd::h)`, exactly the old first block's output on the required parent
input. The unchanged old suffix therefore computes the old trace on
`cmd::h`. Increasing the metadata depth by one removes precisely the extra
first release. Thus the child computes the bounded residual replay function.
All rejection rules are public and fixed; the obstruction below uses only
valid inputs and honestly generated ciphertexts, so extra malformed-input
checks do not affect it.

[DERIVED total size] Each issuance performs one ACE setup, two key generations
and two iO calls. It adds one block net: a new direct first block replaces the
old first block, which is embedded once inside the new adapter. After the
first splice, the first block is always a direct obfuscation of `F_cmd`; it
does not contain the entire parent list. Old adapters are subsequently left
untouched. At fixed `T`, command width and security parameter, each new adapter
therefore has bounded nesting depth. The total distinct block storage and
evaluation work are polynomial in the number of splices and source circuit
sizes. Copying each entire version into an archive can add a quadratic list
overhead; sharing immutable public block encodings avoids that duplication.
These are asymptotic algorithm bounds, not measurements of an iO backend.

[DERIVED complete credential lifecycle]

| Item | Holder and disposition |
|---|---|
| Initial state and unobfuscated root | The initializing state owner; excluded from later host exposure. |
| Every public block and every old parent | Host and recipients; retained and freely evaluable. |
| New command | Its private issuer; not disclosed to the host if that command is protected. |
| `SKnew, EKnew, DKnew` and compiler coins | Fresh per issuance; used to create the two wrappers and not published. Their raw copies must be retired for command privacy. |
| Bound continuation object | Public list, depth and policy context; no secret master is needed for a later splice. |
| Parent certificate | Public provenance of the exact object and policy, if the certificate mechanism is added. |

[DERIVED] The failure below occurs even with perfect retirement of all those
raw secrets and perfect parent authentication. It is not caused by retaining
a forgotten encryption master.

## 3. A perfect two-command distinguisher

[DERIVED retained-view adversary] Let the parent be the initial two-block
source chain, so its first block is
`A(x)=Enc(EK,(x,R_s^T(x)))`. Fix distinct admissible commands `cmd0,cmd1`
and a common admissible residual tape `h`. The host receives the parent and
an honestly spliced child for one hidden command `cmd_b`. It computes

```
c = iO.Eval(child.Fhat, h)
z = iO.Eval(child.Ghat, c)           // equals parent.Dhat_0(cmd_b::h)
z0 = iO.Eval(parent.Dhat_0, cmd0::h)
guess 0 iff z == z0
```

[DERIVED proof] If `b=0`, determinism gives `z=z0`. If `b=1`, the two
canonical parent inputs are distinct; ACE correctness and their distinct
first plaintext fields imply `z!=z0`. Thus the distinguishing probability
gap is one under the source's perfect correctness. This uses three public
block evaluations and one byte comparison, no key extraction, no forged
ciphertext and no cryptanalytic assumption. It is a mathematical algorithm;
no encrypted test or attack execution was run here.

[DERIVED instantiated margin witness] Set `s=(a,T+1)` and choose
`cmd0=Learn(1,-1)`, `cmd1=Learn(1,+1)`. Take `h` empty for the comparison.
Both immediate releases are ACK. After either command and any residual tape
of length at most `T-1`, the second weight stays at least one; every second
coordinate answer is therefore identical. The first-coordinate trajectories
and answers also agree. This is precisely the full residual-equivalence
family in `HIO.md`, transported from `CONSTRUCTION.md` Section3. The child
functions are equivalent over their entire remaining domain, and the parent
is literally the same object in both worlds. Nonetheless the retained-view
splice reveals which private label was issued. Hidden differences beyond
the horizon are not being used to distinguish these worlds.

[DERIVED extra direct disclosure] Without modifying the source terminal,
there is an even simpler disclosure: continuing `z` through the old suffix
returns `(cmd_b::h, trace)`. A new external function that discards that first
field does not remove the retained old terminal from the host's view. Moving
the discard inside a new terminal might hide this particular output, but it
does **not** repair the fingerprint comparison above, which never calls the
terminal.

## 4. What a real repair must change

[DERIVED all-boundaries version] Let `B_j(x)` be any encrypted boundary of
an honestly generated source parent, computed by evaluating its public prefix
through block `j`. Its decrypted plaintext contains `(x,v_j(x))`. Therefore
`B_j` is deterministic and injective in `x`. If a child exposes even one
exact old boundary `B_j(cmd::h)`, the retained parent can compute the two
candidate values and distinguish the private command. Hiding only the first
old boundary is insufficient if a later old boundary becomes public.

[DERIVED why local patches fail]

* A certificate of correct `Splice` certifies the leaking transcript; no
  soundness or ZK property changes its public block values.
* Fresh encryption before entering the old chain does not help when the
  adapter outputs the old ciphertext afterward.
* Stripping the final input tag, or hashing that tag while preserving a
  reproducible distinguishing fingerprint, does not address the comparison.
* Replacing deterministic ACE with a rerandomizable interface is a new
  primitive/construction obligation. The inspected ACE API supplies neither
  ciphertext rerandomization nor a proof for that replacement.

[DERIVED two concrete ways to conceal all old wires] One can put the entire
parent evaluation inside the new iO wrapper, as the bounded construction in
`HIO.md` already does. Alternatively, place fresh outer encryption on every
old boundary and wrap each old block to decrypt, evaluate the old block and
reencrypt, finally releasing only the authorized trace. Then the host sees
none of the old wire values. This second description is a possible repair
interface, not a proved joint-security construction: the exposed outer
wrappers need their own security argument.

[DERIVED cost barrier for those repairs] Whole-parent wrapping satisfies only
the previously recorded recurrence `L_(d+1) <= P_iO(kappa,poly(L_d,T))`.
Wrapping every old block at every later splice similarly revisits old wrapped
blocks, losing the source construction's constant nesting depth. Generic
polynomial iO bounds do not give polynomial total size in the number of hops.
This is a limitation of these stated implementations and available bounds,
not an impossibility theorem for all HIO extensions. A successful alternative
must both conceal every reproducible old boundary and avoid repeatedly
obfuscating an ever larger old wrapper. Neither the Section7 sketch nor the
splice above provides that pair of properties.

## 5. Provenance is still a concrete positive construction

[DERIVED interface] `HIO_PROVENANCE.md` supplies the separate rooted public
certificate construction for the bounded ordinary-iO wrapper. Its NP statement
binds the exact parent, child, release, suite, depth and genesis; its witness
is a valid command and coins satisfying

```
child = iO(padded(Q_parent,cmd); coins)
y = first_release(Eval(parent,[cmd])).
```

The private issuer verifies a full public ancestry before accepting the
parent for a protected observation. There is no continuing state/read master.
Real setup has no surviving proof trapdoor; simulation and extraction
trapdoors, when required, exist only in the security reduction. The helper
note specifies its exact proof-system assumptions and honest-compiler-coin
requirements rather than treating ordinary ZK as arbitrary false-statement
simulation.

[DERIVED direct hybrid improvement] For this wrapper, canonical replay
substitution is unnecessary. At a hybrid node, the *same actual certified
parent* represents both paired residual functions. Hence its two command
wrappers are equivalent. Switch those wrappers directly by iO. Every issued
certificate statement remains true, although the reduction does not know
the challenge obfuscator's coins; proof simulation is needed for a true
statement with an unknown witness. This avoids the stronger false-statement
simulation requirement of canonical-child substitution. The exact adaptive
provenance/extraction game and loss are in `HIO_PROVENANCE.md`.

[DERIVED status and critical path] Authentic-parent issuance can be closed
conditionally for the bounded ordinary-iO construction using that certificate
interface. The ACE flat splice does not supply its missing polynomial size
improvement: it fails on a fully equivalent, nonconstant learner family with
honest parents and honest issuance. The next constructive problem is an
actual rerandomizing/sealed interface between retained components, together
with a joint-view proof and size recurrence—not more validation of this
leaking splice. There is no practical iO, new crypto run, arbitrary-horizon
renewal, or PQ claim in this result.

## Source and work record

[SOURCE] eprint2023/925 was read only at
`/Users/ember/dev/gh/forks/IACR-eprint-mirror/2023/925.pdf`, using the existing
`sources/2023-925.txt` extraction. Exact source hashes are in frozen `HIO.md`;
the load-bearing locations here are Section3.1 pp7–8 and Section5.1 pp12–13,
with Section7 p29 defining the scope of the sketch. These files were not
changed. `CONSTRUCTION.md` Section3 supplies the existing margin witness.

[EXECUTED work scope] Local text inspection and source/math derivation only.
This continuation used zero web queries, zero Scry calls, zero PDF downloads,
zero cryptographic executions and no new experiment or validation grid.
The provenance helper's own source counts, if any, are reported separately.
Frozen HIO/source files, shared ledgers and companion trees remain unchanged.
