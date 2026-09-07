# Compute-and-compare does not certify this public release gate

[REFUTED: applying the audited lockable/compute-and-compare theorems to the
proposed host-usable bit-release gate] The direct comparison target is public.
Random-lock variants do not repair the source premise when the full underlying
function plus retained artifacts supply an accepting input. This is a precise
theorem-premise failure, **not an attack on either obfuscator**, not an
impossibility for every narrower obfuscation scheme, and not a new BFV attack.
There is no obfuscation implementation or private release mechanism here.

## Exact candidate and surviving credentials

[HYPOTHESIS candidate] Let BFV public encryption and ciphertext evaluation
continue an encrypted state. Fix a transition program, a genesis state
commitment, and the complete release context. For an input
`x=(context,parent_ct,output_ct,proof)`, let a public verifier `V(x)` check the
authorized computation and its bindings. The desired secret-key circuit is

```
Release_sk(x) = if V(x) then Out(Dec_sk(output_ct)) else reject.
```

[HYPOTHESIS isolation] In this note `V` is assumed to have the exact required
soundness and context binding; no proof system is implemented or inferred from
a hash. In particular it binds program, genesis, parent, recipient, randomness,
output ciphertext and the intended released projection. BFV parameters, finite
correctness/noise/range and continuity remain separate premises. Granting an
ideal verifier makes the obfuscation-premise obstruction stronger and cleaner.

[DERIVED credential lifecycle] Honest private setup holds BFV `sk`, all setup
coins, and the original circuit description. The proposed deployment retains
`pk`, required evaluation keys, encrypted state and history artifacts, the
public verifier/context, and the obfuscated gate. Setup erases every plaintext
copy of `sk` and its original code/coins; no online writer master is intended.
The theorem must justify exposing the **entire deployed package** to the host.
An ordinary wrapper retaining `sk` is still a reader. If release instead needs
an external secret unlock credential, that credential and its holder become
an additional role; calling it a lock does not remove it.

## What the primary papers actually prove

[SOURCE] [Wichs–Zirdelis, 2017/276](https://eprint.iacr.org/2017/276),
Def.2.4 p.9 and §3.1 p.14: the target must be unpredictable given the full
function and auxiliary input, or meet the stated conditional HILL entropy
requirement. Def.3.1–3.2 pp.12–13 give distributional VBB/simulation and
all-input statistical correctness. Thm.5.4 p.24 covers circuits under their LWE
assumption with target entropy `lambda^epsilon`; Thm.5.6 p.26 additionally needs
an injective PRG for unpredictable seeds to use unpredictability alone.
§5.4/Thm.5.8 pp.26–27 release a **fixed** message `z` on equality; the target
condition includes `(f,z,aux)`. Construction5.3 p.24 encrypts the program under
(leveled) FHE and obfuscates its decryption/equality tester. This gives a
syntax-level circuit compiler, not permission to omit the target condition.

[SOURCE] [Goyal–Koppula–Waters, 2017/274](https://eprint.iacr.org/2017/274),
Def.3.4 p.16 first lets `A0` choose `(P,msg,st)`, then samples an independent
uniform lock. The simulator knows sizes. §4 pp.17–18 publishes encrypted program,
LHE evaluation key and matrix components; the LHE key is internal to setup.
The main construction has Def.3.3 semi-statistical correctness (fixed input
before obfuscation), not Def.3.2's simultaneous all-input guarantee. AppendixD
p.67 separately assumes low-depth injective PRGs for the stronger version.

[SOURCE] The local September9,2019 version of
[Goyal et al., 2019/1010](https://eprint.iacr.org/2019/1010), abstract p.1 and
§2.6 Def.2.2 pp.13–14, addresses perfect correctness while retaining the same
independent-random-lock security experiment. Only these locations were audited;
the later revision and this paper's construction/reduction were not reviewed.
Correctness improvements do not by themselves change the entropy premise.

[SOURCE scope] The 2017/276 LWE definition, §2.1 p.10, uses parameter families
with `q > (lambda beta)^p` for arbitrary polynomial p and discusses
subexponential lattice approximation factors. The 2017/274 introduction p.2
likewise distinguishes polynomial adversary time from its modulus/approximation
regime. Neither audit instantiates practical BFV parameters or proves a
quantum-advice lift of these classical games.

## The first failing premise, route by route

[DERIVED direct bit gate] For a one-bit output, two fixed-message comparisons
can express the desired functionality syntactically:

```
f_sk(x) = (V(x), Out(Dec_sk(output_ct)))
Gate_b  = MBCC[f_sk, (1,b), b]     for b in {0,1}.
```

The target `(1,b)` is public and predictable with probability one. One can
instead use a single equality bit if the public verifier disambiguates
rejection, but its target remains public. A secret binary target, or a long
encoding of one binary target, still admits prediction with probability at
least one half; it does not supply superlogarithmic entropy. Correct proof
binding does not change this arithmetic.

[DERIVED fixed-message limit] One MBCC instance always returns the same `z`
whenever it accepts. A varying decrypt-and-release output is not this syntax
without another construction. Multiple instances can supply a finite output
alphabet, as above, but each instance must satisfy its own security premise
with the **other instances and retained artifacts** included. Marginally random
locks do not establish joint conditional unpredictability.

[DERIVED public unlock lemma] Consider a distribution `(f,y,z,aux)`. Suppose a
PPT algorithm `A(f,z,aux)` produces `x` with `f(x)=y` with probability p.
The predictor `B(f,z,aux)=f(A(f,z,aux))` guesses y with probability at least p.
Thus any nonnegligible p excludes the distribution from the unpredictable
class. In the deterministic known-input case, y is a function of `(f,z,aux)`;
its conditional entropy is zero. An efficient equality test distinguishes
this distribution from any conditional-min-entropy-h alternative by at least
`1-2^-h`, so positive HILL entropy cannot repair this case either.

[DERIVED distinction] The predictor is given **f**, not its obfuscation. This
is the paper's condition for its theorem; it does not assert that the deployed
host can recover f or the secret key. It is therefore a premise falsifier,
not a key-extraction attack. The existence of some unknown accepting input is
insufficient: the lemma requires an efficient way to obtain one from the
conditioned information.

[DERIVED encrypted unlock] Let `f=Dec_sk` and include a correctly formed
`c_star=Enc_pk(y)` in auxiliary artifacts. Even if the actual host cannot
decrypt `c_star`, the source predictor evaluates `f(c_star)` and obtains y.
More generally a known valid proof/ciphertext pair unlocking a wrapper is
enough. A compiler-generated or later supplied input must not disappear from
the exposure accounting. Standard ciphertext confidentiality cannot prove y
hidden **given the same decryption function**. An additional hybrid would need
its own justified premise; none is supplied by the papers' direct theorem.

[DERIVED random padding] If `f` embeds a random lock and outputs that lock on
authorized inputs, the full description itself contains it. If the lock is
instead recovered from an encrypted token, the previous lemma applies once
that token is in the public package. Changing when the host receives the token
does not prove security after receipt. The GKW experiment's `st` is chosen
before its independent lock: correlated post-lock tokens or functions require
a separate composition argument, not a reordering of the game's lines.

[DERIVED binding is still necessary] If the verifier accepts a ciphertext
merely because it has an output-shaped slot, the host can route each private
bit into that slot using a chosen predicate. Exact authorized-program binding
rejects those substitutions. The target-prediction obstruction persists even
when that verifier is ideal. These are separate requirements; fixing either
one does not establish the other.

## The genuine narrower positive and its boundary

[SOURCE] Wichs–Zirdelis §6 p.29 explicitly gives an obfuscated plaintext
equality checker `CC[g o Dec_sk,y]` that preserves ciphertext confidentiality
under its target condition. Its pp.2–3 discussion explains the separation
between users who can successfully unlock and users covered by the secrecy
condition. GKW §1 pp.3–4 describes a one-sided attribute-hiding construction:
encrypt a random lock under ABE, and obfuscate the program that decrypts this
ciphertext using an **input** ABE key. Hiding is argued for unauthorized keys.

[DERIVED usable claim] A fixed high-entropy target, independent of the full
decryptor and auxiliary history, can support a source-conditional equality
tester after honest setup erasure. Public input encryption does not require
an online master, and correct additive ciphertext updates remain well-typed
under the underlying scheme's own finite correctness bounds. This is an actual
restricted primitive foothold; it is not a normally accepting sign/class gate.
For an adversary covered by its evasive distribution, finding a successful
unlock remains negligible. Supplying an accepting encrypted target changes
the security premises rather than proving a stronger post-unlock guarantee.

[DERIVED why the ABE application is not a counterexample] There the locked
function contains an ABE ciphertext and takes a key as input. The authorized
key is absent from the adversary's permitted auxiliary state. Its security
hybrid can hide the lock from unauthorized keys. Supplying a known authorized
key invalidates that one-sided hiding condition. This differs from putting
a decryptor and its accepting ciphertext together in the conditioning set.

## Executed controls, provenance and resumption

[EXECUTED] `audit.py` implements only finite functions and ideal statement
checks, not BFV, encryption, obfuscation or proof verification. It checks:
65,536 known-unlock predictions (all succeed); one conditional target per
`(f,unlock)`; independent fixed-input acceptance exactly 1/256; 512 exposed
random-padding cases; 4,096 joint auxiliary-lock cases; failure of a single
constant message to return two different accepted values; recovery of every
byte by eight unbound predicates; and 2,048 ideal binding rejections. The toy
domain's eight-bit entropy is a control, not a secure parameter claim.

[EXECUTED] Reproduce the local source extraction and controls with:

```sh
python3 -B research/learn_infer_only/experiments/private_construction/lockable_gate/replay.py
```

[EXECUTED provenance] `results.json` pins all three absolute mirror PDF hashes,
text hashes, actual access levels, pages and script hash; `stdout.txt` preserves
the run. `source/*.txt` is ignored scratch extraction. The replay never
downloads a paper. Matrix reductions and practical obfuscator costs were not
reproduced; the result is a source-game applicability audit plus finite controls.

[REPORTED search] Repository `rg` over resident notes, `notes/` and `swarm/`
found no preexisting lockable/compute-and-compare lane (one unrelated evasive-LWE
mention). Two Scry SQL calls and two web search queries discovered the primary
IDs; both Scry calls were free-slack in their saved records. The first query
was overly broad and returned unrelated uses of “lockable”; the refined query
returned seven metadata rows. Neither search is evidence of field-wide absence.
`SEARCHES.md` preserves exact queries and record IDs. Lane totals: SQL10,
schema1, web30, Kagi0. No retries, new packages or additional metered calls.

[OPEN next precise target] A proof for a restricted, repeatedly accepting
decrypt-and-release functionality must tolerate its public accepting queries
and complete future auxiliary package. Neither of the audited direct
distributional/independent-lock theorems supplies that premise. The independent
key FE ladder and exact binding work remain separate possible ingredients.
