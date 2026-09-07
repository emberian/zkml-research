# A direct DDH lemma for this fixed observable span

[DERIVED conditional theorem; independent review pending] The exact rank-two
key set in this experiment admits an adaptive-message IND proof under DDH.
This is a new specialization derived here, not a claim that ABDP2015/017
Theorem3.2 states adaptive security. No simulation, quantum or malicious-setup
theorem is inferred. The proof contains no state-recovery experiment.

## Game and timing

[DERIVED definition] Work in a prime-order group of order q with generator g.
The group, dimension three and key vectors

```
y0=(1,1,0), y1=(0,1,1), w=(1,-1,1)
```

are fixed before setup. Honest setup samples the ABDP master vector uniformly,
publishes the three group elements and gives the adversary both function-key
scalars. The adversary can perform arbitrary efficient local computations,
including deriving every key in their span and using it on arbitrary
ciphertexts. No additional master-key or encryption-coin exposure is permitted.

[DERIVED definition] The adversary then submits a pair `(x0,x1)` adaptively
after seeing the public key, function keys and its permitted history. The pair
must satisfy `Y*x0=Y*x1` over Z_q. It receives a fresh encryption of one side.
In the multiple-input version, one hidden bit is shared by at most polynomially
many such requests, and admissibility is required at every request on the
actual adaptive history. Initial auxiliary state is independent of the honest
master beyond public artifacts supplied in this experiment. Setup-dependent
auxiliary credentials require a separate argument.

[SOURCE boundary] ABDP2015/017 Fig.2 p.7 and Theorem3.2 pp.8–9 give selective
challenge-message security. Its proof chooses a master-key basis using the
challenge difference. The following fixed-span reduction chooses its basis
before any message request, which is why this narrower game can be stronger.

## One challenge, explicit reduction

[DERIVED] Given a DDH instance `(A=g^a,B=g^b,C)`, independently choose uniform
`t0,t1 in Z_q`. Give the adversary

```
mpk = (g^t0 A, g^t1 A^(-1), A)
key_y0 = t0+t1 mod q
key_y1 = t1.
```

These are distributed exactly as honest setup with
`s=(t0+a,t1-a,a)`. The linear map from `(t0,t1,a)` to s is invertible, so s is
uniform. The issued scalars are exactly the inner products with y0 and y1.
No challenge message was used to construct this public key or its keys.

[DERIVED] On receiving an admissible message pair, choose a fair bit mu and
return

```
ct = (B,
      B^t0 C       g^(x_mu[0]),
      B^t1 C^(-1) g^(x_mu[1]),
             C    g^(x_mu[2])).
```

If `C=g^(ab)`, this is exactly the source encryption algorithm with fresh
randomness b. If C is independent uniform, the ciphertext distribution is
independent of mu. Indeed admissibility gives `x1-x0=k*w`; translating C to
`C*g^(-k)` changes the encoding of x1 into that of x0, and preserves uniformity.
This remains true conditioned on the public key and all preceding transcript:
the pair is chosen before this fresh challenge ciphertext, and the reduction
has not exposed B or C through earlier messages. Any later computation is
postprocessing of the same distribution.

[DERIVED quantitative bound] Let `Delta=|Pr[A outputs1|side0]-Pr[A outputs1|side1]|`.
The DDH distinguisher outputs one iff A's guess equals mu. Its advantage, measured
as a difference in event probabilities, is exactly `Delta/2`: in the independent
DDH world its success is one half. Thus `Delta <= 2 epsilon_DDH` for the
actual reduction resources. This does not assert a numerical DDH security level
for the fixed 2048-bit reference group.

## Adaptive histories and the window

[DERIVED] For at most T challenge input ciphertexts, use hybrids with the first
j requests answered from one side and the rest from the other. At the selected
request embed the single challenge above; all other requests are answered by
ordinary public encryption. The adversary chooses each subsequent pair from
the actual transcript. In the random DDH world the selected ciphertext and
therefore all later interactions are independent of mu. The adversary is run
once; there is no rewinding or resampling of its state.

[DERIVED strict PPT sampling] Set `M=2^ceil(log2(max(1,T)))`, draw exactly
`log2(M)` fair bits, and use ranks below T as the selected request. Dummy ranks
output an independent fair bit. Signed telescoping gives DDH advantage exactly
`Delta_total/(2M)` in absolute value. For T>0, `T<=M<2T`, hence the conservative
bound `Delta_total<=2M epsilon_DDH<4T epsilon_DDH`. Ordinary polynomial T is
allowed because this is one uniform polynomial-time reduction. The 12-input
demonstration has M=16 and coefficient32. This is a derived bound, not a
quantitative theorem quoted from the source.

[DERIVED postprocessing] Public ciphertext multiplication and inversion,
window insertion/expiry, ciphertext serialization, fixed-key projection reads
and retained snapshots are all efficient computations of this exposed package.
They need no further secret oracle. Therefore the same IND statement covers
their complete transcript. It protects pairs of **entire input histories** only
when every challenged input pair agrees on the full fixed projection span.
Equality of current window sums alone is not the game's admissibility rule.

[DERIVED range] For honest input coordinates in [-2,2] and W=4, each window
projection lies in [-16,16]. This gives efficient, unique integer decoding
without modular ambiguity in the chosen large-order group. The exposed key
holder also obtains group-valued projections and arbitrary span combinations;
the decoder interval is an application contract, not a cryptographic gate.

[DERIVED exclusions] This proof does not allow selecting new independent key
directions after seeing ciphertexts, exposing the master or per-input coins,
private recipient-only release, trusted continuity, verified erasure, nonlinear
hidden transitions or quantum adversaries. The concrete Python arithmetic is
not constant-time. A proof for these abstract equations is not a side-channel
proof for the implementation. Classical public input issuance and a fixed
span are the exact positive being claimed.
