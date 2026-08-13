# Commit-then-audit sampling: prior art, and a correction to my own pitch

2026-08-11. Lane report + my corrections. Papers in `~/paperbin/attestable/`.

## Correction first: "machine-checked sampling soundness would be a genuine first" — the STATEMENT is not novel

I proposed this angle earlier as a first. It is not. The lane found:

**Rinberg, Karvonen, Hoover, Reuter, Warr — "Verifying LLM Inference to Detect
Model Weight Exfiltration," arXiv 2511.02620 (Nov 2025, Harvard/MATS/Stevens,
with an Anthropic co-author).** Predates the Attestable post. It contains:

- Definition 3.1, `(P, n, M, B_I, B_A)`-exfiltration security — an adversary
  split into internal and external algorithms, versus a warden with an
  inspection budget and an alarm budget.
- §3.1, stated as an explicit assumption: *"Random Sampling for Verification is
  Private and Non-manipulable. … If this process were predictable or
  observable, an adversary could infer which pairs will be re-verified."*
- Appendix D.2, a Merkle inference ledger and model ledger.
- Appendix C.2, the sampling-rate derivation: p = 1%, 99% confidence, k = 1 ⇒
  n = 460 samples; k = 100 ⇒ n = 12,460.
- The baseline impossibility: the adversary can always win with probability
  ≥ (M − B_I)/M by concentrating all leakage in one message.

And the pattern is folklore under at least six names, all with published
detection bounds: **covert security** (Aumann–Lindell, the deterrence factor ε),
**spot-checking** (Sarmenta, FGCS 2002), **PoR/PDP** (Juels–Kaliski,
Ateniese — `1 − ((n−t)/n)^c` is exactly our bound's shape), **refereed
delegation** (Canetti–Riva–Rothblum; Verde for ML), **optimistic rollups**
(Truebit's forced errors *is* "make the audit unpredictable"), and **inspection
games** (Avenhaus, 60 years old).

Claiming a first here would be refuted by one search. Dropping that framing.

## Second correction — the lane overstated, and I checked

The lane reported: *"Attestable's public description of the proved statement
does not mention the seed."* **That is wrong.** Their post says, verbatim:

> For a model (F) with committed weights (W), input (x), random seed (r), and
> output (y), Attestable generates a proof of a statement of the form:
> y = F(W, x, r)

and lists among what a verifier checks: *"the required execution policy and
random seed were followed."* They bind `r`.

The real question is narrower and still open from the public text: **when is `r`
fixed, and who chooses it?** If the datacenter picks `r` after seeing `x`, it can
grind seeds or select among valid continuations and encode a payload in the
*choice* while every proof verifies. If `r` is beacon-derived or committed before
generation, it cannot. Their post does not say which. That is a question to ask
them, not a hole to announce.

## The finding that survives and is worth real money

`E[Λ] = b/q` — expected leakage before first alarm — where

```
q = p·(1 − ε_snd) − ε_bind − ε_beacon
```

`p` = audit rate, `ε_snd` = argument soundness error, `ε_bind` = commitment
binding advantage, `ε_beacon` = advantage in predicting the audit selection given
everything through the commitment.

**The lane found no source that writes this composition down.** Everyone assumes
the sampling rate *is* the detection probability. It isn't: the argument
system's soundness error multiplies into it, and beacon predictability
subtracts. If the beacon is a datacenter-local PRNG the adversary can bias,
`ε_beacon` swamps `p` and the whole regime is vacuous at any audit rate.

Concretely: p = 1%, negligible ε's ⇒ q ≈ 0.01. A 4096-token response over a
128k vocab carries b ≈ 8.7 KB. `E[Λ] ≈ 870 KB` before first alarm — 0.0012% of
a 70 GB model. Sampling looks excellent, **conditional on q being real**.

## What is actually open, checked against the literature

1. **Nothing here has ever been machine-checked.** The lane searched Lean
   (ArkLib, VCVio), Isabelle (CryptHOL, the sumcheck formalization), EasyCrypt
   (Firsov–Unruh), Coq (SSProve, FCF) and found **no** formal treatment of
   covert security, deterrence factors, spot-check bounds, PoR/PDP sampling, or
   fraud-proof soundness. That hole is real.
2. **Adaptivity collapse is assumed everywhere, proved nowhere** — that
   committing before the coin makes {audited} and {invalid} independent up to
   `ε_bind + ε_beacon`.
3. **The error-budget composition above.**
4. **The fully adaptive sequential bound** needs a supermartingale/optional-stopping
   argument. Rinberg's Appendix C.2 is i.i.d. binomial — an oblivious adversary.
5. **The burst lower bound as a stated hypothesis**, making the per-message
   entropy cap load-bearing rather than omitted.

Honest framing: *the first machine-checked soundness theorem for commit-then-audit
sampling, with an explicit error budget composing commitment binding, beacon
unpredictability, and argument soundness into one effective detection
probability, plus a matching lower bound.* True, checkable, useful — and it says
"we proved what everyone assumed and priced what nobody wrote down," which is
stronger and safer than "we proved something new."

## A hard limit worth stating up front

Hopper–Langford–von Ahn: if one-way functions exist, then for any efficiently
computable detection policy with false-positive rate α there is a steganographic
scheme evading it at some positive rate. **So `ε_snd > 0` provably, always.** No
sampling regime drives undetected leakage to zero. The best achievable is a
*rate* bound, and the floor is set by the channel's residual entropy, not by p.
Any "overwhelmingly likely to be detected" claim needs to be a rate bound with a
named residual channel.

## On SL5

RAND's SL5 measures are physical and isolation-based — isolated networks, formal
hardware verification, disabling communication at the hardware level. **There is
nothing in SL5 about output verification, proofs, or firewalls**; the only "AI
Model Resilience" item at SL5 is constant inference time, a timing-side-channel
measure. RAND says flatly that achieving SL5 is currently not possible.

So proof-carrying output is an **extension** of the framework, not satisfaction
of it. That is also the strongest honest form of the pitch, because RAND
explicitly asked for the missing piece: *"development of hardware security
module (HSM)-like devices with an interface that is specialized for ML
applications."*


## Addendum 2026-08-12 — a proved lower bound the design must clear

**eprint 2025/358 (Boyle–Komargodski–Vafa): memory checking has
Ω(log n / log log n) overhead EVEN under covert security.** A Merkle inference
ledger is a memory checker; this theorem says relaxing soundness to
catch-with-constant-probability buys **no asymptotic savings** on the ledger
itself. Any "sampling makes the ledger cheap" claim has to clear this bound —
sampling amortizes the PROOFS, not the ledger. Also now pinned: the rational
proofs line (2013/156, 2014/992, 2017/270, 2018/514, 2026/658), rational
sumchecks without Schwartz–Zippel (2015/1058), financially-backed covert
security (2021/1652 — the deterrence factor as on-chain slashing with
non-interactive judging), and RDoC at its ePrint number (2011/518).
