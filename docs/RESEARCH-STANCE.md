# The stance: basic research, composable ingredients, mutable design

2026-08-14, ember, and it corrects a drift I had not noticed in myself:

> *"We're not trying to just build one thing that dominates everything. We're
> trying to flesh out models and implementations of many of these proof
> systems, by implementing the primitives in composable ways. Lean is a bag of
> formal composable ingredients that we build as we chart them out. We're
> basically doing pure basic research, not trying to build a product —
> formalize and evaluate the landscape. Parts of the design you've been
> tacitly treating as fixed are in fact mutable."*

## What I had been treating as fixed, and is not

| treated as fixed | actual status |
|---|---|
| **Poseidon2** | inherited from Plonky3 — *which we are abandoning*. And we measured it at **2.78× Blake3 natively**, paying that to buy in-circuit cheapness **that nobody here ever checked the trade on.** |
| **BabyBear** | one point in a space that includes KoalaBear, Goldilocks, **and binary towers** — and **13 of 18 keystones are field-agnostic**, with 0 `IsPrimitiveRoot` in the tree. |
| **FRI as the PCS** | BaseFold landed, additive BaseFold landed, Ligerito has exploratory Lean, WHIR is adjacent. |
| **AIR as the relation** | **Spartan/R1CS just landed and composes** from ingredients we already had. |
| **Ext4** | Ext5, Ext6 all live; Ext6 is *built* and Ext4/Ext5 exist as types nowhere. |
| **blowup 6** | the floor was **an upstream bug we had frozen as a law**; lb=2 now verifies. |
| **prime characteristic** | one structure was the whole wall, and it is now named rather than silent. |

## The consequence for how I brief

**Lanes should chart and formalize, not select.** A lane that returns *"here is
the map, here is what each costs, here is the Lean interface both instantiate"*
is worth more than one that returns a winner. **"Does X compose with what we
hold?"** is a scoping question; **"is X worth understanding?"** is a different
one — and I conflated them once already, on Ligerito, where exploratory
formalization then **refuted two of six 'absent' verdicts and inverted the
sequencing.**

**The unit of progress is a composable ingredient with an honest generality
label** — real, cosmetic, or trap — not a system that beats a benchmark.

## The insight this reframe unlocked

⚑ **We are hash-bound at 5.0–7.2×, and we chose our hash for a reason that
only holds in a prime field.** Poseidon2 is cheap in-circuit and expensive
natively; traditional hashes are the reverse; **in a binary field they are
cheap in both.** So the binary-field work is not about competing with
BinarySpartan's benchmark — ***it attacks our own dominant term.*** That is
why the five binary lanes matter more than the rate comparison, and it is a
connection I only made when the design stopped being fixed.

## And the corresponding honesty about rates

I asserted we "can't touch 410k hashes/sec" without deriving anything. Derived:
**~17,700 Poseidon2 permutations proven/second** (38,168 in-circuit ops per
wrap ÷ a 2.16 s wrap), i.e. **12.4× off their SHA-256 throughput and 4.6× off
Flock per-core** — on a contended box, at b=6, before four landed fixes.
⚠ **And I will not quote the compounded figure**, because our own cost model
says the wins **reshuffle phase shares rather than multiplying** — that number
has to be composed and measured, which is what the hbox rig is for.
