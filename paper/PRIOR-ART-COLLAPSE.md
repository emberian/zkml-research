# The math sweep collapsed most of the novelty. What is left is small and true.

2026-08-13. The eprint-only corpus cost us exactly what it was always going to.

## The single most important finding

**p61 is row h=127 of Table 5 in Riesel, *Prime Numbers and Computer Methods
for Factorization*, 2nd ed., Birkhäuser 1994, p. 391** — read out of the book:

    127:  2, 12, 18, 24, 54, 72, 114, 180, 214, 504, 558, ...

**KoalaBear (n=24) and p61 (n=54) are the 4th and 5th entries of one row of a
1994 textbook table.** The family is completely enumerated for n < 7·10^6 (33
primes, 25 inert, 8 not) at prothsearch.com and in OEIS A032413. Our "search
to 600, first failure at n=214" is weaker than published knowledge — and
n=214 is itself a listed term.

**The better story is right there**: the proof-system community adopted n=24
in 2024 without looking at the row it came from. And every n in Riesel's
printed row is even — half our "family law" is *visible in a 1994 table*.

## Per-claim collapse

- **The family law: FOLKLORE.** Φ_n irreducible over F_p ⟺ p is a primitive
  root mod n is **Lidl & Niederreiter Thm 2.47**; primitive-root lifting to
  3^k is Hardy & Wright Thm 123; "p ≡ 2 or 5 mod 9" is **OEIS A228485**
  citing Cohen GTM 239. The composition is a five-line exercise. Drop "law."
  (The general-k version is free and worth stating instead — a 9×6 table;
  corollary: 3|k ⇒ no member is ever inert.)
- **NTT primes tabulated by 2-adicity: KNOWN, and old.** "Fourier prime" /
  "FFT prime" predate ZK by decades (von zur Gathen & Gerhard; Harvey & van
  der Hoeven); NTL literally computes v₂(p−1) in `CalcMaxRoot`; Bhattacharya
  & Astola EUSIPCO 2000 publish the table. ⚑ **FLINT's default FFT prime is
  our own construction one size down: 2^50 − 2^44 + 1 = 63·2^44+1.**
- **"Joint multi-constraint modulus search": KNOWN, four precedents.** The
  closest is the **apfloat 1.10 manual, 15 May 1996** — an exhaustive census
  of Solinas-form primes at word boundaries, jointly by 2-adicity and
  shift-fold reduction cost, with counts, a winner and an exhaustion
  negative. **Its 64-bit moduli are 2^64−2^32+1 (= Goldilocks) with
  generator 7 — three years before Solinas.** Also Pollard 1971, NFLlib
  CT-RSA 2016 (a named prime-selection algorithm with three simultaneous
  constraints and a shipped 1000-prime table).
- **Barrel-shift / Φ_m(2^b): KNOWN since 1982.** Duhamel & Hollmann,
  Electronics Letters 1982; Hollmann & Duhamel ICASSP 1983, abstract
  verbatim: *"transforms using the modulus 2^{2q} − 2^q + 1, which require no
  multiplications… obtained through evaluations of generalized cyclotomic
  polynomials."* That is C7.1's entire object. Goldilocks' "six ways" was
  published by Goucher (2021) and Bloemen (2022). ⚑ **And our count is
  wrong: 21 distinct primes from 37 (m,b) pairs** — the census
  double-counted exactly the multi-representation phenomenon the "six ways"
  sentence celebrates. ⚑ **C7.1's own falsifier fired**: F₇'s 73-bit factor
  has 2-adicity exactly 9 — in band, at the threshold.
- **C1.4 as written is false.** "2-adicity appears in no FHE paper" reads as
  a claim about the concept; NFLlib makes `q ≡ 1 mod 2n` a named selection
  constraint and censuses by it. Rewrite as terminology: **FHE treats it as
  a satisfiability side-condition at fixed small N; the proof side treats it
  as an objective to maximize.** That distinction is real and defensible.
- **§8 must not imply certificate machinery is new** — CoqPrime (FLOPS
  2006), ECPP in Coq (TPHOLs 2007), Pratt certificates in the AFP.

## What actually survives

1. **The specific constraint pair** — FHE noise/RNS/negacyclic *together
   with* proof-side FRI evaluation-domain size. Not "the search."
2. **The terminology observation** (side-condition vs objective).
3. **The Lean artifact** — the specific theorems are still ours, inside
   established practice.
4. **The experiment** and the scaling analysis (K3 chunking).
5. **Free win**: 127·2^114+1 = 2^121 − 2^114 + 1 is prime, 2-adicity 114,
   inert, **inside our own census band** — the family's own answer to the
   ≥2-word band, which §10 missed.
6. **Verified sharpness**: 2^61−2^b+1 is prime only for b ∈ {1,5,21,24,26,54}
   — p61 is the unique high-2-adicity Solinas prime at its width.

## The honest verdict

This is not a paper about a novel prime or a novel search. **At most it is a
short note about a constraint pair nobody has posed together, with a measured
experiment and machine-checked certificates** — and the most interesting
sentence in it is that a 1994 textbook table contains both the field the
proof community uses today and the one it should probably use next.
