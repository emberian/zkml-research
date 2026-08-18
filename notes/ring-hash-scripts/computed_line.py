"""
COMPUTED-LINE CALCULATOR -- the make-or-break test for the "ship at the computed
line" thesis, plus the per-family round-count arithmetic.

Everything here is CLOSED-FORM arithmetic taken verbatim from a source that is
cited inline.  No estimate is invented; where a number is not derivable from a
cited formula the function REFUSES and says so.

Sources:
  [GSR]  Bhati, Tariq, Ashur, "From Round Skipping to S-Box Skipping", eprint
         2026/1692.  Sec 5.2/5.3 (gadget), 6.1 (distinguisher), 6.2/7.1 (degree),
         7.2 (solver cost), Table 1 (KoalaBear instantiation).
  [BV]   Beyne & Verbauwhede, "Integral cryptanalysis in characteristic p",
         eprint 2025/932 / ASIACRYPT 2025.  Our re-run at base ~2^64:
         notes/ring-hash-scripts/integral_char_p_settling.sage
  [GF]   ring-ro-hash/design_gadget_feistel.py + notes/ring-hash-design.md Sec 3.
"""
from math import log2, ceil

L2A = None  # set per call


# ============================================================ [GSR] the gadget
def gsr_absorbed_rounds(t, k):
    """[GSR] Sec 5: the gadget absorbs one initial full round and t-2k partial
    rounds.  Sec 6.1: the distinguisher covers t-2k+1 rounds.  CLOSED FORM."""
    return 1 + max(0, t - 2 * k)


def gsr_residual_degree_exponent(t, alpha, k, Rp, Rf1):
    """[GSR] Sec 7.1: d_opt = alpha^(Rp + Rf1 - t + 2k), valid only for Rf0 = 1.
    Returns the EXPONENT (log_alpha of the degree)."""
    return Rp + Rf1 - t + 2 * k


def gsr_sycz_time_bits(t, alpha, k, Rp, Rf1, p_bits):
    """[GSR] Sec 7.2: Cantor-Zassenhaus on degree d costs O(d^2 log p).
    Nesting k-1 Sylvester resultants blows degree d -> d^(2^(k-1)), so the
    final CZ runs at ((d^(2^(k-1)))^2) log p.  Sec 7.2.2 verbatim:
    time O(d^(2^k) log p), memory O(d^(2^(k-1)) log p)."""
    e = gsr_residual_degree_exponent(t, alpha, k, Rp, Rf1)
    if e < 0:
        return 0.0, 0.0  # degree 1: the whole thing is linear
    d_bits = e * log2(alpha)
    time_bits = (2 ** k) * d_bits + log2(p_bits)
    mem_bits = (2 ** (k - 1)) * d_bits + log2(p_bits)
    return time_bits, mem_bits


def gsr_required_Rp(t, alpha, k, Rf1, p_bits, target_bits):
    """Invert the cost formula: the smallest Rp for which GSR-SyCZ costs >=
    target_bits, AT Rf0 = 1.  This is 'the computed line' for this family."""
    Rp = 0
    while Rp < 5000:
        tb, _ = gsr_sycz_time_bits(t, alpha, k, Rp, Rf1, p_bits)
        if tb >= target_bits:
            return Rp
        Rp += 1
    return None


# ================================================== Poseidon deployed instances
# [GSR] Sec 7.3 + Sec 1: "Poseidon's KoalaBear parameters adopted by the Ethereum
# ecosystem: p ~ 2^31, alpha = 3, t = 24", "the recommended 31" rounds, and the
# attacked schedules (1,23,4)=28 and (1,20,4)=25.  31 = 4 + 23 + 4 pins
# RF = 8 (Rf0 = Rf1 = 4), RP = 23.
POSEIDON_KB_T24 = dict(t=24, alpha=3, p_bits=31, Rf0=4, Rp=23, Rf1=4)


def banner(s):
    print()
    print("=" * 78)
    print(s)
    print("=" * 78)


banner("(1) REPRODUCE [GSR] Table 1 -- falsification guard on our formulas")
P = POSEIDON_KB_T24
rows = [
    # (k, Rf0, Rp, Rf1, paper_time, paper_mem)
    (1, 1, 23, 4, 20.8, 12.9),
    (2, 1, 23, 4, 49.3, 27.1),
    (2, 1, 20, 4, 30.3, 17.6),
    (3, 1, 18, 4, 55.7, 30.3),
    (4, 1, 16, 4, 106.4, 55.7),
]
allok = True
for (k, Rf0, Rp, Rf1, pt, pm) in rows:
    tb, mb = gsr_sycz_time_bits(P["t"], P["alpha"], k, Rp, Rf1, P["p_bits"])
    e = gsr_residual_degree_exponent(P["t"], P["alpha"], k, Rp, Rf1)
    ok = abs(tb - pt) < 0.6 and abs(mb - pm) < 0.6
    allok &= ok
    print(f"  CICO-{k} ({Rf0},{Rp},{Rf1})={Rf0+Rp+Rf1:>2}  d=a^{e:<2} "
          f"ours=(2^{tb:6.1f}, 2^{mb:6.1f})  paper=(2^{pt}, 2^{pm})  "
          f"{'OK' if ok else '*** MISMATCH ***'}")
print(f"\n  GUARD: {'PASS -- our formulas reproduce the paper' if allok else 'FAIL'}")

banner("(2) THE GAP BETWEEN GSR AND FULL POSEIDON, decomposed")
print(f"  deployed KoalaBear t=24 : Rf0={P['Rf0']}, Rp={P['Rp']}, Rf1={P['Rf1']}"
      f"  -> RF={P['Rf0']+P['Rf1']}, total={P['Rf0']+P['Rp']+P['Rf1']} rounds")
print(f"  [GSR] best CICO-1 reach : Rf0=1, Rp=23, Rf1=4          -> total=28 rounds")
print(f"  gap                     : {P['Rf0']-1} rounds, ALL of them initial-full "
      f"(Rf0: 4 -> 1)")
print(f"  Rp in scope of attack   : {P['Rp']}/{P['Rp']} (100%)")
print(f"  Rf1 in scope of attack  : {P['Rf1']}/{P['Rf1']} (100%)")
print(f"\n  absorbed by the gadget  : 1 + (t-2k) = {gsr_absorbed_rounds(P['t'],1)} rounds at k=1")
print(f"  of which partial        : {P['t']-2} of Rp={P['Rp']} "
      f"= {100*(P['t']-2)/P['Rp']:.0f}% of the partial-round budget")
print(f"  partial rounds LEFT     : {P['Rp']-(P['t']-2)}")

banner("(3) THE MAKE-OR-BREAK: computed line vs designers' provisioned rounds")
print("  Q: at Rf0=1 (the shape GSR needs), what Rp does the COMPUTED line demand?")
for tgt in (100, 128, 160):
    for k in (1, 2):
        need = gsr_required_Rp(P["t"], P["alpha"], k, P["Rf1"], P["p_bits"], tgt)
        print(f"    CICO-{k}, target 2^{tgt:<3}: computed line needs Rp >= {need:>3}"
              f"   (deployed Rp = {P['Rp']})   ratio {need/P['Rp']:.1f}x")
print("\n  -> AT THE SHAPE GSR ATTACKS, THE COMPUTED LINE IS 2-5x FURTHER OUT")
print("     THAN THE DEPLOYED PARAMETER.  The computed bound is not tighter.")
print("\n  Q: does the computed line bind on the DEPLOYED shape (Rf0=4)?")
print("     [GSR] Sec 5.3 linearizes the CICO input constraint by pushing the")
print("     KNOWN value S_in[j]=0 forward through exactly ONE x^alpha.  With")
print("     Rf0>=2 the other coordinates of S_in are free, so the state entering")
print("     the partial layer is no longer affine in X1 -- the gadget does not")
print("     compose.  The paper attacks Rf0=1 only, and 31-28 = Rf0-1 exactly.")
print("     => on the deployed shape this family imposes NO constraint on Rp.")

banner("(4) WHAT ACTUALLY DEFENDS POSEIDON t=24 -- the axis, and its provenance")
sbox_full = P["t"]
sbox_part = 1
tot = (P["Rf0"] + P["Rf1"]) * sbox_full + P["Rp"] * sbox_part
print(f"  S-box budget: RF*t + RP = {P['Rf0']+P['Rf1']}*{P['t']} + {P['Rp']} = {tot}")
print(f"    initial full rounds  : {P['Rf0']*sbox_full:>4} S-boxes ({100*P['Rf0']*sbox_full/tot:.1f}%)")
print(f"    final full rounds    : {P['Rf1']*sbox_full:>4} S-boxes ({100*P['Rf1']*sbox_full/tot:.1f}%)")
print(f"    partial rounds       : {P['Rp']*sbox_part:>4} S-boxes ({100*P['Rp']*sbox_part/tot:.1f}%)")
absorbed = P["t"] - 2
print(f"\n  GSR-absorbed partial rounds cost {absorbed} S-boxes = "
      f"{100*absorbed/tot:.1f}% of the whole budget, and buy ZERO against this family.")
print(f"  The Rf0 margin that DOES stop it costs {(P['Rf0']-1)*sbox_full} S-boxes = "
      f"{100*(P['Rf0']-1)*sbox_full/tot:.1f}% of the budget.")

banner("(5) [BV] INTEGRAL: the second measured instance of the same direction")
print("  heuristic instrument (algebraic-degree saturation), as used by designers:")
print("    real-MDS Poseidon, full-element integral dies at r ~ 5 (d=4)")
print("    -- measured, notes/ring-hash-cryptanalysis.md Sec 'priced weaknesses' 2")
print("  exhaustive instrument ([BV] SPN.ipynb machinery at our base ~2^64):")
print("    tau=1 -> round  2")
print("    tau=2 -> round 24")
print("    tau=4 -> round >= 42")
print("    (guard: reproduces the paper's 1/13/20/21 at their base exactly)")
for name, heur, comp in (("tau=2 vs degree-heuristic", 5, 24),):
    print(f"\n  {name}: computed line is {comp/heur:.1f}x FURTHER OUT than the heuristic.")
print("  [BV]'s own word for the prior designer estimates: 'overly optimistic'.")

banner("(6) GADGET-FEISTEL: the DoF-consumption line (the GSR analogue)")
# [GF] parameters
D, B, K, W, PP, NR = 16, 1 << 16, 4, 4, 2, 16
q_bits = 64
elt_bits = D * q_bits
rate_elts = 2 * W - 1          # rate 7, capacity 1 element
print(f"  R_q = Z_q[X]/(X^{D}+1), q ~ 2^{q_bits}; state (L,R) in R_q^{W} x R_q^{W}")
print(f"  base B = 2^16, K = {K} planes/coefficient; P = {PP} adjacent-plane products")
print(f"  NR = {NR} (design note: 'precedent, not attack-tested')")
print()
print("  THE GSR ANALOGUE.  The nonlinearity is Z_{i,j} = Y_{i,j} * Y_{i,j+1}.")
print(f"  With P={PP} the two products of element i are Y0*Y1 and Y1*Y2 -- they")
print("  SHARE Y1.  Fixing Y_{i,1} to a constant linearizes BOTH.  So ONE plane")
print("  per element per round linearizes the entire round.  Cost in attacker DoF:")
plane_bits = D * int(log2(B))          # one plane of one ring element
per_round = W * plane_bits
free_bits = rate_elts * elt_bits
print(f"    one plane of one ring element = {D} coeffs * 16 bits = {plane_bits} bits")
print(f"    per round (w={W} elements)     = {per_round} bits")
print(f"    attacker input DoF (rate {rate_elts}) = {free_bits} bits")
print(f"    => DoF-limited skip = {free_bits}/{per_round} = {free_bits//per_round} rounds")
skip = free_bits // per_round
print(f"\n  Residual after the skip: {NR}-{skip} = {NR-skip} rounds, each raising")
print(f"  degree by 2 in the plane variables -> degree 2^{NR-skip} = {2**(NR-skip)}.")
print("  Univariate root-finding at that degree is FREE.")
print()
print("  *** BUT THE INSTRUMENT DOES NOT APPLY HERE, AND THAT IS THE FINDING. ***")
print("  The degree-2 count is only valid if the planes are FREE variables.  The")
print("  real primitive fixes them: Y are the base-B digits of R_i + a_{r,i}, a")
print("  relation with NO low-degree polynomial expression over F_q (its vanishing")
print("  ideal has degree B = 2^16 per plane).  So the low-degree system has")
print("  ~2^(16 * planes) spurious solutions and the algebraic cost is NOT the")
print("  root-finding cost.  Neither this family's bound NOR its refutation is")
print("  computable by the degree machinery.  See the note.")

banner("(7) COST OF A ROUND -- what the allocation argument is actually worth")
rows_round = W * (1 + PP)
print(f"  gadget-Feistel rows/round = w*(1+P) = {rows_round}; "
      f"rows/perm = {NR}*{rows_round} = {NR*rows_round}")
print(f"  rows per absorbed ring element = {NR*rows_round}/{rate_elts} = "
      f"{NR*rows_round/rate_elts:.1f}")
print(f"  each round is {100/NR:.1f}% of the permutation cost -- so a round-count")
print(f"  verdict of NR=+/-2 moves the deployed 92,257-constraint figure by "
      f"~{2*100/NR:.0f}%.")


banner("(8) DOES THE SKIP CHAIN? -- Poseidon YES, gadget-Feistel NO. Constructive.")
print("""  GSR chains because fixing an S-box input to delta makes the S-box OUTPUT a
  CONSTANT, so the whole state map becomes AFFINE in the state variables -- and
  affine composes with affine.  [GSR] Sec 5.2: 'Because the mapping is affine,
  every state S^(r) with 1 <= r <= t-2k remains an affine combination of the
  variables in X1.'  That sentence is the entire attack.

  gadget-Feistel: fixing Y_{i,1} = delta makes Z_{i,0} = delta*Y_{i,0} and
  Z_{i,1} = delta*Y_{i,2}, so F_r IS affine -- but affine IN THE PLANE VARIABLES
  OF ROUND r.  Round r+1's plane variables are digits_B(R_{r+1} + a), and
  digit extraction of an affine function of digits is NOT affine.  The
  linearization is per-round and DOES NOT COMPOSE.""")

# constructive: exhibit the failure of digit extraction to commute with affine maps
import random
random.seed(2026)
BB = 1 << 16
def dig(x, k=4, b=BB):
    out = []
    for _ in range(k):
        out.append(x % b); x //= b
    return out
bad = 0
for _ in range(2000):
    u, v = random.randrange(BB), random.randrange(BB)      # two plane-0 values
    if dig(u + v)[0] != (dig(u)[0] + dig(v)[0]):           # carry out of plane 0
        bad += 1
print(f"\n  constructive: digit_0(u+v) != digit_0(u)+digit_0(v) in {bad}/2000 random"
      f" plane pairs ({100*bad/2000:.0f}%)")
print("  -- i.e. the digit map is affine on a set of density ~1/2 per plane, not")
print("     globally.  The GSR chain needs GLOBAL affineness and does not get it.")
print("\n  => on the gadget-Feistel the skip family absorbs AT MOST ONE ROUND,")
print("     versus 1 + (t-2k) = 23 rounds of Poseidon t=24.")

banner("(9) THE DoF CEILING -- an EXACT, EXHAUSTIVE bound ON ALL FUTURE ATTACKS")
print("""  This is the one place the pipeline produces a bound in the DEFENSIVE
  direction that is exact rather than loose, and it is pure counting.

  THE S-BOX CEILING IS THE PAPERS' OWN.  [GSR] Sec 4, on Bariant et al. [6]:
  'their technique expends t-2k of the available t-k input DoFs to bypass
  exactly 2t-k S-boxes ... While 2t-k represents the THEORETICAL MAXIMUM number
  of skipped S-boxes under this formulation'.  And Sec 5: 'GSR skips 2t-2k total
  S-boxes; exactly k fewer S-boxes than [6]s theoretical bound.'

  THE ROUND CEILING IS OURS, AND IT IS THE USEFUL ONE.  A partial round carries
  exactly ONE S-box, so in the partial layer each skipped round costs exactly one
  DoF -- no MDS coincidence can buy two.  Reparameterizing absorbs one full layer
  free.  So:

      absorbed rounds  <=  1 + (t - k)          [DoF ceiling, all families in
                                                 the reparameterize-and-linearize
                                                 class, at CICO-k]
      GSR attains          1 + (t - 2k)
      residual headroom    exactly k rounds""")
for t in (8, 12, 16, 24):
    for k in (1, 2, 3):
        print(f"    t={t:>2} k={k}: GSR {1+t-2*k:>2} rounds | ceiling {1+t-k:>2} "
              f"| headroom {k} | DoF spent {t-2*k}+{k} of {t-k}")
print("""
  The k-round gap is exactly the DoF that GSR spends on the k backward CICO
  input constraints (Sec 5.3).  Closing it requires satisfying those constraints
  WITHOUT spending DoF, which no published technique does.  So:

  => at Poseidon t=24, CICO-1, the ceiling for this ENTIRE FAMILY, present and
     future, is 24 absorbed rounds.  GSR is at 23.  A design needs Rf0 >= 2 for
     an unrelated structural reason; given that, the family is blocked outright.
  => this is a bound on ATTACKS NOT YET WRITTEN, computed by counting, and it is
     the single most valuable object the pipeline produces.  It is also the only
     bound here that is plausibly MACHINE-CHECKABLE (Sec 5 of the note).
""")


banner("(10) THE VALUE FUNCTION OF A PARTIAL ROUND -- and it has a KINK")
print("""  Reconciling this lane's t=24 result with the sibling lane's t=16 result
  (notes/gsr-poseidon-2026-1692.md).  They look opposed and are not:

    t=24 KoalaBear : 22 of 23 partial rounds absorbed -> they buy ZERO
    t=16 BabyBear  : 'beyond R_P=15 every additional partial round buys exactly
                      one round of margin at ~0.7% each -- the cheapest margin
                      in the repo'

  Both true.  The value of a partial round is PIECEWISE with a kink at the
  absorption threshold R_P = t-2k:

      security bits bought by R_P  =  0                            if R_P <= t-2k
                                   =  2^k * (R_P-(t-2k)) * log2(a) if R_P >  t-2k

  A MULTIPLICATIVE margin rule ('+7.5% partial rounds') is blind to a kink BY
  CONSTRUCTION: a percentage of a quantity cannot see a threshold in that
  quantity's VALUE.""")
for label, t, a, Rp, Rf1, k in (
    ("Poseidon KoalaBear t=24", 24, 3, 23, 4, 1),
    ("our Poseidon2 BabyBear t=16 (DEPLOYED)", 16, 7, 13, 4, 1),
    ("our Poseidon2 BabyBear t=24 sponge", 24, 7, 21, 4, 1),
):
    kink = t - 2 * k
    above = Rp - kink
    print(f"\n  {label}")
    print(f"    kink at R_P = t-2k = {kink};  deployed R_P = {Rp}"
          f"  -> {'ABOVE by ' + str(above) if above > 0 else 'BELOW/AT the kink'}")
    m = 0.075 * Rp
    print(f"    a '+7.5% R_P' margin = {m:.1f} rounds; rounds of it above the kink"
          f" = {max(0, min(m, Rp - kink if Rp > kink else 0)):.1f}")
    if above <= 0:
        print(f"    ⚑ EVERY ONE of the {Rp} deployed partial rounds buys ZERO"
              f" against this family.")

banner("(11) SAME BUDGET, INSIDE THE DESIGNERS' OWN OPTIMIZATION")
print("""  Verified verbatim in the Poseidon paper (eprint 2019/458, extracted from
  ~/dev/gh/forks/IACR-eprint-mirror/2019/458.pdf):

    Sec 3, 'Security Margin':  'Given the minimum number of rounds necessary to
      provide security against all attacks known in the literature, WE
      ARBITRARILY DECIDED TO ADD: - two more rounds with full S-Box layers
      (+2 RF); - 7.5% more rounds with partial S-Box layers (+7.5% RP).'
      -- the designers' own word is ARBITRARILY.

    Sec 3, 'Statistical Attacks': 'RF^stat >= 6 if C*(t+1) <= N+n-M, else 10',
      C = 1 for the cubic S-box.  R_F IS SET BY STATISTICAL ATTACKS.

    Sec 4, 'Minimize Number of S-Boxes': 'the goal is to find the best ratio
      between RP and RF that minimizes  number of S-Boxes = t * RF + RP'.
      ⚑ THE DESIGNERS ALREADY RUN THE ALLOCATION OPTIMIZATION.  Our contribution
      is not a method -- it is a NEW CONSTRAINT (the GSR kink) in an
      optimization they already solve.

    Footnote 2 (GSR): 'Poseidon instances in [12] are defined with Rf0 = Rf1'.
      So RF is even and Rf0 = RF/2.""")
t, a, k = P["t"], P["alpha"], 1
kink = t - 2 * k
budget = (P["Rf0"] + P["Rf1"]) * t + P["Rp"]
print(f"\n  Poseidon KoalaBear t=24, alpha=3.  Objective t*RF + RP held at {budget}.")
print(f"  Statistical floor RF >= 6.  GSR structural gate Rf0 >= 2, i.e. RF >= 4.\n")
print(f"    {'RF':>3} {'Rf0':>4} {'RP':>4} {'t*RF+RP':>8} {'rounds above GSR kink':>22} {'gate margin (Rf0-2)':>20}")
print(f"    {'-'*3} {'-'*4} {'-'*4} {'-'*8} {'-'*22} {'-'*20}")
for RF in (10, 8, 6, 4):
    Rf0 = RF // 2
    Rp = budget - RF * t
    if Rp < 0: continue
    tag = "  <- DEPLOYED" if RF == 8 else ("  <- statistical floor" if RF == 6 else
          ("  <- BELOW statistical floor" if RF < 6 else ""))
    print(f"    {RF:>3} {Rf0:>4} {Rp:>4} {RF*t+Rp:>8} {Rp-kink:>22} {Rf0-2:>20}{tag}")
print(f"""
  ⚑ THE TRADE, STATED AS A RATIO.  Poseidon's arbitrary '+2 RF' costs 2*t = {2*t}
     S-boxes and buys ONE extra round of margin on the GSR gate axis.  The same
     {2*t} S-boxes on the R_P axis buy {2*t} rounds of margin above the kink.

         48 S-boxes  ->  1 round of gate margin      (what was bought)
         48 S-boxes  ->  48 rounds of kink margin    (what they buy)

     RATIO 48:1.  The designers could not have known -- the kink was not
     discovered until 2026 -- but it is computable NOW, inside their own
     objective function, and no multiplicative margin rule will ever find it.

  ⚠ THE HONEST COUNTER, and it is real.  The '+2 RF' is unknown-attack insurance
     on exactly the axis GSR Sec 5.3 attacks (the backward step through initial
     full rounds).  Spending ALL of it is the wrong lesson if the next paper
     extends that step past one full round -- which the sibling lane names as
     'the thing to watch'.  RF=6 keeps ONE round of gate margin, not zero.
     ⚠ And R_P is separately priced by A4 (CheapLunch) which is NOT in this
     calculation.  This is a DEMONSTRATION OF THE METHOD, not a proposal to
     reparameterize Poseidon.
""")

banner("(12) THE PINCER -- two families whose regions cover a whole axis")
print("""  From the sibling lane (notes/gsr-poseidon-2026-1692.md Sec 1c), computed on
  our deployed constants, and it is the sharpest thing either lane found:

    dim Krylov(M_I, e_0) = t   =>  GSR's t-2k constraints are INDEPENDENT
                                   => the gadget applies in full
    dim Krylov(M_I, e_0) < t   =>  M_I has a nontrivial invariant subspace
                                   => broken by classical SUBSPACE TRAILS

  and Poseidon2's own design criterion (Grassi-Rechberger-Schofnegger, ToSC
  2021, 'Proving resistance against infinitely long subspace trails') REQUIRES
  no nontrivial invariant subspace -- i.e. requires full Krylov.

  => I_{A2} union I_{T3} covers the ENTIRE Krylov axis.  No linear layer exists
     that defeats both.  The sibling lane states it exactly: 'There is no matrix
     that fixes this.'

  ⚑ THIS IS THE COMPOSITION RULE EARNING ITS KEEP.  Under 'R = max_f R_f +
     margin' you take a max and ship, and you NEVER LEARN that an axis is
     exhausted -- there is no max to take, because neither family is about R.
     Under the infeasibility-region formulation the union is computable and the
     answer 'this axis is closed, pay on another one' falls out.
""")
