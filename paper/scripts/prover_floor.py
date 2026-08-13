#!/usr/bin/env python3
"""
Prover-cost floor derivation.  Every constant is MEASURED (source in comment)
or DERIVED (derivation shown).  Currency: base-field MULTIPLICATIONS.
"""
from math import log2

# ===========================================================================
# MEASURED CONSTANTS
# ===========================================================================
# zkml-research/phase0/h2-rns-vs-single-prime/results_2026-08-13_m2max.txt
MUL_PACKED_NS = 0.19      # BabyBear packed mul, M2 Max 1 core (0.148-0.242)
ADD_NS        = MUL_PACKED_NS / 3
FHE_MODADD_NS = 0.19      # 36-bit u64 modular add
# breadstuffs/docs/deos/GPU-PROVER-PROTOTYPE.md:632 (counted from p3 82cfad7)
P2_MULS_BB, P2_ADDS_BB, P2_RATE = 655, 1309, 8
HASH_GPU  = 300e6         # wgpu M2 Max, full MMCS tree
HASH_CPU  = 3.8e6         # rayon over the SCALAR p3 perm, 12 cores

def perm_muls(rf, rp, alpha, w):
    s = {3: 2, 5: 3, 7: 4}[alpha]
    return rf * w * s + rp * s
BB_SBOX = perm_muls(8, 13, 7, 16)          # deployed: descriptor_ir2.rs:8618
KB_SBOX = perm_muls(8, 20, 3, 16)          # Plonky3 KoalaBear w16
DIAG    = P2_MULS_BB - BB_SBOX             # internal 1+Diag(V) layer muls
KB_PERM = KB_SBOX + DIAG
BB_OPEQ = P2_MULS_BB + P2_ADDS_BB / 3
KB_OPEQ = KB_PERM   + P2_ADDS_BB / 3
PERM_NS = P2_MULS_BB * MUL_PACKED_NS + P2_ADDS_BB * ADD_NS
BLAKE3  = 1.75 * 8    # Gbit/s, M2 1 core
kb_gbit = 1e9 / (KB_PERM * MUL_PACKED_NS + P2_ADDS_BB * ADD_NS) * 248 / 1e9

print("="*79); print("0.  THE PERMUTATION"); print("="*79)
print(f"  BabyBear  a=7 RF=8 RP=13: S-box muls {BB_SBOX} + diagonal {DIAG} = {P2_MULS_BB} (counted in-tree)")
print(f"  KoalaBear a=3 RF=8 RP=20: S-box muls {KB_SBOX} + diagonal {DIAG} = {KB_PERM} (derived)")
print(f"  DERIVED native BB/KB perm ratio        : {P2_MULS_BB/KB_PERM:.2f}x")
print(f"  MEASURED in-circuit ratio (hash-verdict): 298/164 = 1.82x   -- agree to 4%")
print(f"  DERIVED 1-core perm cost {PERM_NS:.0f} ns -> ALU ceiling {12e9/PERM_NS/1e6:.0f} Mhash/s on 12 cores")
print(f"  MEASURED scalar-p3 rayon: {HASH_CPU/1e6:.1f} Mhash/s = {12e9/PERM_NS/HASH_CPU:.0f}x below its own ALU ceiling")
print(f"  MEASURED wgpu GPU      : {HASH_GPU/1e6:.0f} Mhash/s")

# ===========================================================================
# 1.  PER-COMMITTED-ELEMENT COST
# ===========================================================================
def per_element(b, w, log_h, d=3, k=2, perm=BB_OPEQ):
    """mult-equiv per committed base felt: (hash, encode, sumcheck)"""
    hash_perms = (2**b) * (1/P2_RATE + 2/w)   # leaf sponge + tree; FRI batches columns
    return hash_perms * perm, (2**b + 1) * log_h / 2, (d-1)*k*10

print(); print("="*79)
print("1.  COST PER COMMITTED BASE FELT  (w=48, h=2^20, d=3, k=2)"); print("="*79)
print("""
   HASH    leaves h*2^b, each a row of w -> ceil(w/8) sponge perms
           tree   h*2^b-1 compress perms
           FRI    the w columns are batched into ONE codeword of length h*2^b
                  BEFORE folding, so FRI hashing is ~h*2^b, NOT n*2^b.
                  <- this is WHY "opening" is 1.04% of DeepProve Table 7.
           per element  2^b * (1/8 + 2/w) perms
   ENCODE  iNTT size h once + 2^b forward NTTs: (2^b+1)*log2(h)/2 mults
   SUMCHECK  linear-time folding: sum_i n/2^i = 2n halvings, each (d-1)*k
           evaluations, rounds>=2 in the ext (Karatsuba e=4 -> 9 base muls)
           per element  ~(d-1)*k*10 mults      <-- INDEPENDENT of the blowup
""")
print(f"  {'b':>2} {'rate':>7} | {'hash':>9} {'encode':>7} {'sumck':>6} | {'hash%':>6} {'rel b=1':>8}")
base = None
for b in (1,2,3,4,5,6):
    hm,en,sc = per_element(b,48,20); t = hm+en+sc
    base = base or t
    print(f"  {b:>2} {'1/'+str(2**b):>7} | {hm:>9.0f} {en:>7.0f} {sc:>6.0f} | {hm/t*100:>5.1f}% {t/base:>7.1f}x")
print("""
  VERDICT: HASH-BOUND at every blowup >= 2.  The sumcheck -- the term the
  literature optimises -- is 2-17% and is the ONLY term that does not scale
  with the blowup.  A 2x on the sumcheck is a 1.02-1.17x on the prover.
""")

# ===========================================================================
# 2.  BLOWUP -- model vs the measured deployed grid
# ===========================================================================
print("="*79); print("2.  THE BLOWUP LEVER -- model checked against a MEASURED grid"); print("="*79)
grid = {3:(194.1,29),4:(159.7,20),5:(136.1,32),6:(120.4,58),7:(114.0,101),8:(106.5,183)}
print("  MEASURED, breadstuffs/.docs-history-noclaude/PROOF-ECONOMICS.md:151 (transfer turn):")
print(f"  {'lb':>3} {'q':>4} {'KiB':>7} {'prove ms':>9} | {'model 2^b':>10} {'meas/lb=4':>10}")
qs = {3:38,4:29,5:23,6:19,7:17,8:15}
for lb,(kib,ms) in grid.items():
    print(f"  {lb:>3} {qs[lb]:>4} {kib:>7.1f} {ms:>9} | {2**lb/2**4:>9.1f}x {ms/20:>9.1f}x")
print(f"""
  The model predicts prove-time ~ 2^b.  MEASURED: from lb=4 the doubling is
  exact (20 -> 32 -> 58 -> 101 -> 183 ms is 1.6/1.8/1.7/1.8x per step).
  Below lb=4 the model OVER-predicts -- at lb=3 the query/opening term and the
  38 query paths take back what the halved codeword saved.  Named inadequacy.

  ** THE DEPLOYED POINT IS lb=6.  THE MEASURED OPTIMUM IS lb=4.  2.9x. **
  And lb=6 buys 34 PROVEN bits (UDR, two-regime-calculator.md); lb=4/q=29
  buys about the same.  The 130 that lb=6 is chosen for is the CBR column,
  which ethereum/soundcalc DELETED.  We are paying 2.9x for a withdrawn regime.

  FLOOR ON THE BLOWUP, and it is a FIELD-CHOICE consequence:
  MEASURED (circuit/tests/fri_blowup_global_knob_survey.rs) 38 of 91 goldens
  REFUSE to prove at lb=2 -- the inline degree-7 Poseidon2 S-box needs a
  degree-6 quotient.  At KoalaBear (a=3) the quotient is degree 2 and lb=2 is
  legal.  So KoalaBear buys {P2_MULS_BB/KB_PERM:.2f}x on the permutation AND unlocks one more
  blowup halving = {P2_MULS_BB/KB_PERM*2:.1f}x on the DOMINANT term.  The field memo argued
  constraint degree; this is the same fact priced on the term that dominates.
""")

# ===========================================================================
# 3.  WORKLOAD 1 -- BFV
# ===========================================================================
print("="*79); print("3.  WORKLOAD 1 -- BFV"); print("="*79)
N, LIMBS, POLYS, ORDERS = 4096, 3, 2, 4
RESIDUES = ORDERS*POLYS*LIMBS*N          # 98,304
AIR_ROWS, AIR_W = 2**20, 48
AIR_ELEMS = AIR_ROWS*AIR_W
print(f"""
  MEASURED GEOMETRY (metatheory/Market/PrivateBookBfvNttFamily.lean, theorem
  `production_geometry`; Rust census asserts the row histogram exhaustively):
     EQUATION_COUNT      = 4*2*3*4096 = {RESIDUES:,}
     live rows           = 1,032,192  (ForwardU 294,912 / Pointwise 98,304 /
                                       InverseProduct 589,824 / Terminal 49,152)
     padded rows         = 2^20       width = 48    range checks = 48/row
                                       (21 limb @14/14/8b + 11 carry @16b + 16 sched)
     radix 2^14, 3 limbs per 36-bit residue
     committed base felts = 2^20 * 48 = {AIR_ELEMS:,}

  *** WHAT IT ACTUALLY PROVES: a fresh ENCRYPTION,  ct0 = u*pk0 + e0 + D*m,
      ct1 = u*pk1 + e1.  NOT fold_add, NOT ct x pt, NOT ct x ct -- those have
      NO AIR AT ALL (fhegg-core/src/bfv_lean.rs:539 `fold_add`, no descriptor).

  *** AND pk IS PUBLIC.  So (u,e0,e1,m) |-> (ct0,ct1) is a PUBLIC LINEAR MAP
      over R_q.  The entire 1,032,192-row butterfly family commits the
      INTERIOR of a public linear map.  That is the whole finding. ***

  Blow-up against information content:
     output residues {RESIDUES:,} at 36 bits = {RESIDUES*36/8/1024:.0f} KiB
     committed {AIR_ELEMS:,} felts at 31 bits = {AIR_ELEMS*31/8/1024/1024:.1f} MiB
     ratio = {AIR_ELEMS*31/(RESIDUES*36):.0f}x
""")
for b in (4,6):
    hm,en,sc = per_element(b,AIR_W,20)
    c = AIR_ELEMS*(hm+en+sc)
    print(f"     AIR prover cost @lb={b}: {c:.3e} mult-equiv = {c*MUL_PACKED_NS/1e9:>7.2f} s/core,"
          f" {c*MUL_PACKED_NS/1e9/12:>6.2f} s on 12 cores")
    if b==4: AIR4 = c
    if b==6: AIR6 = c

print("""
  (a) THE SUMCHECK ROUTE for the SAME statement.
      In the NTT domain u*pk is pointwise with a PUBLIC vector:
         hat(ct)(x) = hat(pk)(x)*hat(u)(x) + hat(e)(x) + D*hat(m)(x)
      = one degree-3 zerocheck per limb per poly.  The coefficient<->NTT
      domain change is a public linear map whose matrix w^{ij} factors over
      bit pairs, so its MLE is succinct: verifier O(log^2 N), prover O(N)
      (the zkCNN linear-time FFT sumcheck; our notes file it as conv-specific
      -- it is not, it is THE FHE domain-change primitive).
      COMMIT: only the secret inputs u, e0, e1, m (+ the public ct if the
      light client cannot afford O(N) MLE evaluation).""")
for name, felts in [("36-bit limb -> 2 BabyBear felts", 2),
                    ("KoalaBear-matched limb (1 of 3)", (2+2+1)/3)]:
    secret = ORDERS*4*LIMBS*N*felts          # u,e0,e1,m
    public = ORDERS*POLYS*LIMBS*N*felts      # ct, if committed
    e = secret+public
    hm,en,sc = per_element(4,48,17); sc_extra = 3*ORDERS*POLYS*LIMBS*N*20  # 3 sumchecks/transform
    c = e*(hm+en+sc)+sc_extra
    print(f"      {name:<34}: {e:>9,} felts -> {c:.3e} = {c*MUL_PACKED_NS/1e6:>7.1f} ms/core")
    if felts == 2: SC2 = c
    else: SCKB = c
print(f"""
      RATIO vs the emitted AIR at matched lb=4 : {AIR4/SC2:.0f}x  (2-felt limbs)
                                                {AIR4/SCKB:.0f}x  (KoalaBear-matched limb)
      RATIO vs the DEPLOYED lb=6 AIR           : {AIR6/SCKB:.0f}x

      ITEMISED, {AIR_ELEMS:,} -> {ORDERS*6*LIMBS*N*2:,} committed felts:
        10.5x  the butterfly network itself -- 1,032,192 rows to certify
               {RESIDUES:,} equations, i.e. the INTERIOR of the transform
         2.0x  36-bit limbs emulated in a 31-bit field
         2.0x  the carry + range columns that emulation forces (32 of 48 ranges)
         1.02x padding 1,032,192 live rows to 2^20
        (and the deployed family already beats SCHOOLBOOK_FAMILY_ROWS =
         402,653,184 by 384x -- the 128x below is on top of that.)
""")

print("  (b) fold_add -- the extreme case, and there IS no AIR to compare to.")
CT = POLYS*LIMBS*N
print(f"""
      One ciphertext = {POLYS}*{LIMBS}*{N} = {CT:,} residues.
      MEASURED plaintext ct+ct: 4.67-5.29 us ({CT:,} modular adds @ {FHE_MODADD_NS} ns).

      THEOREM (proof in prose): a linear relation over MLE-committed vectors
      costs ZERO beyond the openings.  MLE is a LINEAR map F^n -> multilinear
      polys, so c_out = sum a_k c_k  =>  hat(c_out) = sum a_k hat(c_k) AS
      POLYNOMIALS; one common-point opening certifies it up to m/|F|.
      No sumcheck rounds.  No carries.  No range checks.

      SIDE CONDITION, and it is satisfiable two ways:
        (i)  lazy accumulation -- 109 bits in u128 leaves 19 spare, so a
             <=512-add fold needs NO reduction.  MEASURED 0.88x, i.e. the
             representation that deletes the proof relation is also FASTER FHE.
        (ii) a KoalaBear-matched limb: reduction mod q_j IS field arithmetic.

      COST SCALING.  Any AIR must contain every addition it constrains:
         AIR route      Theta(B * N * L)  committed elements   <- ~ the ADDITIONS
         linear route   Theta(N * L)      committed elements   <- ~ the RESULT
      ratio = B, the fold width.  And the operands are ALREADY committed by
      the protocol, so the true MARGINAL cost of a fold is the output only:""")
for B in (4,64,512):
    air = B*CT*2*sum(per_element(4,20,int(log2(B*CT))+1))
    lin = CT*2*sum(per_element(4,48,17))
    print(f"        B={B:>4}: hypothetical AIR {air:.2e}  vs linear {lin:.2e}  = {air/lin:>6.0f}x")
print("""
  (c) ct x pt : degree-3 zerocheck over m=log2(24576)->15 vars.
      prover 2*2^15*(d-1)*k*10 = 2.6M mult-equiv = 0.5 ms.  NOT the cost.
  (d) ct x ct + relin : tensor is degree 2 -> one more degree-3 zerocheck.
      The key-switch is a FIXED PUBLIC LINEAR MAP on the DIGIT DECOMPOSITION.
      Public + linear = free.  So the ENTIRE cost of ct x ct is the RANGE
      CHECKS ON THE KEY-SWITCH DIGITS.  In RNS-BV the digits ARE the limbs,
      so a proof-field-matched limb deletes 1/3 of them by construction.
""")

# ===========================================================================
# 4.  WORKLOAD 2 -- ML
# ===========================================================================
print("="*79); print("4.  WORKLOAD 2 -- ML matmul"); print("="*79)
n = 4096
print(f"""
  Y = W X, W is {n}x{n}, X is {n}xB.  Sumcheck on
      hat(Y)(i,j) = sum_k hat(W)(i,k) hat(X)(k,j), bind i->r_i, j->r_j.
  PROVER: fold hat(W) over i  -> n^2 mults      <- DOMINANT
          fold hat(X) over j  -> n*B mults
          sumcheck over log n -> O(n)
  PLAINTEXT: n^2 B.   OVERHEAD = (n^2 + nB)/(n^2 B) = 1/B + 1/n.
""")
for B,note in [(1,"DECODE -- the proof costs AS MUCH AS the inference"),(8,""),(64,""),
               (512,"<== THIS is Thaler '13's 0.18-0.33% band"),(4096,"B=n, the square matmul Thaler measured")]:
    print(f"    B={B:>5}  overhead {(1/B+1/n)*100:>8.3f}%   {note}")
print(f"""
  ** Thaler's 0.18-0.33% is the B ~ n case.  At B=1 the SAME construction has
     ~100% overhead.  Autoregressive DECODE is B=1.  The famous number does
     not apply to the workload everyone wants to prove. **

  THE FLOOR: Omega(#weights) field ops PER PROOF.  Evaluating an MLE at a
  fresh random point is <w, eq_r>; eq_r has full support off the hypercube;
  so every coefficient must be read.  IRREDUCIBLE for a fresh challenge.""")
for name,p in [("GPT-2 124M",124e6),("Llama-3-8B",8e9),("70B",70e9)]:
    print(f"    {name:<12} {p:>8.3g} params -> {p*MUL_PACKED_NS/1e9:>7.2f} s/core, "
          f"{p*MUL_PACKED_NS/1e9/12:>6.3f} s @12 cores, {p/200e9:>6.3f} s @200 Gmul/s GPU")
print("""    (a 7B decode step is memory-bound at ~14 GB / ~1 TB/s ~ 15-100 ms.
     So the matmul-proof FLOOR is the SAME ORDER as the inference itself.)
  ESCAPE: amortise the CHALLENGE across tokens -- prove T tokens under one
  challenge, floor per token = #weights/T.  That is a proof-GRANULARITY
  decision, not a prover optimisation.
""")
print("-"*79); print("  THE FULL FORWARD PASS -- where the cost actually is"); print("-"*79)
SITES, EQ, EB = 165_150_720, 34.0, 11.0
print(f"""  MEASURED (zkml-research/phase0/results_cost_model.txt), GPT-2 seq 512:
     renormalisation sites {SITES:,}
     committed elements: quantized {SITES*EQ:,.0f} ({EQ:.0f}/site) | bf16 {SITES*EB:,.0f} ({EB:.0f}/site)
  DECOMPOSING the {EQ:.0f}/site, from the harness's own substrate read of p3-lookup:
     10 committed base columns
   +  6 LogUp lookups x 4 base felts (ONE EXTENSION aux column per lookup per row)
  => {6*4/EQ*100:.0f}% OF EVERY COMMITTED ELEMENT IN A zkML PROOF IS A LogUp
     EXTENSION-FIELD RUNNING-SUM COLUMN.  That is the dominant term; its cause
     is one aux column per lookup per row.

  Information content of a site: one 8-bit activation.  Committed: {EQ:.0f}*31 = {EQ*31:.0f} bits.
     BLOW-UP {EQ*31/8:.0f}x  =  {31/8:.2f}x field embedding  x  {EQ:.0f}x protocol
""")
def wl(el,b=4,w=64,lh=24): return SITES*el*sum(per_element(b,w,lh))
for lab,el in [("quantized (DeepProve shape)",EQ),("bf16 exact tables",EB)]:
    c = wl(el)
    print(f"    {lab:<28}: {c:.3e} mult-equiv = {c*MUL_PACKED_NS/1e9/12:>8.0f} s @12 cores,"
          f" {c/200e9:>7.1f} s @200 Gmul/s GPU")
floor = SITES*8/(248/KB_OPEQ)
print(f"""    THREE FLOORS, nested:
     (F-info) commit {SITES:,} x 8 bits = {SITES*8/8/1e6:.0f} MB at rate 1.
       Poseidon2-KB absorbs 8*31=248 bits per {KB_OPEQ:.0f} op-equiv = {248/KB_OPEQ:.3f} bits/op.
       -> {floor:.3e} op-equiv = {floor*MUL_PACKED_NS/1e9/12:.2f} s @12 cores, {floor/200e9:.3f} s @GPU
     (F-fri)  x2 for rate 1/2 -- a hash-based PCS needs distance:  {floor*2*MUL_PACKED_NS/1e9/12:.2f} s @12c
     (F-blake) F-info with a bit-oriented hash instead: /{BLAKE3/kb_gbit:.1f} = {floor/(BLAKE3/kb_gbit)*MUL_PACKED_NS/1e9/12:.3f} s @12c

    GAP F-info -> bf16      : {wl(EB)/floor:>5.0f}x
    GAP F-info -> quantized : {wl(EQ)/floor:>5.0f}x
    AND IT FACTORS EXACTLY:  {EQ*31/8:.0f}x element blow-up  x  {2**4}x (lb=4)  x {wl(EQ)/floor/(EQ*31/8)/16:.2f}x encode+sumcheck
    ** {EQ*31/8:.0f}x of the {wl(EQ)/floor:.0f}x is the PROTOCOL committing 34 felts per 8-bit value.
       {2**4}x is the RATE.  Only ~{wl(EQ)/floor/(EQ*31/8)/16:.1f}x is anything else. **
""")
print("-"*79); print("  PRICING LogUp-GKR (workstream card G4) -- derived"); print("-"*79)
pe = sum(per_element(4,64,24))
before = EQ*pe; after = 10*pe + 6*2*((3-1)*2*10)
print(f"""     before : {EQ:.0f} committed x {pe:.0f} mult-equiv        = {before:>10,.0f} /site
     after  : 10 committed x {pe:.0f}                = {10*pe:>10,.0f} /site
              + fraction tree, 6 fracs x 2 nodes    = {6*2*((3-1)*2*10):>10,.0f} /site
              total                                 = {after:>10,.0f} /site
     SPEEDUP = {before/after:.2f}x
  Largest available lever in the ML workload; attacks the dominant term AT ITS
  CAUSE; both halves already in-tree (prover/src/tower256_kernels.rs::
  fraction_add_layer is the driverless char-2 fraction-tree kernel; the Selvage
  sumcheck protocol layer is already degree-generic).
""")
print("-"*79); print("  THE TRAP: batching lookups into fewer aux columns"); print("-"*79)
b4, b6 = sum(per_element(4,64,24)), sum(per_element(6,64,24))
print(f"""  p3-lookup CAN batch fractions into one aux column via a common denominator,
  at constraint degree ~1+batch.  6 lookups -> 1 takes 34 -> 14 elements/site
  ({EQ/14:.2f}x fewer).  But degree 7 forces quotient degree 6 forces lb >= 6 (MEASURED:
  38/91 goldens refuse below that with the deg-7 chip).
     per-element lb=4 {b4:.0f}  ->  lb=6 {b6:.0f}   ({b6/b4:.2f}x dearer)
     net {EQ/14:.2f}x fewer x {b6/b4:.2f}x dearer = {14*b6/(EQ*b4):.2f}x  ->  a {EQ*b4/(14*b6):.2f}x LOSS.
  VERDICT: lookup batching is a LOSS unless the batch degree stays inside the
  existing quotient degree.  aux columns <-> constraint degree <-> blowup <->
  hash work: that chain IS the cost structure.
""")

# ===========================================================================
# 5.  WORKLOAD 3 -- the turn
# ===========================================================================
print("="*79); print("5.  WORKLOAD 3 -- a kernel semantic turn"); print("="*79)
TW, TK, TPI, TP2 = 1804, 706, 61, 142
ROWS = 64
print(f"""  MEASURED (deployed wide `transferVmDescriptor2R24`, Lean-emitted IR-v2):
     trace_width {TW}   constraints {TK}   public inputs {TPI} (only 29 pinned)
     Poseidon2 chip lookups {TP2}   range lookups 218   main rows {ROWS} (floor 2^6)
     committed base felts, main table = {ROWS*TW:,}
     one map-op row = 84 Poseidon2 perms (4 arity-3 leaf absorbs + 5 x 16
     node folds at HEAP_TREE_DEPTH=16, HEAP_LEAF_ARITY=3)
     one cap-open   = 17 perms

  MEASURED WALL-CLOCK (M2 Max 12c, .docs-history-noclaude/PERFORMANCE.md):
     executor execute (the turn itself)   7.0 us
     witness generation                 319 us
     prove_full_turn                    147 ms   <- multiplier 21,000x
     of which: descriptor leg 52 ms, recursion/PI binding ~95 ms
     verify_full_turn                   149 ms   |  wire 169 KiB

  MEASURED COHORTS -- and this is the whole answer for workload 3:
     map_write_chip        227 ms   (one sorted-Poseidon2 write on the chip bus)
     absent_chip           137 ms
     umem_write_read_nochip 14.9 ms  (SAME INTENT, no in-circuit hashing)
     ==> {227/14.9:.1f}x.  The in-circuit Merkle path is {227/14.9:.0f}x the same state access
         expressed without it, and the cheaper path IS ALREADY BUILT.
""")
GENUINE = 5*16*8 + 8*4 + 61   # 5 sibling paths x 16 x 8-felt digests + leaves + PIs
print(f"""  THE FLOOR for a turn.  Genuine witness: 5 sibling paths x 16 levels x 8
  felts = {5*16*8} + leaves/values ~{8*4} + {TPI} PIs = ~{GENUINE:,} felts.
     committed today (main table alone) {ROWS*TW:,} felts -> blow-up {ROWS*TW/GENUINE:.0f}x
     hash floor: {GENUINE:,} felts * 31 bits / {248/KB_OPEQ:.3f} bits-per-op
                 = {GENUINE*31/(248/KB_OPEQ):.2e} op-equiv = {GENUINE*31/(248/KB_OPEQ)*MUL_PACKED_NS/1e6:.3f} ms
     MEASURED 147 ms  ->  GAP TO FLOOR = {147e-3/(GENUINE*31/(248/KB_OPEQ)*MUL_PACKED_NS/1e9):.0f}x

  WHERE IT GOES.  These are a DECOMPOSITION, not independent multipliers --
  they overlap and their product over-counts.  Each is measured separately:
     2.83x  recursion / PI binding: 95 of the 147 ms is a SECOND proof over
            the first.  MEASURED (descriptor leg 52 ms).
     2.9x   lb=6 vs the measured optimum lb=4.  MEASURED on the (lb,q) grid.
     15.2x  in-circuit Poseidon2 for state authentication -- but this bites
            the CHIP cohorts (227 ms), not the umem transfer.  MEASURED.
     {ROWS*TW/GENUINE:.0f}x    geometry: 64 rows x 1804 columns committed for ~{GENUINE:,} felts of
            real witness.  The 64-row floor plus a 1804-wide union-of-all-verbs
            trace is the single largest structural waste, and a 1-effect turn
            pays all of it.
  The honest compounded statement: the two INDEPENDENT config levers (recursion
  shape, blowup) are ~8x; the geometry is a further ~{ROWS*TW/GENUINE:.0f}x that needs a
  per-verb trace rather than a union trace.
""")

# ===========================================================================
# 6.  HASH CHOICE
# ===========================================================================
print("="*79); print("6.  THE ONLY HASH FIGURE OF MERIT: BITS PER UNIT ALU"); print("="*79)


print(f"""     Poseidon2-BabyBear  : 248 bits / {BB_OPEQ:.0f} op-equiv = {248/BB_OPEQ:.3f} bits/op
     Poseidon2-KoalaBear : 248 bits / {KB_OPEQ:.0f} op-equiv = {248/KB_OPEQ:.3f} bits/op  ({BB_OPEQ/KB_OPEQ:.2f}x)
     Blake3 (M2 1 core)  : {BLAKE3:.1f} Gbit/s  vs Poseidon2-KB {kb_gbit:.2f} Gbit/s  ({BLAKE3/kb_gbit:.1f}x)
  Blake3 is {BLAKE3/kb_gbit:.1f}x faster natively and ~1000x worse in-circuit.  So use a
  bit-oriented hash at every LEAF that is never re-verified inside a circuit,
  and Poseidon2 only where a proof verifies a proof.  We use Poseidon2
  everywhere.  At 57% of prover time that is a ~2x standing loss on the
  non-recursed legs.
""")

# ===========================================================================
# 7.  RANKED REMOVALS
# ===========================================================================
print("="*79); print("7.  RANKED: WHAT COULD BE REMOVED AND WHAT IT BUYS"); print("="*79)
rows = [
 ("BFV: delete the butterfly AIR, prove the public linear map by sumcheck",
  f"{AIR6/SCKB:.0f}x", "FHE", "exponent (interior->boundary)"),
 ("Turn: state membership as a PCS OPENING, not an in-circuit Merkle path",
  "15x", "turn", "constant, measured in-tree"),
 ("ML: LogUp-GKR -- kill the committed extension aux column",
  f"{before/after:.1f}x", "ML", "constant on the dominant term"),
 ("ALL: lb 6 -> 4 (measured optimum; lb=6 buys a WITHDRAWN regime)",
  "2.9x", "all", "constant"),
 ("ALL: KoalaBear -- 1.9x on the perm AND unlocks lb=2 (a=3 quotient)",
  f"{P2_MULS_BB/KB_PERM*2:.1f}x", "all", "constant"),
 ("ALL: bit-oriented hash on non-recursed leaves",
  "~2x", "all", "constant"),
 ("ML: pack 4-bit weights / 8-bit activations (Binius ring-switch)",
  f"{31/8:.1f}x", "ML", "constant"),
 ("ML: amortise the challenge across T tokens",
  "T", "ML", "exponent in the deployment"),
 ("BFV: fold_add as a linear relation (no AIR ever written)",
  "B (fold width)", "FHE", "exponent"),
 ("Turn: fix the 64-row floor / 1804-col width for 1-effect turns",
  f"~{ROWS*TW/GENUINE:.0f}x", "turn", "constant"),
]
print(f"  {'lever':<66} {'buys':>10}  {'kind'}")
for a,b_,c,d in rows: print(f"  {a:<66} {b_:>10}  {d}")
print("""
  COMPOUNDING, honestly: the four ALL-rows multiply (2.9 x 3.8 x 2 ~ 22x) only
  if the terms are independent.  They are not -- lb and the field both act on
  the hash term, so their product is real, while the Blake3 row and the lb row
  BOTH shrink hashing and partially overlap.  A defensible compounded estimate
  on the shared substrate is 8-15x, before any per-workload lever.
""")
