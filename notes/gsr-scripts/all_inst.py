from math import log2
def gsr(t, a, pb, k, Rp, Rf1=4):
    skip = max(0, min(Rp, t-2*k)); un = Rp-skip; g = un+Rf1
    d = a**g; D = d**(2**(k-1))
    return dict(skip=skip, g=g, d_bits=log2(d), t_bits=2*log2(D)+log2(pb),
                m_bits=log2(D)+log2(pb), reach=1+Rp+Rf1, total=8+Rp)
BAR=123.6
print(f"{'instance':<34}{'t':>3}{'a':>3}{'RP':>4}{'tot':>5}  {'skip':>7} {'reach':>6} {'log2 d':>7} {'time':>8} {'vs 2^31':>9}")
for nm,t,a,Rp,pb in [("BabyBear w16 (DEPLOYED)",16,7,13,31),
                     ("BabyBear w24 (seg-digest)",24,7,21,31),
                     ("BN254 w3 (outer wrap)",3,5,56,254),
                     ("Poseidon KoalaBear (paper)",24,3,23,31)]:
    for k in (1,2):
        r = gsr(t,a,pb,k,Rp)
        brute = pb*k
        print(f"{nm+' k='+str(k):<34}{t:>3}{a:>3}{Rp:>4}{r['total']:>5}  {str(r['skip'])+'/'+str(Rp):>7} "
              f"{str(r['reach'])+'/'+str(r['total']):>6} {r['d_bits']:>7.1f} {'2^'+format(r['t_bits'],'.1f'):>8} "
              f"{'BEATS' if r['t_bits']<brute else 'no gain':>9} (brute 2^{brute})")
print()
print("--- repair sweep, DEPLOYED w16 (t=16, a=7, RF=8): what each extra partial round buys ---")
for Rp in range(13,23):
    r1=gsr(16,7,31,1,Rp); r2=gsr(16,7,31,2,Rp)
    # deepest total round count still beaten at k=1
    deep=0
    for R2 in range(0,Rp+1):
        rr=gsr(16,7,31,1,R2)
        if rr['t_bits']<31: deep=max(deep,1+R2+4)
    print(f"  RP={Rp:>2} tot={8+Rp:>2}  CICO-1 full-RP time=2^{r1['t_bits']:>5.1f} "
          f"{'BEATS 2^31' if r1['t_bits']<31 else 'DEAD      '}  deepest reach={deep:>2}  "
          f"MARGIN={8+Rp-deep:>2} rounds   sboxes={8*16+Rp:>3} (+{Rp-13} vs deployed, +{2.13*(Rp-13):.1f} cells, +{100*2.13*(Rp-13)/300:.1f}%)")
