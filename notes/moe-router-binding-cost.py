#!/usr/bin/env python3
"""Refined derivation: statement variants priced with committed-vs-virtual split,
tie probability at each selection boundary, and the sampling composition."""

DSV3 = dict(hidden_size=7168, intermediate_size=18432, moe_intermediate_size=2048,
            num_hidden_layers=61, first_k_dense_replace=3, n_routed_experts=256,
            n_shared_experts=1, num_experts_per_tok=8, n_group=8, topk_group=4)

d = DSV3["hidden_size"]; f = DSV3["moe_intermediate_size"]
E = DSV3["n_routed_experts"]; k = DSV3["num_experts_per_tok"]
G = DSV3["n_group"]; PG = E // G; KG = DSV3["topk_group"]
KA = k + DSV3["n_shared_experts"]
L = DSV3["num_hidden_layers"] - DSV3["first_k_dense_replace"]
LIMBS = 2   # 29-bit composite key -> 16-bit + 13-bit limb lookups

# The three nested selections in DeepSeek-V3's noaux_tc router.
STAGES = [("group-inner top-2 of 32", PG, 2, G),
          ("group top-4 of 8",        G,  KG, 1),
          ("expert top-8 of 256",     E,  k, 1)]

def variant_a():
    """Sorted-permutation form. Keys are injective (they embed the index), so the
    sorted array alone suffices; indices are recovered by decomposing the k keys."""
    commit = rc = logup = 0
    for _, n, kk, rep in STAGES:
        commit += rep * n            # the sorted key array
        commit += rep * kk           # decomposed index of each selected key
        rc     += rep * (n - 1)      # sortedness: adjacent differences
        rc     += rep * kk           # index decomposition range
        logup  += rep * 2 * n        # multiset argument: both sides
    return dict(commit=commit, rc=rc, rc_lookups=LIMBS*rc, logup=logup,
                batch_inv_mults=3*(logup-1), inversions=1)

def variant_b(materialise_slack: bool):
    """Threshold form. Witness tau; every element gets one signed slack that is
    range-checked. The slack is a degree-2 expression in committed values, so it
    is a real column only if the proof system needs low degree."""
    commit = rc = 0
    for _, n, kk, rep in STAGES:
        commit += rep * n            # the {0,1} selection indicators
        commit += rep * 1            # tau
        if materialise_slack:
            commit += rep * n
        rc     += rep * n            # one range check per element
        rc     += rep * 1            # tau itself MUST be range-checked (wraparound)
    return dict(commit=commit, rc=rc, rc_lookups=LIMBS*rc, logup=0,
                batch_inv_mults=0, inversions=0)

def layer_costs(sel):
    expert_commit = 4*f + d
    experts_commit = KA*expert_commit + d
    experts_nonlin = KA*f
    experts_requant = KA*(f + f + d)
    experts_macs = KA*3*d*f
    router_commit = E + E + sel['commit'] + G + k + 1   # logits, sigmoids, sel, Gscores, gates, Dinv
    router_lookups = E + sel['rc_lookups']
    return dict(experts_commit=experts_commit,
                experts_lookups=experts_nonlin+experts_requant,
                experts_nonlin=experts_nonlin, experts_requant=experts_requant,
                experts_macs=experts_macs,
                router_commit=router_commit, router_lookups=router_lookups,
                router_macs=E*d,
                dense_commit=(E+1)*expert_commit + d,
                dense_lookups=(E+1)*(f + f + f + d),
                dense_macs=(E+1)*3*d*f)

F = lambda n: f"{n:,}"
print("="*78)
print("STATEMENT VARIANTS — per token per MoE layer, SELECTION ARGUMENT ONLY")
print("(both variants additionally pay the 256 logits + 256 sigmoid lookups)")
print("="*78)
a  = variant_a()
bv = variant_b(False)
bm = variant_b(True)
print(f"{'':32}{'commit':>9}{'rangechk':>10}{'rc lookups':>12}{'LogUp':>8}{'extra mults':>13}")
for name, v in [("(a) sorted permutation", a),
                ("(b) threshold, slack virtual", bv),
                ("(b) threshold, slack as column", bm)]:
    print(f"{name:32}{F(v['commit']):>9}{F(v['rc']):>10}{F(v['rc_lookups']):>12}"
          f"{F(v['logup']):>8}{F(v['batch_inv_mults']):>13}")
print()
print(f"  committed-column ratio (a)/(b,virtual) = {a['commit']/bv['commit']:.2f}x")
print(f"  (b) eliminates the multiset argument entirely: {F(a['logup'])} LogUp terms,")
print(f"      {F(a['batch_inv_mults'])} batch-inversion mults and 1 field inversion, per token per layer.")
print(f"  (b) pays for it with {bv['rc']-a['rc']} extra range checks. NET: (b) wins.")
print()

print("="*78)
print("FULL PROOF COST — per token per MoE layer, variant (b) slack-virtual")
print("="*78)
c = layer_costs(bv)
sc = c['experts_commit']+c['router_commit']
sl = c['experts_lookups']+c['router_lookups']
sm = c['experts_macs']+c['router_macs']
dc = c['dense_commit']+c['router_commit']
dl = c['dense_lookups']+c['router_lookups']
dm = c['dense_macs']+c['router_macs']
print(f"{'':40}{'committed':>12}{'lookups':>12}{'MACs':>16}")
print(f"{'9 active experts':40}{F(c['experts_commit']):>12}{F(c['experts_lookups']):>12}{F(c['experts_macs']):>16}")
print(f"{'   SiLU nonlinearity':40}{'':>12}{F(c['experts_nonlin']):>12}")
print(f"{'   requantisation':40}{'':>12}{F(c['experts_requant']):>12}")
print(f"{'router matmul + binding (b)':40}{F(c['router_commit']):>12}{F(c['router_lookups']):>12}{F(c['router_macs']):>16}")
print(f"{'SPARSE + BOUND (the proposal)':40}{F(sc):>12}{F(sl):>12}{F(sm):>16}")
print(f"{'BASELINE: prove all 257 experts':40}{F(dc):>12}{F(dl):>12}{F(dm):>16}")
print(f"{'DISCOUNT':40}{dc/sc:>11.1f}x{dl/sl:>11.1f}x{dm/sm:>15.1f}x")
print()
print("PRICE OF SOUNDNESS — router binding as a share of the sparse proof:")
print(f"   committed {c['router_commit']}/{sc} = {100*c['router_commit']/sc:.2f}%   "
      f"lookups {c['router_lookups']}/{sl} = {100*c['router_lookups']/sl:.2f}%   "
      f"MACs {100*c['router_macs']/sm:.2f}%")
print(f"   of which the SELECTION ARGUMENT proper: {bv['commit']} committed "
      f"= {100*bv['commit']/sc:.2f}% of the sparse proof")
print()
print(f"Per token, all {L} MoE layers:")
print(f"   sparse+bound committed {F(L*sc)}   baseline {F(L*dc)}")
print(f"   router binding         {F(L*c['router_commit'])} committed, {F(L*c['router_lookups'])} lookups")
print(f"   selection indices      {L*k} bytes/token (8 indices x 1 byte x {L} layers)")
print()

print("="*78)
print("TIE PROBABILITY AT EACH SELECTION BOUNDARY (why the tie-break is not optional)")
print("="*78)
print("Model: scores spread over the representable range; the gap between adjacent")
print("order statistics of n samples is ~1/n of the range, so P[boundary tie] ~ n/2^b.")
print(f"{'fixed-point bits b':>20}{'top-2 of 32':>16}{'top-4 of 8':>16}{'top-8 of 256':>16}")
for b in (16, 20, 24, 28):
    p32 = PG/2**b * G     # 8 independent group boundaries
    p8  = G/2**b
    p256= E/2**b
    print(f"{b:>20}{p32:>16.2e}{p8:>16.2e}{p256:>16.2e}")
print()
print("Read as: 1-in-N tokens has an ambiguous boundary somewhere, by chance alone.")
for b in (16, 20, 24, 28):
    tot = PG/2**b*G + G/2**b + E/2**b
    print(f"   b={b}: any-boundary tie ~ {tot:.2e}  = 1 in {1/tot:,.0f} tokens; "
          f"an adversary choosing inputs finds one in ~{1/tot:,.0f} forward passes")
print()

print("="*78)
print("SAMPLING COMPOSITION — AuditSampling q = p(1-eps_chk) - eps_bind - eps_beacon")
print("="*78)
print("Checker = re-derive routing for a sampled TOKEN (all layers). A round of n")
print("tokens with c routed dishonestly has eps_chk = 1 - c/n (the sampled token")
print("misses the cheat), so q(c) = p*c/n - eps, eps = eps_bind + eps_beacon.")
print()
print("Stolen work before the first alarm <= b/q with payload b = c*w:")
print("   c*w / (p*c/n - eps) = w*n*c / (p*c - n*eps)   ->   w*n/p  when eps = 0,")
print("   INDEPENDENT of how many tokens the prover cheats on.")
print()
print(f"{'n (tokens/round)':>18}{'p':>8}{'eps':>10}{'undetectable floor c*':>24}{'stolen (units of w)':>22}")
for n in (256, 4096):
    for p in (0.01, 0.05):
        for eps in (0.0, 1e-6, 1e-3):
            cstar = n*eps/p
            # worst-case stolen work: take c just above the floor -> unbounded;
            # report the eps=0 uniform bound and the floor separately
            stolen = n/p if eps == 0 else float('inf')
            s = f"{stolen:,.0f}" if stolen != float('inf') else "unbounded above c*"
            print(f"{n:>18}{p:>8}{eps:>10}{cstar:>24.4f}{s:>22}")
print()
print("Auditor cost, derived:")
router_all_layers = L*E*d
full_token = 36_624_596_992
print(f"   re-derive ALL {L} routers for one token: {F(router_all_layers)} MACs")
print(f"   full honest forward pass for one token:  {F(full_token)} MACs")
print(f"   ratio = {100*router_all_layers/full_token:.2f}%  ->  auditing every layer of a")
print(f"   sampled token is essentially free; NEVER sample (token,layer) cells, which")
print(f"   would dilute eps_chk by a further factor of {L}.")
