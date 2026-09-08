//! `[PROVER-sumcheck]` — the sumcheck ENGINE over a multilinear hypercube table,
//! mirroring `Selvage/MultilinearExtension.lean`'s `mle`/`roundSum` machinery.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE with the Lean sumcheck verifier
//! as its specification. The Lean side proved the sumcheck sound
//! (`mle_sumcheck_soundness`, the round chain `roundSum_zero`/`roundSum_succ`/
//! `roundSum_last`, degree via `roundSum_affine`) about ITS objects; this file
//! re-computes the same shapes in Rust so the prover produces the claim the Lean
//! proved sound. There is no formal semantics of Rust, so the agreement is
//! established by CONFORMANCE VECTORS
//! (`prover/testdata/sumcheck_conformance.json`, written by the Lean `#eval` in
//! `Compiler/SumcheckConformance.lean` from the REAL `mle`/`roundSum`) — never
//! called refinement or verification. Agreement on vectors is the whole claim.
//!
//! The mirrored semantics (Selvage, `Cube` section):
//! * `chi_eval` = `chiEval b x = ∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)`;
//! * `mle_eval` = `mle f x = Σ_b f(b)·χ_b(x)` (WHIR Def 4.5's `f̂`);
//! * `round_sum` = `roundSum g r i t = Σ_{b ∈ {0,1}^{m−i−1}} g(r₀,…,r_{i−1}, t, b)`
//!   at `g = mle f` — challenges strictly below `i`, the running variable at `i`,
//!   boolean corners above (entries of `r` at ≥ `i` are never read, the mirror of
//!   `roundSum_congr_prefix`);
//! * `round_poly` = round `i`'s message as its evals `[gᵢ(0), gᵢ(1)]` — degree ≤ 1
//!   for a multilinear `g` (`roundSum_affine`), so two points determine it; the
//!   Lean `roundPoly` carries the same data as coefficients
//!   `C(gᵢ(1)−gᵢ(0))·X + C(gᵢ(0))`.
//!
//! **Index convention** (pinned by the conformance vector): the table `f` has
//! length `2^m` and index bit `i` (LSB-first) is cube coordinate `i` — Lean's
//! `bitsToIdx b = Σᵢ (if bᵢ then 2^i else 0)`. Round `i` binds coordinate `i`.
//!
//! Challenges are CALLER-SUPPLIED (fixed, for the conformance vector); drawing
//! them from a Fiat-Shamir transcript is `[PROVER-fs]`, not this rung. The
//! gate-constraint → hypercube-table encoding (the descriptor's gates as the
//! R1CS-style `Â·B̂−Ĉ` claim of `Assurance/AirSumcheckQuadratic`, degree-2 round
//! polynomials) is the NEXT rung, `[PROVER-sumcheck-gates]` — this file is the
//! degree-≤1 engine it will drive. Perf note: `round_sum` is the LITERAL mirror
//! (O(2^m) MLE evals per point); the standard table-folding optimization arrives
//! only when a rung needs it, and will be conformance-checked against this mirror
//! (`mle_kernels::fold_mle_table` is the folding kernel already in the crate).
//!
//! ## The degree-3 rung (`cubic` items below)
//!
//! `Assurance/AirSumcheckCubic.lean` builds the degree-3 realizer
//! `cubicForm E A B C D = Ê·(Â·B̂ + Ĉ·D̂)` — one shape covering BOTH a GKR
//! fraction-tree layer (`eq·(p_L·q_R + p_R·q_L)`) and a zkML matmul claim
//! (`eq·(Â·B̂ − Ĉ)`), each named there as a theorem. This file re-computes that
//! engine, at TWO speeds that are checked against each other:
//!
//! * `cubic_round_sum_literal` — the LITERAL mirror of the Lean `roundSum
//!   (cubicForm …)`, O(4^m), the thing the conformance vector binds;
//! * `fold_table` + `cubic_round_evals` — the folded prover, O(2^m) TOTAL, which
//!   is what lifts the rung off its `m ≈ 12` ceiling.
//!
//! `folded_prover_agrees_with_literal_mirror` pins the fast path to the mirror,
//! so the Lean binding survives the optimization instead of being replaced by it.
//!
//! **`h(1)` is on the wire.** A degree-3 round message is FOUR evaluations
//! `[h(0), h(1), h(2), h(3)]`. The p3-sumcheck engine sends `[h(0), h(∞)]` and
//! lets the verifier DERIVE `h(1) = claim − h(0)`, which makes its round check
//! `h(0) + h(1) = claim` true by construction — the check is not skipped, it is
//! made a tautology. Here `h(1)` is prover-supplied and the round check can fail;
//! `no_message_passes_both_checks` exhibits the resulting fork: against a false
//! claim, the honest `h(1)` fails the ROUND check and the derived `h(1)` fails the
//! TERMINAL check, and there is no third option. Cost of not compressing: one
//! field element per round.
//!
//! **Interpolation needs `p > 3`.** `eval_lagrange` divides by the node
//! differences of `{0,1,2,3}`, whose denominators are `±6, ±2`; it returns `None`
//! when the modulus makes them non-invertible and the verifier REJECTS on `None`
//! rather than folding a wrong value. This is why the Lean side keeps the round
//! polynomial in COEFFICIENT form (no division, no characteristic hypothesis):
//! the char-2 binary-tower instantiation cannot use these nodes at all and will
//! need coefficient-form messages, which is an open fork, not an oversight.

/// A canonical residue mod the caller's prime `p` (`0 ≤ v < p`). The engine is
/// prime-generic so the Lean `MLEExample` keystones over F₅ bind here too;
/// the conformance vector instantiates `p = crate::babybear::P`.
pub type Fp = u64;

pub(crate) fn add_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + b as u128) % p as u128) as u64
}

pub(crate) fn sub_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 + p as u128 - b as u128 % p as u128) % p as u128) as u64
}

pub(crate) fn mul_mod(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 * b as u128) % p as u128) as u64
}

/// `m` from a table of length `2^m`. Panics on a non-power-of-two length —
/// there is no hypercube it could be a table of.
fn cube_dim(f: &[Fp]) -> usize {
    assert!(
        !f.is_empty() && f.len().is_power_of_two(),
        "table length {} is not a power of two",
        f.len()
    );
    f.len().trailing_zeros() as usize
}

/// Mirror of `chiEval`: `χ_b(x) = ∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)`, with corner
/// `b` given as an index (bit `i` = coordinate `i`).
pub fn chi_eval(b: usize, point: &[Fp], p: u64) -> Fp {
    point.iter().enumerate().fold(1 % p, |acc, (i, &x)| {
        let factor = if (b >> i) & 1 == 1 {
            x % p
        } else {
            sub_mod(1 % p, x, p)
        };
        mul_mod(acc, factor, p)
    })
}

/// Mirror of `mle`: the multilinear extension `f̂(x) = Σ_b f(b)·χ_b(x)` of a
/// hypercube table `f` (length `2^m`) at a point (length `m`) — the literal
/// chi-basis sum, matching the Lean definition shape for shape.
pub fn mle_eval(f: &[Fp], point: &[Fp], p: u64) -> Fp {
    let m = cube_dim(f);
    assert_eq!(
        point.len(),
        m,
        "point dimension {} != table dimension {m}",
        point.len()
    );
    f.iter().enumerate().fold(0, |acc, (b, &v)| {
        add_mod(acc, mul_mod(v % p, chi_eval(b, point, p), p), p)
    })
}

/// Mirror of `roundSum` at `g = mle f`: round `i`'s partial sum
/// `gᵢ(t) = Σ_{b ∈ {0,1}^{m−i−1}} f̂(r₀,…,r_{i−1}, t, b)`. `r` must have length
/// `m`; entries at positions ≥ `i` are never read (`roundSum_congr_prefix`).
pub fn round_sum(f: &[Fp], r: &[Fp], i: usize, t: Fp, p: u64) -> Fp {
    let m = cube_dim(f);
    assert_eq!(
        r.len(),
        m,
        "challenge vector length {} != dimension {m}",
        r.len()
    );
    assert!(i < m, "round index {i} out of range (m = {m})");
    let suffix = m - i - 1;
    let mut point: Vec<Fp> = Vec::with_capacity(m);
    let mut acc = 0;
    for b in 0..1usize << suffix {
        point.clear();
        point.extend_from_slice(&r[..i]);
        point.push(t % p);
        for j in 0..suffix {
            point.push(((b >> j) & 1) as u64);
        }
        acc = add_mod(acc, mle_eval(f, &point, p), p);
    }
    acc
}

/// Round `i`'s polynomial `gᵢ` as its evaluations `[gᵢ(0), gᵢ(1)]` — degree ≤ 1
/// for a multilinear table (`roundSum_affine`), so two points interpolate it.
/// The same data as the Lean `roundPoly`'s coefficients.
pub fn round_poly(f: &[Fp], r: &[Fp], i: usize, p: u64) -> Vec<Fp> {
    vec![round_sum(f, r, i, 0, p), round_sum(f, r, i, 1, p)]
}

/// Evaluate a degree-≤1 round polynomial given as `[g(0), g(1)]` at `t`:
/// the two-point interpolation `(1 − t)·g(0) + t·g(1)` (`roundSum_affine`'s
/// right-hand side).
pub fn eval_affine(evals: &[Fp], t: Fp, p: u64) -> Fp {
    assert_eq!(
        evals.len(),
        2,
        "degree-<=1 round polynomial has exactly 2 evals"
    );
    add_mod(
        mul_mod(sub_mod(1 % p, t, p), evals[0], p),
        mul_mod(t % p, evals[1], p),
        p,
    )
}

/// The full sumcheck transcript for the claim `Σ_b f(b)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumcheckProof {
    /// The claimed total `H = Σ_b f(b)` (honest prover: the true sum).
    pub claim: Fp,
    /// Per round `i`, the message `gᵢ` as `[gᵢ(0), gᵢ(1)]`.
    pub rounds: Vec<Vec<Fp>>,
    /// The challenges `rᵢ` folded in after each round — caller-supplied here
    /// (fixed for conformance); Fiat-Shamir drawing is `[PROVER-fs]`.
    pub challenges: Vec<Fp>,
}

/// The honest sumcheck prover: claim `Σ_b f(b)`, then per round the message
/// `gᵢ = [gᵢ(0), gᵢ(1)]` with challenge `rᵢ` folded in. By construction the
/// transcript satisfies the Lean-proved chain: `g₀(0)+g₀(1) = claim`
/// (`roundSum_zero` + `mle_hypercube_sum`), `g_{k+1}(0)+g_{k+1}(1) = g_k(r_k)`
/// (`roundSum_succ`), and `g_{m−1}(r_{m−1}) = f̂(r)` (`roundSum_last`) — the
/// tests EXERCISE these identities, they do not prove them.
pub fn prove_sumcheck(f: &[Fp], challenges: &[Fp], p: u64) -> SumcheckProof {
    let m = cube_dim(f);
    assert_eq!(
        challenges.len(),
        m,
        "need one challenge per round (m = {m})"
    );
    assert!(
        challenges.iter().all(|&r| r < p),
        "challenges must be canonical mod p"
    );
    let claim = f.iter().fold(0, |acc, &v| add_mod(acc, v % p, p));
    let rounds = (0..m).map(|i| round_poly(f, challenges, i, p)).collect();
    SumcheckProof {
        claim,
        rounds,
        challenges: challenges.to_vec(),
    }
}

/// The sumcheck verifier, mirroring Selvage's `SumcheckAccepts`
/// (`Selvage/SumcheckReduction.lean`), conjunct for conjunct: every round's
/// boolean check `gᵢ(0)+gᵢ(1) = running` against the folded claim chain
/// (`scChain`, `Selvage/Sumcheck.lean`), then the terminal oracle check
/// `running = f̂(r)` with `f̂` supplied as an oracle (in the deployed protocol,
/// an opening of the committed table; here, typically
/// `|pt| mle_eval(f, pt, p)`). The degree bound `d = 1` is enforced by the
/// message REPRESENTATION — two evaluations define exactly the affine
/// interpolant, Lean's `roundPoly`.
///
/// Every check REJECTS on failure — fail-closed. A verifier that folds without
/// checking accepts every transcript (the fail-open seam the p3-sumcheck
/// reconnaissance measured); this shape is the refusal of that seam.
/// Conservative reject on any shape or canonicity violation. Runs; does not
/// verify in the formal sense — no Rust semantics.
pub fn verify_sumcheck(proof: &SumcheckProof, f_oracle: impl Fn(&[Fp]) -> Fp, p: u64) -> bool {
    if proof.rounds.len() != proof.challenges.len() {
        return false;
    }
    if proof.claim >= p || proof.challenges.iter().any(|&r| r >= p) {
        return false;
    }
    let mut running = proof.claim;
    for (g, &r) in proof.rounds.iter().zip(proof.challenges.iter()) {
        if g.len() != 2 || g.iter().any(|&v| v >= p) {
            return false;
        }
        // The boolean check: gᵢ(0) + gᵢ(1) = scChain value (claim, then folds).
        if add_mod(g[0], g[1], p) != running {
            return false;
        }
        // The fold: next chain value is gᵢ(rᵢ).
        running = eval_affine(g, r, p);
    }
    // The terminal oracle check: the folded claim equals f̂ at the challenge
    // point (`scChain_mleHonest_final`'s target).
    running == f_oracle(&proof.challenges)
}

// ===========================================================================
// The degree-3 rung. Mirrors `Assurance/AirSumcheckCubic.lean`.
// ===========================================================================

/// `a^e mod p` by square-and-multiply — the engine had only add/sub/mul.
pub fn pow_mod(a: Fp, e: u64, p: u64) -> Fp {
    let mut base = a % p;
    let mut exp = e;
    let mut acc = 1 % p;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mul_mod(acc, base, p);
        }
        base = mul_mod(base, base, p);
        exp >>= 1;
    }
    acc
}

/// The modular inverse `a⁻¹ mod p` for PRIME `p`, by Fermat (`a^{p−2}`).
/// `None` for `a ≡ 0`, so a caller cannot silently consume a wrong value —
/// every caller here turns `None` into a REJECT.
///
/// Correctness rests on `p` being prime; `prove_*`/`verify_*` are documented
/// prime-only and the conformance vector instantiates `p = babybear::P`.
pub fn inv_mod(a: Fp, p: u64) -> Option<Fp> {
    if a % p == 0 {
        None
    } else {
        Some(pow_mod(a, p - 2, p))
    }
}

/// The Lagrange denominators for the node set `{0, …, d}`:
/// `Dⱼ = ∏_{k ≠ j} (j − k) = (−1)^{d−j}·j!·(d−j)!`. Precomputed as constants
/// (index by `d`, then by `j`) — degrees 1 through 3, which is every degree this
/// engine sends.
const LAGRANGE_DENOMS: [&[i64]; 4] = [&[1], &[-1, 1], &[2, -1, 2], &[-6, 2, -2, 6]];

/// Reduce a (possibly negative) integer denominator into `[0, p)`.
fn denom_mod(d: i64, p: u64) -> Fp {
    let m = d.unsigned_abs() % p;
    if d < 0 { sub_mod(0, m, p) } else { m }
}

/// Evaluate the degree-`d` interpolant of `evals` (given at the nodes
/// `0, 1, …, d`) at `t`, in the Lagrange basis with the denominators above.
///
/// `None` — and therefore a verifier REJECT — when the modulus cannot support
/// the node set: `p ≤ d` makes the nodes collide, and `p ∈ {2,3}` makes a
/// denominator non-invertible. Never returns a value it could not justify.
pub fn eval_lagrange(evals: &[Fp], t: Fp, p: u64) -> Option<Fp> {
    let d = evals.len().checked_sub(1)?;
    if d >= LAGRANGE_DENOMS.len() || (p as u128) <= d as u128 {
        return None;
    }
    let denoms = LAGRANGE_DENOMS[d];
    let t = t % p;
    let mut acc = 0;
    for (j, &y) in evals.iter().enumerate() {
        // ∏_{k ≠ j} (t − k)
        let mut num = 1 % p;
        for k in 0..=d {
            if k != j {
                num = mul_mod(num, sub_mod(t, (k as u64) % p, p), p);
            }
        }
        let inv = inv_mod(denom_mod(denoms[j], p), p)?;
        acc = add_mod(acc, mul_mod(mul_mod(y % p, num, p), inv, p), p);
    }
    Some(acc)
}

/// Bind the LSB coordinate of a value table at `r`: the pair `(f[2k], f[2k+1])`
/// becomes `f[2k] + r·(f[2k+1] − f[2k])`. The p-generic twin of
/// `mle_kernels::fold_mle_table`, whose `NativeMleScalar` trait carries no
/// runtime modulus and so cannot serve this engine (see the module docs).
pub fn fold_table(f: &[Fp], r: Fp, p: u64) -> Vec<Fp> {
    assert!(f.len() >= 2 && f.len().is_power_of_two(), "foldable table");
    f.chunks_exact(2)
        .map(|pair| {
            add_mod(
                pair[0] % p,
                mul_mod(r % p, sub_mod(pair[1], pair[0], p), p),
                p,
            )
        })
        .collect()
}

/// The five tables of a cubic claim `Σ_b E(b)·(A(b)·B(b) + C(b)·D(b))`, in the
/// order the Lean `cubicForm E A B C D` takes them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CubicTables {
    pub e: Vec<Fp>,
    pub a: Vec<Fp>,
    pub b: Vec<Fp>,
    pub c: Vec<Fp>,
    pub d: Vec<Fp>,
}

impl CubicTables {
    /// All five tables must be `2^m` long for one common `m`.
    pub fn dim(&self) -> usize {
        let m = cube_dim(&self.e);
        for t in [&self.a, &self.b, &self.c, &self.d] {
            assert_eq!(cube_dim(t), m, "all five tables share one dimension");
        }
        m
    }

    /// The claimed total `Σ_b E(b)·(A(b)·B(b) + C(b)·D(b))`.
    pub fn claim(&self, p: u64) -> Fp {
        let n = self.e.len();
        (0..n).fold(0, |acc, k| {
            let inner = add_mod(
                mul_mod(self.a[k] % p, self.b[k] % p, p),
                mul_mod(self.c[k] % p, self.d[k] % p, p),
                p,
            );
            add_mod(acc, mul_mod(self.e[k] % p, inner, p), p)
        })
    }

    /// The FACTORED terminal openings `[Ê(x), Â(x), B̂(x), Ĉ(x), D̂(x)]` — five
    /// values the verifier combines itself, mirroring `scChain_cubicHonest_final`.
    pub fn openings(&self, point: &[Fp], p: u64) -> [Fp; 5] {
        [
            mle_eval(&self.e, point, p),
            mle_eval(&self.a, point, p),
            mle_eval(&self.b, point, p),
            mle_eval(&self.c, point, p),
            mle_eval(&self.d, point, p),
        ]
    }

    fn fold(&self, r: Fp, p: u64) -> CubicTables {
        CubicTables {
            e: fold_table(&self.e, r, p),
            a: fold_table(&self.a, r, p),
            b: fold_table(&self.b, r, p),
            c: fold_table(&self.c, r, p),
            d: fold_table(&self.d, r, p),
        }
    }
}

/// Combine five openings into the cubic value — the verifier's own arithmetic,
/// `Ê·(Â·B̂ + Ĉ·D̂)`.
pub fn cubic_combine(o: &[Fp; 5], p: u64) -> Fp {
    let inner = add_mod(mul_mod(o[1], o[2], p), mul_mod(o[3], o[4], p), p);
    mul_mod(o[0], inner, p)
}

/// The LITERAL mirror of the Lean `roundSum (cubicForm E A B C D) r i t` — the
/// summand evaluated through `mle_eval` at every suffix corner. O(4^m); this is
/// the shape the conformance vector binds and the oracle the folded prover is
/// checked against.
pub fn cubic_round_sum_literal(tabs: &CubicTables, r: &[Fp], i: usize, t: Fp, p: u64) -> Fp {
    let m = tabs.dim();
    assert_eq!(r.len(), m, "challenge vector length {} != {m}", r.len());
    assert!(i < m, "round index {i} out of range (m = {m})");
    let suffix = m - i - 1;
    let mut point: Vec<Fp> = Vec::with_capacity(m);
    let mut acc = 0;
    for b in 0..1usize << suffix {
        point.clear();
        point.extend_from_slice(&r[..i]);
        point.push(t % p);
        for j in 0..suffix {
            point.push(((b >> j) & 1) as u64);
        }
        acc = add_mod(acc, cubic_combine(&tabs.openings(&point, p), p), p);
    }
    acc
}

/// Round `i`'s message from ALREADY-FOLDED tables: the four evaluations
/// `[h(0), h(1), h(2), h(3)]`. Each remaining pair contributes its line values
/// at the four nodes; O(len) per round, so O(2^m) over the whole protocol.
///
/// `h(1)` is computed here and SENT — it is never derived by the verifier.
pub fn cubic_round_evals(tabs: &CubicTables, p: u64) -> [Fp; 4] {
    let half = tabs.e.len() / 2;
    let mut out = [0u64; 4];
    for k in 0..half {
        let line = |tab: &[Fp], t: u64| -> Fp {
            let lo = tab[2 * k] % p;
            let hi = tab[2 * k + 1] % p;
            add_mod(lo, mul_mod(t % p, sub_mod(hi, lo, p), p), p)
        };
        for (idx, out_slot) in out.iter_mut().enumerate() {
            let t = idx as u64;
            let inner = add_mod(
                mul_mod(line(&tabs.a, t), line(&tabs.b, t), p),
                mul_mod(line(&tabs.c, t), line(&tabs.d, t), p),
                p,
            );
            *out_slot = add_mod(*out_slot, mul_mod(line(&tabs.e, t), inner, p), p);
        }
    }
    out
}

/// A degree-3 sumcheck transcript.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CubicSumcheckProof {
    /// The claimed total (honest prover: `CubicTables::claim`).
    pub claim: Fp,
    /// Per round, `[hᵢ(0), hᵢ(1), hᵢ(2), hᵢ(3)]` — FOUR evals, `h(1)` included.
    pub rounds: Vec<[Fp; 4]>,
    /// The challenges folded in after each round. Fiat-Shamir is `[PROVER-fs]`.
    pub challenges: Vec<Fp>,
}

/// The honest degree-3 prover, folded: five tables shrink by half each round, so
/// the whole run is O(2^m) rather than the literal mirror's O(4^m).
pub fn prove_cubic_sumcheck(tabs: &CubicTables, challenges: &[Fp], p: u64) -> CubicSumcheckProof {
    let m = tabs.dim();
    assert_eq!(challenges.len(), m, "need one challenge per round (m = {m})");
    assert!(
        challenges.iter().all(|&r| r < p),
        "challenges must be canonical mod p"
    );
    let claim = tabs.claim(p);
    let mut state = tabs.clone();
    let mut rounds = Vec::with_capacity(m);
    for &r in challenges.iter() {
        rounds.push(cubic_round_evals(&state, p));
        state = state.fold(r, p);
    }
    CubicSumcheckProof {
        claim,
        rounds,
        challenges: challenges.to_vec(),
    }
}

/// The degree-3 verifier, fail-closed, mirroring Selvage's `SumcheckAccepts`
/// conjunct for conjunct at `d = 3`.
///
/// Every round check reads the PROVER'S `h(1)`; nothing is reconstructed from
/// the running claim, so `h(0) + h(1) = running` is a real constraint. The
/// terminal check takes the five openings and combines them itself
/// (`scChain_cubicHonest_final`'s factored target). Any shape violation,
/// non-canonical value, or non-invertible interpolation REJECTS.
///
/// Runs; does not verify in the formal sense — there is no semantics of Rust.
pub fn verify_cubic_sumcheck(
    proof: &CubicSumcheckProof,
    openings: impl Fn(&[Fp]) -> [Fp; 5],
    p: u64,
) -> bool {
    if proof.rounds.len() != proof.challenges.len() {
        return false;
    }
    if proof.claim >= p || proof.challenges.iter().any(|&r| r >= p) {
        return false;
    }
    let mut running = proof.claim;
    for (h, &r) in proof.rounds.iter().zip(proof.challenges.iter()) {
        if h.iter().any(|&v| v >= p) {
            return false;
        }
        // The boolean check against the prover-supplied h(1) — NOT a tautology.
        if add_mod(h[0], h[1], p) != running {
            return false;
        }
        match eval_lagrange(h, r, p) {
            Some(v) => running = v,
            None => return false,
        }
    }
    let o = openings(&proof.challenges);
    if o.iter().any(|&v| v >= p) {
        return false;
    }
    running == cubic_combine(&o, p)
}

// ─── The zkML matmul CONTRACTION, driven over the cubic engine ──────────────
//
// `Assurance/ZkmlMatmulSumcheck.lean` is the Lean side and the only authority on
// what these objects mean:
//
//   `mle₂_contraction`   Ĉ(x,y) = Σ_p Â(x,p)·B̂(p,y)  at EVERY (x,y)
//   `cubicForm_contraction`  the instance: head E ≡ 1, pair (g,h), C ≡ 0, D ≡ 1
//   `matmul_sumcheck_soundness`  ≤ (μ+ν)/|F| + κ·3/|F|
//
// Two things this code is NOT:
//
// * It is **not** the Hadamard face. `cubicForm_hadamard` (renamed — it was called
//   `cubicForm_matmul`) is `eq·(Â·B̂ − Ĉ)`, a POINTWISE product; a contraction sums
//   an inner index that appears in neither output coordinate.
// * It is **not** a complete argument. `[MATMUL-pcs]`: a succinct verifier needs
//   THREE root-bound MLE claims: `Ĉ(x,y)`, `Â(x,r)`, and `B̂(r,y)`. The Lean claim
//   seam exists as `MleEvalClaim`; its BaseFold RBR/BCS proof transcript does not.
//   `verify_matmul` hides the first claim by receiving the complete output table
//   and takes the latter two values from a closure. All three proofs are unpriced.

/// A matmul claim on cubes: `A` is `2^mu × 2^kappa`, `B` is `2^kappa × 2^nu`, both
/// row-major with LSB-first cube indices (index bit `i` = cube coordinate `i`, the
/// convention `bitsToIdx` pins on the Lean side).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatmulClaim {
    pub mu: usize,
    pub kappa: usize,
    pub nu: usize,
    /// `a[row][inner]`
    pub a: Vec<Vec<Fp>>,
    /// `b[inner][col]`
    pub b: Vec<Vec<Fp>>,
}

impl MatmulClaim {
    fn check_shape(&self) {
        assert_eq!(self.a.len(), 1 << self.mu, "A has 2^mu rows");
        assert!(
            self.a.iter().all(|r| r.len() == 1 << self.kappa),
            "every A row has 2^kappa entries"
        );
        assert_eq!(self.b.len(), 1 << self.kappa, "B has 2^kappa rows");
        assert!(
            self.b.iter().all(|r| r.len() == 1 << self.nu),
            "every B row has 2^nu entries"
        );
    }

    /// The TRUE output table `C = A·B` — the Lean `matmulTable`. This is the
    /// `m·k·n` work the prover must do anyway to know its own answer; the argument
    /// below is what replaces proving it gate by gate.
    pub fn output(&self, p: u64) -> Vec<Vec<Fp>> {
        self.check_shape();
        (0..1 << self.mu)
            .map(|i| {
                (0..1 << self.nu)
                    .map(|j| {
                        (0..1 << self.kappa).fold(0, |acc, q| {
                            add_mod(acc, mul_mod(self.a[i][q] % p, self.b[q][j] % p, p), p)
                        })
                    })
                    .collect()
            })
            .collect()
    }

    /// `Â(x, ·)` on the inner cube — the Lean `rowPartial`.
    pub fn row_partial(&self, x: &[Fp], p: u64) -> Vec<Fp> {
        self.check_shape();
        assert_eq!(x.len(), self.mu, "outer row point has mu coordinates");
        (0..1 << self.kappa)
            .map(|q| {
                (0..1 << self.mu).fold(0, |acc, i| {
                    add_mod(acc, mul_mod(self.a[i][q] % p, chi_eval(i, x, p), p), p)
                })
            })
            .collect()
    }

    /// `B̂(·, y)` on the inner cube — the Lean `colPartial`.
    pub fn col_partial(&self, y: &[Fp], p: u64) -> Vec<Fp> {
        self.check_shape();
        assert_eq!(y.len(), self.nu, "outer column point has nu coordinates");
        (0..1 << self.kappa)
            .map(|q| {
                (0..1 << self.nu).fold(0, |acc, j| {
                    add_mod(acc, mul_mod(self.b[q][j] % p, chi_eval(j, y, p), p), p)
                })
            })
            .collect()
    }

    /// The five cubic tables at the bound outer point: `E ≡ 1`, the product pair,
    /// `C ≡ 0`, `D ≡ 1`. The head is CONSTANT — there is no `eq` factor, because the
    /// outer indices were bound before the sumcheck started.
    pub fn tables(&self, x: &[Fp], y: &[Fp], p: u64) -> CubicTables {
        let n = 1usize << self.kappa;
        CubicTables {
            e: vec![1 % p; n],
            a: self.row_partial(x, p),
            b: self.col_partial(y, p),
            c: vec![0; n],
            d: vec![1 % p; n],
        }
    }
}

/// The two-block multilinear extension of a `2^mu × 2^nu` table — the Lean `mle₂`.
/// This is how the VERIFIER computes its target from the claimed output table; it
/// never takes the prover's word for the total.
pub fn mle2_eval(table: &[Vec<Fp>], x: &[Fp], y: &[Fp], p: u64) -> Fp {
    let rows = table.len();
    assert!(rows == 1 << x.len(), "table rows must be 2^|x|");
    let mut acc = 0;
    for (i, row) in table.iter().enumerate() {
        assert!(row.len() == 1 << y.len(), "table cols must be 2^|y|");
        let cx = chi_eval(i, x, p);
        for (j, &v) in row.iter().enumerate() {
            acc = add_mod(acc, mul_mod(mul_mod(v % p, cx, p), chi_eval(j, y, p), p), p);
        }
    }
    acc
}

/// The honest contraction prover: fold the two operands at the outer point, then
/// run the folded cubic prover on the inner cube. Work is
/// `O(2^(mu+kappa) + 2^(kappa+nu))` for the folding and `O(2^kappa)` for the rounds
/// — the `m·k·n` contraction itself is NOT re-done here.
pub fn prove_matmul(
    claim: &MatmulClaim,
    x: &[Fp],
    y: &[Fp],
    challenges: &[Fp],
    p: u64,
) -> CubicSumcheckProof {
    prove_cubic_sumcheck(&claim.tables(x, y, p), challenges, p)
}

/// The contraction verifier, fail-closed.
///
/// 1. The target is recomputed from the CLAIMED output table (`mle2_eval`), never
///    read from the proof: a prover that sends a total the claimed table does not
///    have is rejected before any round is examined. Receiving that whole table is
///    a native-test convenience; a succinct verifier instead checks the root-bound
///    claim `Ĉ(x,y)`.
/// 2. The rounds are the landed degree-3 verifier, `h(1)` read from the wire.
/// 3. The terminal check combines FIVE openings, of which three are the constants
///    `1, 0, 1` the verifier supplies itself. Only two are terminal oracle values,
///    and `open_gh` stands for their missing BaseFold RBR/BCS proofs. Together with
///    the output claim above, the complete argument needs three MLE proofs.
///
/// Runs; does not verify in the formal sense — there is no semantics of Rust.
pub fn verify_matmul(
    claimed_output: &[Vec<Fp>],
    x: &[Fp],
    y: &[Fp],
    proof: &CubicSumcheckProof,
    open_gh: impl Fn(&[Fp]) -> (Fp, Fp),
    p: u64,
) -> bool {
    let target = mle2_eval(claimed_output, x, y, p);
    if proof.claim != target {
        return false;
    }
    verify_cubic_sumcheck(
        proof,
        |r| {
            let (g, h) = open_gh(r);
            [1 % p, g, h, 0, 1 % p]
        },
        p,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::babybear::{badd, bmul, bsub, P};

    /// `Selvage/MultilinearExtension.lean`'s `MLEExample` over F₅: the AND table
    /// `[0,0,0,1]` (bit i = coordinate i; AND is 1 only at index 3 = corner
    /// (1,1)). The asserted values are KERNEL-DECIDED in the Lean file
    /// (`mle_and_agrees`, `mle_and_offcube`, `roundSum_and_chain0/1/final`);
    /// reproducing them here is a cross-check on vectors, not a proof.
    const F_AND: [Fp; 4] = [0, 0, 0, 1];
    const P5: u64 = 5;

    #[test]
    fn mle_agrees_on_corners_and_gate() {
        // mle_and_agrees: f̂ interpolates the table at all four corners.
        for b in 0..4usize {
            let corner = vec![(b & 1) as u64, ((b >> 1) & 1) as u64];
            assert_eq!(mle_eval(&F_AND, &corner, P5), F_AND[b], "corner {b}");
        }
    }

    #[test]
    fn mle_and_offcube_matches_lean_decided_value() {
        // mle_and_offcube: f̂_AND(2,3) = 2·3 = 1 in F₅ — a genuine extension.
        assert_eq!(mle_eval(&F_AND, &[2, 3], P5), 1);
    }

    #[test]
    fn round_chain_matches_lean_decided_examples() {
        // roundSum_and_chain0: g₀(0) + g₀(1) = Σ_b fAnd(b) = 1 (r = [2,0]).
        let r = [2, 0];
        let g0 = round_poly(&F_AND, &r, 0, P5);
        assert_eq!(add_mod(g0[0], g0[1], P5), 1);
        // roundSum_and_chain1: g₁(0) + g₁(1) = g₀(2).
        let g1 = round_poly(&F_AND, &r, 1, P5);
        assert_eq!(add_mod(g1[0], g1[1], P5), round_sum(&F_AND, &r, 0, 2, P5));
        // roundSum_and_final: g₁(3) = f̂_AND(2,3) at r = [2,3].
        let r = [2, 3];
        assert_eq!(round_sum(&F_AND, &r, 1, 3, P5), mle_eval(&F_AND, &r, P5));
    }

    /// An asymmetric m = 3 table over F₉₇ — bit-order-sensitive, unlike AND.
    const F97: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
    const P97: u64 = 97;

    #[test]
    fn mle_agrees_on_corners_m3() {
        for b in 0..8usize {
            let corner: Vec<Fp> = (0..3).map(|i| ((b >> i) & 1) as u64).collect();
            assert_eq!(mle_eval(&F97, &corner, P97), F97[b], "corner {b}");
        }
    }

    #[test]
    fn round_sum_is_affine_in_t() {
        // roundSum_affine, exercised: gᵢ(t) = (1−t)·gᵢ(0) + t·gᵢ(1) off {0,1}.
        let r = [17, 42, 63];
        for i in 0..3 {
            let g = round_poly(&F97, &r, i, P97);
            for t in [2, 5, 96] {
                assert_eq!(
                    round_sum(&F97, &r, i, t, P97),
                    eval_affine(&g, t, P97),
                    "round {i} t {t}"
                );
            }
        }
    }

    #[test]
    fn round_sum_ignores_challenges_at_and_above_i() {
        // roundSum_congr_prefix, exercised: round i reads r only below i.
        let r1 = [17, 42, 63];
        let r2 = [17, 42, 11];
        assert_eq!(
            round_sum(&F97, &r1, 2, 7, P97),
            round_sum(&F97, &r2, 2, 7, P97)
        );
        let r3 = [17, 5, 90];
        assert_eq!(
            round_sum(&F97, &r1, 1, 7, P97),
            round_sum(&F97, &r3, 1, 7, P97)
        );
    }

    #[test]
    fn prove_verify_round_trip() {
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        assert_eq!(proof.claim, F97.iter().sum::<u64>() % P97);
        assert!(verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }

    #[test]
    fn chain_identities_hold_on_honest_transcript() {
        // The Lean-proved chain, exercised on the honest transcript:
        // roundSum_zero, roundSum_succ, roundSum_last.
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        assert_eq!(
            add_mod(proof.rounds[0][0], proof.rounds[0][1], P97),
            proof.claim
        );
        for k in 0..2 {
            assert_eq!(
                add_mod(proof.rounds[k + 1][0], proof.rounds[k + 1][1], P97),
                eval_affine(&proof.rounds[k], chal[k], P97),
                "g_{}(0)+g_{}(1) = g_{}(r_{})",
                k + 1,
                k + 1,
                k,
                k
            );
        }
        assert_eq!(
            eval_affine(&proof.rounds[2], chal[2], P97),
            mle_eval(&F97, &chal, P97)
        );
    }

    #[test]
    fn zero_rounds_table() {
        // m = 0: the table is one value, the claim is that value, no rounds —
        // the Lean `scChain_mleHonest_final` m = 0 case (`claim = f̂(r)`).
        let proof = prove_sumcheck(&[42], &[], P97);
        assert_eq!(proof.claim, 42);
        assert!(proof.rounds.is_empty());
        assert!(verify_sumcheck(&proof, |pt| mle_eval(&[42], pt, P97), P97));
    }

    #[test]
    fn tampered_round_poly_fails() {
        let chal = [17, 42, 63];
        for i in 0..3 {
            for j in 0..2 {
                let mut proof = prove_sumcheck(&F97, &chal, P97);
                proof.rounds[i][j] = (proof.rounds[i][j] + 1) % P97;
                assert!(
                    !verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97),
                    "tampered g_{i}({j}) must fail"
                );
            }
        }
    }

    #[test]
    fn false_claim_fails() {
        // The direct refusal of the fail-open seam: a wrong total is caught at
        // round 0's boolean check, not laundered by folding.
        let chal = [17, 42, 63];
        let mut proof = prove_sumcheck(&F97, &chal, P97);
        proof.claim = (proof.claim + 1) % P97;
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }

    #[test]
    fn wrong_oracle_fails() {
        // The transcript is internally consistent but the final oracle check
        // targets a DIFFERENT table's MLE — the terminal comparison has teeth.
        let chal = [17, 42, 63];
        let proof = prove_sumcheck(&F97, &chal, P97);
        let other: [Fp; 8] = [3, 1, 4, 1, 5, 9, 2, 7];
        assert!(!verify_sumcheck(
            &proof,
            |pt| mle_eval(&other, pt, P97),
            P97
        ));
    }

    #[test]
    fn malformed_proof_shapes_rejected() {
        let chal = [17, 42, 63];
        let good = prove_sumcheck(&F97, &chal, P97);
        // Round/challenge count mismatch.
        let mut proof = good.clone();
        proof.rounds.pop();
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
        // A round message that is not 2 evals.
        let mut proof = good.clone();
        proof.rounds[1] = vec![1, 2, 3];
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
        // Non-canonical value.
        let mut proof = good;
        proof.rounds[0][0] += P97;
        assert!(!verify_sumcheck(&proof, |pt| mle_eval(&F97, pt, P97), P97));
    }

    #[test]
    fn engine_arithmetic_agrees_with_babybear_kernels() {
        // The engine's p-generic mod arithmetic and the crate's fixed-P
        // BabyBear kernels are two computations of the same field ops; the
        // conformance vector rides on this agreement, so pin it directly.
        let mut seed = 0x00b1_ec7e_u64;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 16) % P
        };
        for _ in 0..1_000 {
            let a = next();
            let b = next();
            assert_eq!(add_mod(a, b, P), badd(a, b));
            assert_eq!(sub_mod(a, b, P), bsub(a, b));
            assert_eq!(mul_mod(a, b, P), bmul(a, b));
        }
    }

    // ---------------- the degree-3 rung ----------------

    /// A deterministic m-variable instance over F₉₇, asymmetric in every table.
    fn cubic_instance(m: usize) -> CubicTables {
        let n = 1usize << m;
        let gen = |seed: u64| -> Vec<Fp> {
            let mut s = seed;
            (0..n)
                .map(|_| {
                    s = s
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    (s >> 33) % P97
                })
                .collect()
        };
        CubicTables {
            e: gen(1),
            a: gen(2),
            b: gen(3),
            c: gen(4),
            d: gen(5),
        }
    }

    #[test]
    fn inv_mod_is_a_two_sided_inverse() {
        for a in 1..P97 {
            let inv = inv_mod(a, P97).expect("nonzero is invertible");
            assert_eq!(mul_mod(a, inv, P97), 1, "a = {a}");
        }
        assert_eq!(inv_mod(0, P97), None);
        // BabyBear too, since the conformance vector rides on it.
        for a in [1, 2, 3, 6, 42, P - 1] {
            let inv = inv_mod(a, P).expect("nonzero is invertible");
            assert_eq!(mul_mod(a, inv, P), 1, "a = {a}");
        }
    }

    #[test]
    fn eval_lagrange_reproduces_its_own_nodes() {
        // The interpolant through 4 points agrees with them at 0,1,2,3.
        let evals = [11, 5, 90, 33];
        for (t, &y) in evals.iter().enumerate() {
            assert_eq!(eval_lagrange(&evals, t as u64, P97), Some(y), "node {t}");
        }
    }

    #[test]
    fn eval_lagrange_matches_a_known_cubic() {
        // h(X) = 2X³ + 3X² + 5X + 7 over F₉₇, sampled at 0..3 and re-evaluated.
        let h = |x: u64| -> u64 {
            let x = x % P97;
            let x2 = mul_mod(x, x, P97);
            let x3 = mul_mod(x2, x, P97);
            add_mod(
                add_mod(mul_mod(2, x3, P97), mul_mod(3, x2, P97), P97),
                add_mod(mul_mod(5, x, P97), 7, P97),
                P97,
            )
        };
        let evals = [h(0), h(1), h(2), h(3)];
        for t in [4, 17, 50, 96] {
            assert_eq!(eval_lagrange(&evals, t, P97), Some(h(t)), "t = {t}");
        }
    }

    #[test]
    fn eval_lagrange_refuses_moduli_it_cannot_serve() {
        // The {0,1,2,3} node set needs p > 3 and 6 invertible. A refusal must be
        // a refusal, not a wrong value silently folded (`None`, never `Some`).
        assert_eq!(eval_lagrange(&[1, 1, 1, 1], 0, 2), None);
        assert_eq!(eval_lagrange(&[1, 1, 1, 1], 0, 3), None);
        // Degree 5 has no precomputed denominators — refuse rather than guess.
        assert_eq!(eval_lagrange(&[1, 2, 3, 4, 5, 6], 0, P97), None);
    }

    #[test]
    fn fold_table_agrees_with_the_mle_kernel_recurrence() {
        // The p-generic fold is the same recurrence as the crate's typed
        // `mle_kernels::fold_mle_table`: lo + r·(hi − lo) on LSB-adjacent pairs.
        let f: Vec<Fp> = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let r = 42;
        let got = fold_table(&f, r, P97);
        let want: Vec<Fp> = (0..4)
            .map(|k| {
                add_mod(f[2 * k], mul_mod(r, sub_mod(f[2 * k + 1], f[2 * k], P97), P97), P97)
            })
            .collect();
        assert_eq!(got, want);
        // Folding every coordinate is an MLE evaluation.
        let point = [42, 17, 63];
        let mut layer = f.clone();
        for &r in point.iter() {
            layer = fold_table(&layer, r, P97);
        }
        assert_eq!(layer, vec![mle_eval(&f, &point, P97)]);
    }

    #[test]
    fn folded_prover_agrees_with_literal_mirror() {
        // THE BINDING THAT SURVIVES THE OPTIMIZATION: the O(2^m) folded prover
        // and the O(4^m) literal mirror of the Lean `roundSum (cubicForm …)`
        // produce the same four evals in every round. Without this the speedup
        // would have replaced the Lean-mirroring path instead of accelerating it.
        for m in 1..=5usize {
            let tabs = cubic_instance(m);
            let chal: Vec<Fp> = (0..m).map(|i| (7 * i as u64 + 13) % P97).collect();
            let mut state = tabs.clone();
            for i in 0..m {
                let folded = cubic_round_evals(&state, P97);
                for (t, &got) in folded.iter().enumerate() {
                    assert_eq!(
                        got,
                        cubic_round_sum_literal(&tabs, &chal, i, t as u64, P97),
                        "m {m} round {i} t {t}"
                    );
                }
                state = state.fold(chal[i], P97);
            }
        }
    }

    #[test]
    fn cubic_round_sum_is_cubic_in_t() {
        // The Lean `cubicRoundPoly_eval`, exercised: the four evals interpolate
        // the round partial sum at points OFF the node set {0,1,2,3}.
        let m = 4;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63, 5];
        let mut state = tabs.clone();
        for i in 0..m {
            let h = cubic_round_evals(&state, P97);
            for t in [4, 11, 60, 96] {
                assert_eq!(
                    eval_lagrange(&h, t, P97),
                    Some(cubic_round_sum_literal(&tabs, &chal, i, t, P97)),
                    "round {i} t {t}"
                );
            }
            state = state.fold(chal[i], P97);
        }
    }

    #[test]
    fn cubic_chain_identities_hold_on_the_honest_transcript() {
        let m = 4;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63, 5];
        let proof = prove_cubic_sumcheck(&tabs, &chal, P97);
        // roundSum_zero + cubicForm_cube_sum: h₀(0) + h₀(1) = the claim.
        assert_eq!(
            add_mod(proof.rounds[0][0], proof.rounds[0][1], P97),
            proof.claim
        );
        // roundSum_succ: h_{k+1}(0) + h_{k+1}(1) = h_k(r_k).
        for k in 0..m - 1 {
            assert_eq!(
                add_mod(proof.rounds[k + 1][0], proof.rounds[k + 1][1], P97),
                eval_lagrange(&proof.rounds[k], chal[k], P97).unwrap(),
                "chain link {k}"
            );
        }
        // scChain_cubicHonest_final: the terminal value is the FACTORED combine.
        assert_eq!(
            eval_lagrange(&proof.rounds[m - 1], chal[m - 1], P97).unwrap(),
            cubic_combine(&tabs.openings(&chal, P97), P97)
        );
    }

    #[test]
    fn cubic_prove_verify_round_trip() {
        for m in 1..=6usize {
            let tabs = cubic_instance(m);
            let chal: Vec<Fp> = (0..m).map(|i| (11 * i as u64 + 3) % P97).collect();
            let proof = prove_cubic_sumcheck(&tabs, &chal, P97);
            assert!(
                verify_cubic_sumcheck(&proof, |pt| tabs.openings(pt, P97), P97),
                "m = {m}"
            );
        }
    }

    #[test]
    fn cubic_tampered_round_message_fails() {
        let m = 3;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63];
        for i in 0..m {
            for j in 0..4 {
                let mut proof = prove_cubic_sumcheck(&tabs, &chal, P97);
                let before = proof.rounds[i][j];
                proof.rounds[i][j] = (before + 1) % P97;
                // The mutation must actually be a mutation.
                assert_ne!(proof.rounds[i][j], before, "round {i} eval {j} unmutated");
                assert!(
                    !verify_cubic_sumcheck(&proof, |pt| tabs.openings(pt, P97), P97),
                    "tampered h_{i}({j}) must fail"
                );
            }
        }
    }

    #[test]
    fn cubic_false_claim_and_wrong_oracle_fail() {
        let m = 3;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63];
        let good = prove_cubic_sumcheck(&tabs, &chal, P97);

        let mut bad = good.clone();
        bad.claim = (bad.claim + 1) % P97;
        assert!(!verify_cubic_sumcheck(&bad, |pt| tabs.openings(pt, P97), P97));

        // The terminal check has teeth: a different D table is a different claim.
        let mut other = tabs.clone();
        other.d[0] = (other.d[0] + 1) % P97;
        assert_ne!(other.d, tabs.d, "the oracle swap must be a real swap");
        assert!(!verify_cubic_sumcheck(
            &good,
            |pt| other.openings(pt, P97),
            P97
        ));
    }

    #[test]
    fn no_message_passes_both_checks() {
        // THE p3 PITFALL, REFUSED. Against a FALSE claim a prover has exactly two
        // options for h₀(1), and this engine rejects both:
        //   * the honest h₀(1) fails the ROUND check (h(0)+h(1) is the TRUE sum);
        //   * the derived h₀(1) = claim − h(0) passes the round check by
        //     construction — which is what p3 hands the verifier for free — and
        //     then fails the TERMINAL check.
        // A verifier that DERIVES h(1) has only the second branch and has made
        // its round check a tautology.
        let m = 3;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63];
        let honest = prove_cubic_sumcheck(&tabs, &chal, P97);
        let false_claim = (honest.claim + 1) % P97;

        // Branch 1: honest messages, false claim.
        let mut p1 = honest.clone();
        p1.claim = false_claim;
        assert_ne!(
            add_mod(p1.rounds[0][0], p1.rounds[0][1], P97),
            p1.claim,
            "the honest round-0 check must genuinely disagree with the false claim"
        );
        assert!(!verify_cubic_sumcheck(&p1, |pt| tabs.openings(pt, P97), P97));

        // Branch 2: the p3-style DERIVED h(1), which makes the round check pass.
        let mut p2 = honest.clone();
        p2.claim = false_claim;
        let derived = sub_mod(false_claim, p2.rounds[0][0], P97);
        assert_ne!(
            derived, honest.rounds[0][1],
            "the derived h(1) must differ from the honest one, or this test is a no-op"
        );
        p2.rounds[0][1] = derived;
        assert_eq!(
            add_mod(p2.rounds[0][0], p2.rounds[0][1], P97),
            p2.claim,
            "the derived message DOES pass the round check — that is the pitfall"
        );
        assert!(
            !verify_cubic_sumcheck(&p2, |pt| tabs.openings(pt, P97), P97),
            "the terminal check must catch what the round check cannot"
        );
    }

    #[test]
    fn cubic_malformed_shapes_rejected() {
        let m = 3;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = vec![17, 42, 63];
        let good = prove_cubic_sumcheck(&tabs, &chal, P97);

        let mut proof = good.clone();
        proof.rounds.pop();
        assert!(!verify_cubic_sumcheck(
            &proof,
            |pt| tabs.openings(pt, P97),
            P97
        ));

        let mut proof = good.clone();
        proof.rounds[0][0] += P97; // non-canonical
        assert!(!verify_cubic_sumcheck(
            &proof,
            |pt| tabs.openings(pt, P97),
            P97
        ));

        let mut proof = good;
        proof.challenges[1] += P97;
        assert!(!verify_cubic_sumcheck(
            &proof,
            |pt| tabs.openings(pt, P97),
            P97
        ));
    }

    #[test]
    fn folding_lifts_the_dimension_ceiling() {
        // The literal mirror is O(4^m); the folded prover is O(2^m). At m = 16
        // the mirror would be ~4·10⁹ MLE evaluations — this runs instantly, which
        // is the whole point of wiring the fold.
        let m = 16;
        let tabs = cubic_instance(m);
        let chal: Vec<Fp> = (0..m).map(|i| (13 * i as u64 + 7) % P97).collect();
        let proof = prove_cubic_sumcheck(&tabs, &chal, P97);
        assert_eq!(proof.rounds.len(), m);
        assert!(verify_cubic_sumcheck(&proof, |pt| tabs.openings(pt, P97), P97));
    }

    #[test]
    fn cubic_matmul_and_fraction_layer_instantiations() {
        // The two consumers the Lean names as theorems, exercised numerically.
        let m = 3;
        let n = 1usize << m;
        let base = cubic_instance(m);

        // Hadamard (elementwise) zerocheck: eq·(Â·B̂ − Ĉ) is cubicForm with D ≡ 1 and
        // C negated (`cubicForm_hadamard` — NOT the matmul face; a contraction sums an
        // inner index, see `matmul_claim` below and `Assurance/ZkmlMatmulSumcheck.lean`).
        let matmul = CubicTables {
            e: base.e.clone(),
            a: base.a.clone(),
            b: base.b.clone(),
            c: base.c.iter().map(|&v| sub_mod(0, v, P97)).collect(),
            d: vec![1; n],
        };
        let point = [17, 42, 63];
        let o = matmul.openings(&point, P97);
        let direct = mul_mod(
            mle_eval(&base.e, &point, P97),
            sub_mod(
                mul_mod(
                    mle_eval(&base.a, &point, P97),
                    mle_eval(&base.b, &point, P97),
                    P97,
                ),
                mle_eval(&base.c, &point, P97),
                P97,
            ),
            P97,
        );
        assert_eq!(cubic_combine(&o, P97), direct, "cubicForm_hadamard");

        // GKR fraction-tree layer: the head table is the eq weights b ↦ χ_b(z)
        // (`cubicForm_fraction_layer`; `Selvage.eqMle_eq_mle` says its MLE is
        // eq(z, ·)).
        let z = [5, 11, 90];
        let eq_table: Vec<Fp> = (0..n).map(|b| chi_eval(b, &z, P97)).collect();
        let frac = CubicTables {
            e: eq_table,
            a: base.a.clone(),
            b: base.b.clone(),
            c: base.c.clone(),
            d: base.d.clone(),
        };
        // eqMle_fold: the eq-weighted hypercube sum is the MLE at z. Here the
        // claim of the fraction layer is the numerator word evaluated at z.
        let word: Vec<Fp> = (0..n)
            .map(|k| {
                add_mod(
                    mul_mod(base.a[k], base.b[k], P97),
                    mul_mod(base.c[k], base.d[k], P97),
                    P97,
                )
            })
            .collect();
        assert_eq!(frac.claim(P97), mle_eval(&word, &z, P97), "eqMle_fold");

        let chal: Vec<Fp> = vec![3, 71, 22];
        let proof = prove_cubic_sumcheck(&frac, &chal, P97);
        assert!(verify_cubic_sumcheck(&proof, |pt| frac.openings(pt, P97), P97));
    }

    // ── The zkML matmul contraction ────────────────────────────────────────

    /// A deterministic pseudo-random matmul instance over BabyBear.
    fn matmul_instance(mu: usize, kappa: usize, nu: usize, seed: u64) -> MatmulClaim {
        let mut s = seed;
        let mut next = move || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 33) % P
        };
        let a: Vec<Vec<Fp>> = (0..1 << mu)
            .map(|_| (0..1 << kappa).map(|_| next()).collect())
            .collect();
        let b: Vec<Vec<Fp>> = (0..1 << kappa)
            .map(|_| (0..1 << nu).map(|_| next()).collect())
            .collect();
        MatmulClaim {
            mu,
            kappa,
            nu,
            a,
            b,
        }
    }

    /// `Assurance/ZkmlMatmulSumcheck.lean`'s `mle₂_contraction`, checked numerically
    /// OFF the cube: the extension of the true output at a random `(x,y)` equals the
    /// inner product of the two folded tables. The Lean statement is the theorem;
    /// this is the seam agreeing with it.
    #[test]
    fn matmul_contraction_identity_off_cube() {
        let claim = matmul_instance(2, 3, 2, 7);
        let x = [123456789, 987654321];
        let y = [555555555, 42];
        let out = claim.output(P);
        let g = claim.row_partial(&x, P);
        let h = claim.col_partial(&y, P);
        let inner = (0..g.len()).fold(0, |acc, q| add_mod(acc, mul_mod(g[q], h[q], P), P));
        assert_eq!(mle2_eval(&out, &x, &y, P), inner, "mle₂_contraction");
        // ...and the cube corners still read the table (mle₂_agrees).
        assert_eq!(mle2_eval(&out, &[0, 0], &[1, 0], P), out[0][1]);
    }

    /// The contraction is NOT the Hadamard product — `matmul_is_not_hadamard`, in
    /// Rust, so a reader of this module cannot re-make the naming mistake.
    #[test]
    fn matmul_is_not_hadamard() {
        let claim = matmul_instance(1, 1, 1, 11);
        let out = claim.output(P);
        let hadamard = mul_mod(claim.a[0][0], claim.b[0][0], P);
        assert_ne!(out[0][0], hadamard);
    }

    #[test]
    fn matmul_honest_proof_verifies() {
        let claim = matmul_instance(2, 4, 3, 99);
        let x = [11, 22];
        let y = [33, 44, 55];
        let out = claim.output(P);
        let tabs = claim.tables(&x, &y, P);
        let chal: Vec<Fp> = vec![101, 202, 303, 404];
        let proof = prove_matmul(&claim, &x, &y, &chal, P);
        assert_eq!(proof.claim, mle2_eval(&out, &x, &y, P), "claim IS Ĉ(x,y)");
        assert!(verify_matmul(
            &out,
            &x,
            &y,
            &proof,
            |r| (mle_eval(&tabs.a, r, P), mle_eval(&tabs.b, r, P)),
            P
        ));
    }

    /// A FORGED output table is rejected, and the mutation is asserted to be real
    /// first so this cannot decay into a test of the honest table. Two adversaries:
    /// the lazy one keeps the honest total (rejected on the target check), the
    /// serious one sends the total its forged table actually has (rejected at round
    /// 0's boolean check, because the honest round messages do not sum to it).
    #[test]
    fn matmul_forged_output_rejected() {
        let claim = matmul_instance(2, 4, 2, 5);
        let x = [7, 9];
        let y = [13, 17];
        let out = claim.output(P);
        let mut forged = out.clone();
        forged[1][0] = add_mod(forged[1][0], 1, P);
        assert_ne!(forged[1][0], out[1][0], "the mutation must be real");
        let tabs = claim.tables(&x, &y, P);
        let chal: Vec<Fp> = vec![21, 22, 23, 24];
        let open = |r: &[Fp]| (mle_eval(&tabs.a, r, P), mle_eval(&tabs.b, r, P));

        let honest = prove_matmul(&claim, &x, &y, &chal, P);
        assert!(
            !verify_matmul(&forged, &x, &y, &honest, open, P),
            "lazy forgery: the target no longer matches the claim"
        );

        let mut matched = honest.clone();
        matched.claim = mle2_eval(&forged, &x, &y, P);
        assert_ne!(matched.claim, honest.claim, "the forged target must differ");
        assert!(
            !verify_matmul(&forged, &x, &y, &matched, open, P),
            "matched forgery: round 0's boolean check fails"
        );
    }

    /// ⚑ The contraction instance rides a degree-3 wire with a degree-2 message:
    /// the third finite difference is ZERO in every round (the head is constant and
    /// the second pair is dead) while the second is not. Both halves are theorems in
    /// `Assurance/ZkmlMatmulConformance.lean` (`matmulRounds_are_not_cubic`,
    /// `matmulRounds_are_quadratic`); this is the same fact on the engine.
    #[test]
    fn matmul_message_is_quadratic_on_a_cubic_wire() {
        let claim = matmul_instance(1, 3, 1, 31);
        let x = [111];
        let y = [222];
        let mut state = claim.tables(&x, &y, P);
        let chal: Vec<Fp> = vec![5, 6, 7];
        for &r in chal.iter() {
            let h = cubic_round_evals(&state, P);
            let third = sub_mod(
                add_mod(h[3], mul_mod(3, h[1], P), P),
                add_mod(mul_mod(3, h[2], P), h[0], P),
                P,
            );
            assert_eq!(third, 0, "no cubic term at the contraction instance");
            let second = sub_mod(add_mod(h[2], h[0], P), mul_mod(2, h[1], P), P);
            assert_ne!(second, 0, "but the message is genuinely quadratic");
            state = state.fold(r, P);
        }
    }

    /// **The measured comparison against the gate route.** MNIST layer 1 is
    /// `[2,784]·[784,100]`, padded to `[2,1024]·[1024,128]`
    /// (`Theory/ZkmlMatmulSum.lean`'s `padded_contraction` is why that is the same
    /// claim). The AIR route emits one gate per DSL node — `m·n·(2k+2)` — which is
    /// 314 000 gates unpadded and 524 800 padded, at a measured ≈52 bytes/gate of
    /// descriptor JSON. This route sends `κ` round messages of four field elements.
    ///
    /// What this does NOT measure, and must not be quoted as if it did:
    /// `[MATMUL-pcs]`, the BaseFold RBR/BCS proofs for all three root-bound MLE
    /// claims. The claim object exists; the proof transcript does not.
    #[test]
    fn matmul_at_mnist_layer_one_size() {
        let claim = matmul_instance(1, 10, 7, 2026);
        let x = [111111111];
        let y = [222222222, 3, 5, 7, 11, 13, 17];
        let chal: Vec<Fp> = (0..10).map(|i| 1000003 + i as u64).collect();

        let t0 = std::time::Instant::now();
        let out = claim.output(P);
        let t_out = t0.elapsed();

        // Split the prover, because "prove" hides two very different costs: binding
        // the outer indices (a partial evaluation over the whole operand) and the
        // sumcheck rounds themselves.
        let t1 = std::time::Instant::now();
        let tabs = claim.tables(&x, &y, P);
        let t_bind = t1.elapsed();
        let t1b = std::time::Instant::now();
        let proof = prove_cubic_sumcheck(&tabs, &chal, P);
        let t_rounds = t1b.elapsed();
        let t_prove = t_bind + t_rounds;
        let t2 = std::time::Instant::now();
        let ok = verify_matmul(
            &out,
            &x,
            &y,
            &proof,
            |r| (mle_eval(&tabs.a, r, P), mle_eval(&tabs.b, r, P)),
            P,
        );
        let t_verify = t2.elapsed();
        assert!(ok);

        // Transcript: the claim, κ messages of 4 nodes, κ challenges.
        let felts = 1 + 4 * proof.rounds.len() + proof.challenges.len();
        assert_eq!(felts, 51);
        let bytes = felts * 8;
        let air_gates_unpadded = 2 * 100 * (2 * 784 + 2);
        let air_gates_padded = 2 * 128 * (2 * 1024 + 2);
        assert_eq!(air_gates_unpadded, 314_000);
        assert_eq!(air_gates_padded, 524_800);
        println!(
            "matmul [2,1024]x[1024,128]: output {:?}, bind-outer {:?}, rounds {:?}, \
             prove {:?}, verify {:?}; \
             transcript {felts} field elements = {bytes} bytes + 3 UNPRICED MLE proofs; \
             AIR route {air_gates_unpadded} gates unpadded / {air_gates_padded} padded \
             (~{} MB of descriptor at 52 B/gate)",
            t_out,
            t_bind,
            t_rounds,
            t_prove,
            t_verify,
            air_gates_padded * 52 / 1_000_000
        );
    }
}
