// Batched negacyclic RNS NTT over ~61-bit primes, and the he_outer / he_matvec return pipeline, for CUDA.
// 2026-11-06, accelerator readiness (initiative 17), lane w1-bfv. Compiled at run time by cupy (NVRTC);
// host harness: accel_bench_cuda.py. Convention: accel_rns_ref.py (Cooley-Tukey forward with psi merged
// into psi_brv twiddles, natural in / bit-reversed out; Gentleman-Sande inverse with ipsi_brv, N^-1 folded
// into the last stage). Every stored value is a canonical residue in [0, p).
//
// Layout: a batch is `rows` polynomials of N words; row r uses prime index r % L. Tables are [L][N].
// Modular multiply by a FIXED operand w (twiddles, plaintext spectra, public key, secret key), MODE:
//   0  Shoup:      wq = floor(w 2^64 / p);  q = mulhi(a, wq); r = a w - q p (mod 2^64) in [0, 2p)
//   1  Montgomery: w stored as w 2^64 mod p; t = (a w + m p) / 2^64, m = a w (-p^-1) mod 2^64, in [0, 2p)
// Both need p < 2^62 and a < 2^64 (Shoup) or a, w < p (Montgomery).
// Two-phase NTT: phase A works on R = N / E "rows" of a column block (stages with pair distance >= E),
// phase B on contiguous segments of E words (pair distance < E). E = N makes it one kernel, phase A empty.

typedef unsigned long long u64;
typedef long long i64;

struct ModC {
    u64 p;      // prime
    u64 pn;     // -p^-1 mod 2^64 (Montgomery)
    u64 ninv_w, ninv_q;   // N^-1 as a fixed operand (w, Shoup quotient) in this MODE's form
    u64 last_w, last_q;   // ipsi_brv[1] * N^-1, likewise
    u64 r2;     // 2^128 mod p (to enter Montgomery form)
    u64 two64;  // 2^64 mod p
};

__device__ __forceinline__ u64 addm(u64 a, u64 b, u64 p) { u64 s = a + b; return s >= p ? s - p : s; }
__device__ __forceinline__ u64 subm(u64 a, u64 b, u64 p) { return a >= b ? a - b : a + p - b; }

template <int MODE>
__device__ __forceinline__ u64 mulw(u64 a, u64 w, u64 wq, u64 p, u64 pn) {
    if (MODE == 0) {
        u64 q = __umul64hi(a, wq);
        u64 r = a * w - q * p;
        return r >= p ? r - p : r;
    } else {
        u64 lo = a * w, hi = __umul64hi(a, w);
        u64 m = lo * pn;
        u64 t = hi + __umul64hi(m, p) + (lo != 0ULL);
        return t >= p ? t - p : t;
    }
}

// ------------------------------------------------------------------ forward, phase A (columns)
template <int MODE>
__device__ void fwdA_body(u64* sh, u64* g, const u64* w, const u64* wq, u64 p, u64 pn, int logN, int logR, int logC,
                          int c0) {
    const int R = 1 << logR, C = 1 << logC, CS = 1 << (logN - logR), tot = R << logC;
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x) {
        int k = idx >> logC, cc = idx & (C - 1);
        sh[idx] = g[(size_t)k * CS + c0 + cc];
    }
    __syncthreads();
    for (int s = 0; s < logR; s++) {
        const int ld = logR - s - 1;           // pair distance 2^ld in row space
        for (int b = threadIdx.x; b < (tot >> 1); b += blockDim.x) {
            int cc = b & (C - 1), bk = b >> logC;
            int grp = bk >> ld, r = bk & ((1 << ld) - 1);
            int k1 = (grp << (ld + 1)) + r, k2 = k1 + (1 << ld);
            int wi = (1 << s) + grp;
            u64 U = sh[(k1 << logC) + cc];
            u64 V = mulw<MODE>(sh[(k2 << logC) + cc], w[wi], wq[wi], p, pn);
            sh[(k1 << logC) + cc] = addm(U, V, p);
            sh[(k2 << logC) + cc] = subm(U, V, p);
        }
        __syncthreads();
    }
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x) {
        int k = idx >> logC, cc = idx & (C - 1);
        g[(size_t)k * CS + c0 + cc] = sh[idx];
    }
}

template <int MODE>
__global__ void fwdA(u64* data, const u64* tw, const u64* twq, const ModC* mc, int logN, int logR, int logC, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN;
    fwdA_body<MODE>(sh, data + (size_t)row * N, tw + (size_t)l * N, twq + (size_t)l * N, mc[l].p, mc[l].pn, logN,
                    logR, logC, blockIdx.x << logC);
}

// ------------------------------------------------------------------ forward, phase B (segments of E)
template <int MODE>
__global__ void fwdB(u64* data, const u64* tw, const u64* twq, const ModC* mc, int logN, int logE, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN, E = 1 << logE;
    const u64 p = mc[l].p, pn = mc[l].pn;
    const u64* w = tw + (size_t)l * N;
    const u64* wq = twq + (size_t)l * N;
    const int base = blockIdx.x << logE;
    u64* g = data + (size_t)row * N + base;
    for (int i = threadIdx.x; i < E; i += blockDim.x) sh[i] = g[i];
    __syncthreads();
    for (int s = logN - logE; s < logN; s++) {
        const int lt = logN - s - 1;           // t = 2^lt
        for (int b = threadIdx.x; b < (E >> 1); b += blockDim.x) {
            int grp = b >> lt, r = b & ((1 << lt) - 1);
            int l1 = (grp << (lt + 1)) + r, l2 = l1 + (1 << lt);
            int wi = (1 << s) + (base >> (lt + 1)) + grp;
            u64 U = sh[l1];
            u64 V = mulw<MODE>(sh[l2], w[wi], wq[wi], p, pn);
            sh[l1] = addm(U, V, p);
            sh[l2] = subm(U, V, p);
        }
        __syncthreads();
    }
    for (int i = threadIdx.x; i < E; i += blockDim.x) g[i] = sh[i];
}

// ------------------------------------------------------------------ inverse (GS), phase B first, then A
// GS butterfly at group twiddle index wi; `last` (h == 1) folds N^-1 into both outputs.
template <int MODE>
__device__ __forceinline__ void gs(u64& x, u64& y, const u64* w, const u64* wq, int wi, const ModC& m, bool last) {
    u64 U = x, V = y;
    if (!last) {
        x = addm(U, V, m.p);
        y = mulw<MODE>(subm(U, V, m.p), w[wi], wq[wi], m.p, m.pn);
    } else {
        x = mulw<MODE>(addm(U, V, m.p), m.ninv_w, m.ninv_q, m.p, m.pn);
        y = mulw<MODE>(subm(U, V, m.p), m.last_w, m.last_q, m.p, m.pn);
    }
}

// FUSE = 0: plain inverse. FUSE = 1: on load, x = P^ * A0^ + K^ * U^ (the return's NTT-domain MAC), with the
// operands addressed per row (see ret_index). Fused variants are checked against the unfused path.
template <int MODE>
__global__ void invB(u64* data, const u64* itw, const u64* itwq, const ModC* mc, int logN, int logE, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN, E = 1 << logE;
    const ModC m = mc[l];
    const u64* w = itw + (size_t)l * N;
    const u64* wq = itwq + (size_t)l * N;
    const int base = blockIdx.x << logE;
    u64* g = data + (size_t)row * N + base;
    for (int i = threadIdx.x; i < E; i += blockDim.x) sh[i] = g[i];
    __syncthreads();
    for (int lt = 0; lt < logE; lt++) {        // t = 2^lt, h = N / 2t
        const int lh = logN - lt - 1;
        for (int b = threadIdx.x; b < (E >> 1); b += blockDim.x) {
            int grp = b >> lt, r = b & ((1 << lt) - 1);
            int l1 = (grp << (lt + 1)) + r, l2 = l1 + (1 << lt);
            int wi = (1 << lh) + (base >> (lt + 1)) + grp;
            gs<MODE>(sh[l1], sh[l2], w, wq, wi, m, lh == 0);
        }
        __syncthreads();
    }
    for (int i = threadIdx.x; i < E; i += blockDim.x) g[i] = sh[i];
}

template <int MODE>
__global__ void invA(u64* data, const u64* itw, const u64* itwq, const ModC* mc, int logN, int logR, int logC, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN;
    const ModC m = mc[l];
    const u64* w = itw + (size_t)l * N;
    const u64* wq = itwq + (size_t)l * N;
    const int R = 1 << logR, C = 1 << logC, CS = 1 << (logN - logR), tot = R << logC, c0 = blockIdx.x << logC;
    u64* g = data + (size_t)row * N;
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x) {
        int k = idx >> logC, cc = idx & (C - 1);
        sh[idx] = g[(size_t)k * CS + c0 + cc];
    }
    __syncthreads();
    for (int s = logR - 1; s >= 0; s--) {      // h = 2^s, pair distance in rows 2^(logR - s - 1)
        const int ld = logR - s - 1;
        for (int b = threadIdx.x; b < (tot >> 1); b += blockDim.x) {
            int cc = b & (C - 1), bk = b >> logC;
            int grp = bk >> ld, r = bk & ((1 << ld) - 1);
            int k1 = (grp << (ld + 1)) + r, k2 = k1 + (1 << ld);
            gs<MODE>(sh[(k1 << logC) + cc], sh[(k2 << logC) + cc], w, wq, (1 << s) + grp, m, s == 0);
        }
        __syncthreads();
    }
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x) {
        int k = idx >> logC, cc = idx & (C - 1);
        g[(size_t)k * CS + c0 + cc] = sh[idx];
    }
}

// ------------------------------------------------------------------ return pipeline, elementwise kernels
// Return r (0 <= r < nret), prime l, coefficient k. Spectra arrays are [*][L][N]. Fixed operands (plaintext
// spectra Ph, public key K0/K1) are stored in this MODE's form with a quotient array (Shoup) or in
// Montgomery form (quotient array unused). With K blocks per return (K = 1: he_outer; K = d / dc: a he_matvec
// row block summed over its column blocks):
//   acc_c = sum_{b < K} Ph[pidx[r] K + b] * Ch[cidx[r] K + b][c] + Kc * U^[r],   c = 0, 1,
// written to Acc[r][c][l][k] (Ch is [*][2][L][N]).
template <int MODE>
__global__ void ret_mac(u64* Acc, const u64* Ph, const u64* Phq, const u64* Ch, const u64* K0, const u64* K0q,
                        const u64* K1, const u64* K1q, const u64* Uh, const int* pidx, const int* cidx, int K,
                        const ModC* mc, int logN, int L, int nret) {
    const int N = 1 << logN;
    const size_t LN = (size_t)L * N;
    size_t gid = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= (size_t)nret * LN) return;
    const int r = gid / LN;
    const size_t lk = gid - (size_t)r * LN;
    const int l = lk >> logN;
    const u64 p = mc[l].p, pn = mc[l].pn;
    const u64 u = Uh[r * LN + lk];
    u64 a0 = mulw<MODE>(u, K0[lk], K0q[lk], p, pn);
    u64 a1 = mulw<MODE>(u, K1[lk], K1q[lk], p, pn);
    const size_t pb = (size_t)pidx[r] * K, cb = (size_t)cidx[r] * K;
    for (int b = 0; b < K; b++) {
        const u64 P = Ph[(pb + b) * LN + lk], Pq = Phq[(pb + b) * LN + lk];
        a0 = addm(a0, mulw<MODE>(Ch[(2 * (cb + b)) * LN + lk], P, Pq, p, pn), p);
        a1 = addm(a1, mulw<MODE>(Ch[(2 * (cb + b) + 1) * LN + lk], P, Pq, p, pn), p);
    }
    Acc[(2 * (size_t)r) * LN + lk] = a0;
    Acc[(2 * (size_t)r + 1) * LN + lk] = a1;
}

// c0 += E0 + mask_encode(M) ; c1 += E1, in place on Acc (coefficient domain after the inverse NTT).
// mask_encode(M) mod p_l = (t - rr) (2t)^-1 mod p_l, rr = (2 ((Q mod t) M mod t) + t) mod 2t (accel_rns_ref).
// Mt: per prime {(2t)^-1 mod p_l: w, q}; T: {t, (Q mod t), its Shoup quotient wrt t}.
__global__ void ret_finalize(u64* Acc, const u64* E0, const u64* E1, const u64* M, const ModC* mc, const u64* inv2t,
                             const u64* inv2tq, u64 t, u64 qmt, u64 qmtq, int logN, int L, int nret) {
    const int N = 1 << logN;
    const size_t LN = (size_t)L * N;
    size_t gid = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= (size_t)nret * LN) return;
    const int r = gid / LN;
    const size_t lk = gid - (size_t)r * LN;
    const int l = lk >> logN, k = lk & (N - 1);
    const u64 p = mc[l].p;
    const u64 x = mulw<0>(M[(size_t)r * N + k], qmt, qmtq, t, 0);           // (Q mod t) M mod t
    u64 rr = 2 * x + t;
    if (rr >= 2 * t) rr -= 2 * t;
    i64 v = (i64)t - (i64)rr;
    while (v < 0) v += (i64)p;
    while ((u64)v >= p) v -= (i64)p;
    const u64 me = mulw<0>((u64)v, inv2t[l], inv2tq[l], p, 0);
    u64* c0 = Acc + (2 * (size_t)r) * LN + lk;
    u64* c1 = Acc + (2 * (size_t)r + 1) * LN + lk;
    *c0 = addm(addm(*c0, E0[(size_t)r * LN + lk], p), me, p);
    *c1 = addm(*c1, E1[(size_t)r * LN + lk], p);
}

// Decryption, step 1: X[r] = c1^[r] * S^ (copy of c1 spectrum multiplied in place); X is [nret][L][N].
template <int MODE>
__global__ void pmul_fixed(u64* X, const u64* S, const u64* Sq, const ModC* mc, int logN, int L, int nrows) {
    const int N = 1 << logN;
    const size_t LN = (size_t)L * N;
    size_t gid = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= (size_t)nrows * N) return;
    const size_t lk = gid % LN;
    const int l = lk >> logN;
    X[gid] = mulw<MODE>(X[gid], S[lk], Sq[lk], mc[l].p, mc[l].pn);
}

// Decryption, step 2: x_l = c0_l + X_l, then HPS scaling round(t x / Q) mod t (accel_rns_ref.HPS):
// ip = sum (x w_l mod t) + sum hi(x thh_l), fr = sum lo(x thh_l) + hi(x thl_l) (carries counted),
// out = (ip + carries + round(fr)) mod t; amb counts fractions within 2L+2 ulp of 1/2.
__global__ void hps_decrypt(u64* out, unsigned int* amb, const u64* C0, int c0_stride_ret, const u64* X,
                            const ModC* mc, const u64* hw, const u64* hwq, const u64* thh, const u64* thl, u64 t,
                            int logN, int L, int nret) {
    const int N = 1 << logN;
    size_t gid = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= (size_t)nret * N) return;
    const int r = gid >> logN, k = gid & (N - 1);
    u64 ip = 0, fr = 0, carry = 0;
    for (int l = 0; l < L; l++) {
        const size_t off = (size_t)l * N + k;
        const u64 x = addm(C0[(size_t)r * c0_stride_ret + off], X[(size_t)r * L * N + off], mc[l].p);
        u64 a = mulw<0>(x, hw[l], hwq[l], t, 0);
        ip += a; if (ip >= t) ip -= t;
        u64 hi = __umul64hi(x, thh[l]);
        while (hi >= t) hi -= t;
        ip += hi; if (ip >= t) ip -= t;
        u64 lo = x * thh[l];
        u64 f = __umul64hi(x, thl[l]);
        u64 s1 = fr + lo; carry += (s1 < fr);
        u64 s2 = s1 + f; carry += (s2 < s1);
        fr = s2;
    }
    const u64 half = 1ULL << 63;
    u64 fr2 = fr + half;
    carry += (fr2 < fr);
    const u64 dist = fr >= half ? fr - half : half - fr;     // unsigned: fr == 0 must not overflow
    if (dist < (u64)(2 * L + 2)) atomicAdd(amb, 1u);
    u64 c = carry % t;
    ip += c; if (ip >= t) ip -= t;
    out[gid] = ip;
}

// ------------------------------------------------------------------ randomness for the bench (NOT a CSPRNG)
// splitmix64 on (seed, counter): stands in for the protocol's CSPRNG so the timing includes generating u, e,
// M and the flood on device. A ChaCha20/AES-CTR generator costs more; BFV.md prices it separately.
__device__ __forceinline__ u64 smix(u64 x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}
// U[r][l][k]: ternary u (same value across primes), E0/E1: e in [-8, 8] (+ flood in E0, as 2^fbits-scaled
// 128-bit value reduced per prime), M[r][k] < t (by rejection-free 61-bit draw, then one subtraction).
__global__ void gen_random(u64* U, u64* E0, u64* E1, u64* M, const ModC* mc, u64 t, u64 seed, int fbits, int logN,
                           int L, int nret) {
    const int N = 1 << logN;
    size_t gid = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= (size_t)nret * N) return;
    const int r = gid >> logN, k = gid & (N - 1);
    u64 z0 = smix(seed ^ (gid * 4 + 0)), z1 = smix(seed ^ (gid * 4 + 1)), z2 = smix(seed ^ (gid * 4 + 2)),
        z3 = smix(seed ^ (gid * 4 + 3));
    int u = (int)(z0 % 3) - 1, e0 = (int)((z0 >> 32) % 17) - 8, e1 = (int)((z1 >> 40) % 17) - 8;
    u64 m = z1 & ((1ULL << 61) - 1);
    if (m >= t) m -= t;
    M[gid] = m;
    // flood: f = (z2 mod 2^(fbits-64)) * 2^64 + z3, signed by the top bit of z1
    u64 fh = fbits > 64 ? (z2 & ((1ULL << (fbits - 64)) - 1)) : 0;
    bool neg = (z1 >> 63) & 1;
    for (int l = 0; l < L; l++) {
        const ModC m_ = mc[l];
        const u64 p = m_.p;
        // f mod p = fh * (2^64 mod p) + z3 mod p
        u64 lo = fh * m_.two64, hi = __umul64hi(fh, m_.two64);
        // 128-bit (hi, lo) mod p by Montgomery-free long division in two steps: (hi 2^64 + lo) mod p
        u64 a = mulw<1>(hi, m_.r2, 0, p, m_.pn);                // hi 2^128 / 2^64 = hi 2^64 mod p
        u64 f = addm(a, lo % p, p);
        f = addm(f, z3 % p, p);
        if (neg) f = f ? p - f : 0;
        const size_t o = ((size_t)r * L + l) * N + k;
        U[o] = u >= 0 ? (u64)u : p - 1;
        E0[o] = addm(f, e0 >= 0 ? (u64)e0 : p - (u64)(-e0), p);
        E1[o] = e1 >= 0 ? (u64)e1 : p - (u64)(-e1);
    }
}

// ------------------------------------------------------------------ fixed-operand preparation
// Shoup quotient floor(w 2^64 / p) for w < p by 64-step restoring division (amortized: plaintext spectra).
__global__ void shoup_quot(u64* w, u64* q, const ModC* mc, int logN, int L, long long n) {
    long long gid = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= n) return;
    const u64 p = mc[(gid >> logN) % L].p;
    u64 rem = w[gid], qq = 0;
    for (int i = 0; i < 64; i++) {
        rem <<= 1; qq <<= 1;
        if (rem >= p) { rem -= p; qq |= 1; }
    }
    q[gid] = qq;
}
// Montgomery form w 2^64 mod p, in place (q untouched).
__global__ void to_mont(u64* w, u64* q, const ModC* mc, int logN, int L, long long n) {
    long long gid = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= n) return;
    const ModC m = mc[(gid >> logN) % L];
    w[gid] = mulw<1>(w[gid], m.r2, 0, m.p, m.pn);
}

// ------------------------------------------------------------------ register-blocked variants (radix 2^G)
// Same transform and words as fwdA/fwdB/invB/invA; each thread keeps 2^g words in registers across g
// consecutive stages, so shared-memory round trips and __syncthreads drop by g. Unit u of a group covers
// indices l0 + m 2^ltm (m < 2^g), l0 = hi 2^(lt0 + 1) + lo, lo < 2^ltm; stage q pairs m with m + 2^(g-1-q)
// (forward, distances shrinking) or m with m + 2^q (inverse, distances growing).
template <int MODE, int g>
__device__ __forceinline__ void fwdB_group(u64* sh, const u64* w, const u64* wq, u64 p, u64 pn, int logN, int logE,
                                           int s0, int base) {
    const int lt0 = logN - s0 - 1, ltm = lt0 - (g - 1);
    const int units = (1 << logE) >> g;
    for (int u = threadIdx.x; u < units; u += blockDim.x) {
        const int lo = u & ((1 << ltm) - 1), hi = u >> ltm;
        const int l0 = (hi << (lt0 + 1)) + lo;
        u64 x[1 << g];
#pragma unroll
        for (int m = 0; m < (1 << g); m++) x[m] = sh[l0 + (m << ltm)];
#pragma unroll
        for (int q = 0; q < g; q++) {
            const int s = s0 + q, lt = lt0 - q, dm = 1 << (g - 1 - q);
#pragma unroll
            for (int m1 = 0; m1 < (1 << g); m1++) {
                if (m1 & dm) continue;
                const int wi = (1 << s) + ((base + l0 + (m1 << ltm)) >> (lt + 1));
                u64 U = x[m1], V = mulw<MODE>(x[m1 + dm], w[wi], wq[wi], p, pn);
                x[m1] = addm(U, V, p);
                x[m1 + dm] = subm(U, V, p);
            }
        }
#pragma unroll
        for (int m = 0; m < (1 << g); m++) sh[l0 + (m << ltm)] = x[m];
    }
}

template <int MODE, int g>
__device__ __forceinline__ void invB_group(u64* sh, const u64* w, const u64* wq, const ModC& mo, int logN, int logE,
                                           int ltm, int base) {
    const int ltt = ltm + g - 1;
    const int units = (1 << logE) >> g;
    for (int u = threadIdx.x; u < units; u += blockDim.x) {
        const int lo = u & ((1 << ltm) - 1), hi = u >> ltm;
        const int l0 = (hi << (ltt + 1)) + lo;
        u64 x[1 << g];
#pragma unroll
        for (int m = 0; m < (1 << g); m++) x[m] = sh[l0 + (m << ltm)];
#pragma unroll
        for (int q = 0; q < g; q++) {
            const int lt = ltm + q, dm = 1 << q, lh = logN - lt - 1;
#pragma unroll
            for (int m1 = 0; m1 < (1 << g); m1++) {
                if (m1 & dm) continue;
                const int wi = (1 << lh) + ((base + l0 + (m1 << ltm)) >> (lt + 1));
                gs<MODE>(x[m1], x[m1 + dm], w, wq, wi, mo, lh == 0);
            }
        }
#pragma unroll
        for (int m = 0; m < (1 << g); m++) sh[l0 + (m << ltm)] = x[m];
    }
}

template <int MODE, int g>
__device__ __forceinline__ void fwdA_group(u64* sh, const u64* w, const u64* wq, u64 p, u64 pn, int logR, int logC,
                                           int s0) {
    const int ld0 = logR - s0 - 1, ldm = ld0 - (g - 1);
    const int units = ((1 << logR) >> g) << logC;
    for (int u = threadIdx.x; u < units; u += blockDim.x) {
        const int cc = u & ((1 << logC) - 1), uk = u >> logC;
        const int lo = uk & ((1 << ldm) - 1), hi = uk >> ldm;
        const int k0 = (hi << (ld0 + 1)) + lo;
        u64 x[1 << g];
#pragma unroll
        for (int m = 0; m < (1 << g); m++) x[m] = sh[((k0 + (m << ldm)) << logC) + cc];
#pragma unroll
        for (int q = 0; q < g; q++) {
            const int s = s0 + q, ld = ld0 - q, dm = 1 << (g - 1 - q);
#pragma unroll
            for (int m1 = 0; m1 < (1 << g); m1++) {
                if (m1 & dm) continue;
                const int wi = (1 << s) + ((k0 + (m1 << ldm)) >> (ld + 1));
                u64 U = x[m1], V = mulw<MODE>(x[m1 + dm], w[wi], wq[wi], p, pn);
                x[m1] = addm(U, V, p);
                x[m1 + dm] = subm(U, V, p);
            }
        }
#pragma unroll
        for (int m = 0; m < (1 << g); m++) sh[((k0 + (m << ldm)) << logC) + cc] = x[m];
    }
}

template <int MODE, int g>
__device__ __forceinline__ void invA_group(u64* sh, const u64* w, const u64* wq, const ModC& mo, int logR, int logC,
                                           int ldm) {
    const int ldt = ldm + g - 1;
    const int units = ((1 << logR) >> g) << logC;
    for (int u = threadIdx.x; u < units; u += blockDim.x) {
        const int cc = u & ((1 << logC) - 1), uk = u >> logC;
        const int lo = uk & ((1 << ldm) - 1), hi = uk >> ldm;
        const int k0 = (hi << (ldt + 1)) + lo;
        u64 x[1 << g];
#pragma unroll
        for (int m = 0; m < (1 << g); m++) x[m] = sh[((k0 + (m << ldm)) << logC) + cc];
#pragma unroll
        for (int q = 0; q < g; q++) {
            const int ld = ldm + q, s = logR - ld - 1, dm = 1 << q;
#pragma unroll
            for (int m1 = 0; m1 < (1 << g); m1++) {
                if (m1 & dm) continue;
                const int wi = (1 << s) + ((k0 + (m1 << ldm)) >> (ld + 1));
                gs<MODE>(x[m1], x[m1 + dm], w, wq, wi, mo, s == 0);
            }
        }
#pragma unroll
        for (int m = 0; m < (1 << g); m++) sh[((k0 + (m << ldm)) << logC) + cc] = x[m];
    }
}

#define DISPATCH_G(G, g, CALL) \
    switch (g) { case 1: CALL(1); break; case 2: if (G >= 2) CALL(2); break; \
                 case 3: if (G >= 3) CALL(3); break; case 4: if (G >= 4) CALL(4); break; }

template <int MODE, int G>
__global__ void fwdBr(u64* data, const u64* tw, const u64* twq, const ModC* mc, int logN, int logE, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN, E = 1 << logE;
    const u64 p = mc[l].p, pn = mc[l].pn;
    const u64* w = tw + (size_t)l * N;
    const u64* wq = twq + (size_t)l * N;
    const int base = blockIdx.x << logE;
    u64* gm = data + (size_t)row * N + base;
    for (int i = threadIdx.x; i < E; i += blockDim.x) sh[i] = gm[i];
    __syncthreads();
    for (int s0 = logN - logE; s0 < logN;) {
        const int g = min(G, logN - s0);
#define CALLF(gg) fwdB_group<MODE, gg>(sh, w, wq, p, pn, logN, logE, s0, base)
        DISPATCH_G(G, g, CALLF)
#undef CALLF
        __syncthreads();
        s0 += g;
    }
    for (int i = threadIdx.x; i < E; i += blockDim.x) gm[i] = sh[i];
}

template <int MODE, int G>
__global__ void invBr(u64* data, const u64* itw, const u64* itwq, const ModC* mc, int logN, int logE, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN, E = 1 << logE;
    const ModC mo = mc[l];
    const u64* w = itw + (size_t)l * N;
    const u64* wq = itwq + (size_t)l * N;
    const int base = blockIdx.x << logE;
    u64* gm = data + (size_t)row * N + base;
    for (int i = threadIdx.x; i < E; i += blockDim.x) sh[i] = gm[i];
    __syncthreads();
    for (int ltm = 0; ltm < logE;) {
        const int g = min(G, logE - ltm);
#define CALLI(gg) invB_group<MODE, gg>(sh, w, wq, mo, logN, logE, ltm, base)
        DISPATCH_G(G, g, CALLI)
#undef CALLI
        __syncthreads();
        ltm += g;
    }
    for (int i = threadIdx.x; i < E; i += blockDim.x) gm[i] = sh[i];
}

template <int MODE, int G>
__global__ void fwdAr(u64* data, const u64* tw, const u64* twq, const ModC* mc, int logN, int logR, int logC, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN;
    const u64 p = mc[l].p, pn = mc[l].pn;
    const u64* w = tw + (size_t)l * N;
    const u64* wq = twq + (size_t)l * N;
    const int C = 1 << logC, CS = 1 << (logN - logR), tot = (1 << logR) << logC, c0 = blockIdx.x << logC;
    u64* gm = data + (size_t)row * N;
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x)
        sh[idx] = gm[(size_t)(idx >> logC) * CS + c0 + (idx & (C - 1))];
    __syncthreads();
    for (int s0 = 0; s0 < logR;) {
        const int g = min(G, logR - s0);
#define CALLFA(gg) fwdA_group<MODE, gg>(sh, w, wq, p, pn, logR, logC, s0)
        DISPATCH_G(G, g, CALLFA)
#undef CALLFA
        __syncthreads();
        s0 += g;
    }
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x)
        gm[(size_t)(idx >> logC) * CS + c0 + (idx & (C - 1))] = sh[idx];
}

template <int MODE, int G>
__global__ void invAr(u64* data, const u64* itw, const u64* itwq, const ModC* mc, int logN, int logR, int logC, int L) {
    extern __shared__ u64 sh[];
    const int row = blockIdx.y, l = row % L, N = 1 << logN;
    const ModC mo = mc[l];
    const u64* w = itw + (size_t)l * N;
    const u64* wq = itwq + (size_t)l * N;
    const int C = 1 << logC, CS = 1 << (logN - logR), tot = (1 << logR) << logC, c0 = blockIdx.x << logC;
    u64* gm = data + (size_t)row * N;
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x)
        sh[idx] = gm[(size_t)(idx >> logC) * CS + c0 + (idx & (C - 1))];
    __syncthreads();
    for (int ldm = 0; ldm < logR;) {
        const int g = min(G, logR - ldm);
#define CALLIA(gg) invA_group<MODE, gg>(sh, w, wq, mo, logR, logC, ldm)
        DISPATCH_G(G, g, CALLIA)
#undef CALLIA
        __syncthreads();
        ldm += g;
    }
    for (int idx = threadIdx.x; idx < tot; idx += blockDim.x)
        gm[(size_t)(idx >> logC) * CS + c0 + (idx & (C - 1))] = sh[idx];
}
