/* The packed-binary leaf PIOP, minimal and complete in shape (notes/redesign):
 *   (1) zerocheck  sum_x eq(tau,x) * (a(x) b(x) + c(x)) = 0 over three committed BINARY columns (a degree-2
 *       constraint standing in for the DFA's boolean/transition constraints), Gruen-factored eq;
 *   (2) lookup read-check  sum_x eq(r,x) * val[addr(x)] = rv~(r), a 16-entry Tower256 table read through a 4-bit
 *       address column (Shout's read-checking sumcheck, one chunk), with bucketed first round;
 *   (3) the one-hot opening claims ra~(rho, v) for v < 16 at the lookup's final point (eq table + buckets).
 * Columns are packed 64 rows per word. Challenges in GF(2^256) (polynomial basis, isomorphic to Tower256).
 * Challenges come from a SplitMix64 stream (no hash transcript: one Keccak-f per round is noise here).
 *   ./piop check ELL [bad]      -> transcript as JSON (piop_ref.py recomputes it and verifies)
 *   ./piop bench ELL REPS THREADS -> ns per row, Tower256 multiplies per row; THREADS independent proofs */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include "gf256.h"

typedef struct { uint64_t s; } rng_t;
static uint64_t rnd(rng_t *r) { uint64_t z = (r->s += 0x9e3779b97f4a7c15ULL); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static g256 rnd_g(rng_t *r) { g256 x; for (int i = 0; i < 4; i++) x.w[i] = rnd(r); return x; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

typedef struct {
    int ell; size_t n;
    uint64_t *a, *b, *c;  /* packed bits */
    uint8_t *addr;        /* 4-bit addresses, one per row (a packed column of 4 lanes) */
    g256 val[16], *tau, *rz, *rl, *rlk;
    /* transcript */
    g256 *zq;             /* 3 per round */
    g256 zfinal[3];
    g256 lclaim, *lq;     /* 2 per round */
    g256 lfinal, ra[16];
    long mults;
} inst_t;

static int bit(const uint64_t *v, size_t i) { return v[i >> 6] >> (i & 63) & 1; }

static void gen(inst_t *I, int ell, uint64_t seed, int bad) {
    rng_t R = {seed}; size_t n = (size_t)1 << ell, W = (n + 63) / 64;
    I->ell = ell; I->n = n;
    I->a = calloc(W, 8); I->b = calloc(W, 8); I->c = calloc(W, 8); I->addr = malloc(n);
    for (size_t w = 0; w < W; w++) { I->a[w] = rnd(&R); I->b[w] = rnd(&R); I->c[w] = I->a[w] & I->b[w]; }
    if (n < 64) { uint64_t m = (1ULL << n) - 1; I->a[0] &= m; I->b[0] &= m; I->c[0] &= m; }
    if (bad) I->c[(bad % n) >> 6] ^= 1ULL << ((bad % n) & 63);   /* one violated row */
    for (size_t i = 0; i < n; i++) I->addr[i] = rnd(&R) & 15;
    for (int v = 0; v < 16; v++) I->val[v] = rnd_g(&R);
    I->tau = malloc(ell * sizeof(g256)); I->rz = malloc(ell * sizeof(g256)); I->rl = malloc(ell * sizeof(g256)); I->rlk = malloc(ell * sizeof(g256));
    for (int i = 0; i < ell; i++) I->tau[i] = rnd_g(&R);
    for (int i = 0; i < ell; i++) I->rz[i] = rnd_g(&R);
    for (int i = 0; i < ell; i++) I->rl[i] = rnd_g(&R);
    for (int i = 0; i < ell; i++) I->rlk[i] = rnd_g(&R);
    I->zq = malloc(3 * ell * sizeof(g256)); I->lq = malloc(2 * ell * sizeof(g256));
}

/* eq table over m variables pt[0..m) (pt[0] is the index LSB): out[x] = prod eq(pt_k, x_k); 2^m - 1 mults */
static void eq_table(g256 *out, const g256 *pt, int m) {
    out[0] = G_ONE;
    for (int k = 0; k < m; k++) {
        size_t h = (size_t)1 << k;
        for (size_t i = 0; i < h; i++) {
            g256 hi = g_mul(out[i], pt[k]);          /* x_k = 1: eq = t   (1+t+1 = t) */
            out[i] = g_add(out[i], hi);              /* x_k = 0: eq = 1+t */
            out[i + h] = hi;
        }
    }
}
/* careful: the loop above writes out[i+h] for index bit k = 1, i.e. pt[k] is bit k: LSB-first. */

static void prove(inst_t *I) {
    int ell = I->ell; size_t n = I->n;
    long m0 = g256_mults;
    /* ---------- (1) zerocheck ---------- */
    g256 *E = malloc((n / 2 + 1) * sizeof(g256));
    eq_table(E, I->tau + 1, ell - 1);                  /* E_0 over x_1..x_{ell-1} */
    g256 *A = malloc(n / 2 * sizeof(g256)), *B = malloc(n / 2 * sizeof(g256)), *C = malloc(n / 2 * sizeof(g256));
    {   /* round 0 on bits: masks select E entries; fold with rho to GF(2^256) without multiplies */
        g256 q0 = {{0}}, q1 = {{0}}, qi = {{0}};
        for (size_t j = 0; j < n / 2; j++) {
            int a0 = bit(I->a, 2 * j), a1 = bit(I->a, 2 * j + 1), b0 = bit(I->b, 2 * j), b1 = bit(I->b, 2 * j + 1);
            int c0 = bit(I->c, 2 * j), c1 = bit(I->c, 2 * j + 1);
            uint64_t m_0 = -(uint64_t)((a0 & b0) ^ c0), m_1 = -(uint64_t)((a1 & b1) ^ c1), m_i = -(uint64_t)((a0 ^ a1) & (b0 ^ b1));
            for (int w = 0; w < 4; w++) { q0.w[w] ^= E[j].w[w] & m_0; q1.w[w] ^= E[j].w[w] & m_1; qi.w[w] ^= E[j].w[w] & m_i; }
        }
        I->zq[0] = q0; I->zq[1] = q1; I->zq[2] = qi;
        g256 r = I->rz[0];
        for (size_t j = 0; j < n / 2; j++) {
#define FOLDBIT(dst, v) do { int x0 = bit(v, 2 * j), x1 = bit(v, 2 * j + 1); uint64_t mr = -(uint64_t)(x0 ^ x1); \
            for (int w = 0; w < 4; w++) dst[j].w[w] = r.w[w] & mr; dst[j].w[0] ^= (uint64_t)x0; } while (0)
            FOLDBIT(A, I->a); FOLDBIT(B, I->b); FOLDBIT(C, I->c);
        }
        for (size_t j = 0; j < n / 4; j++) E[j] = g_add(E[2 * j], E[2 * j + 1]);  /* E_1: sum out x_1 */
    }
    for (int i = 1; i < ell; i++) {
        size_t half = n >> (i + 1);
        g256 q0 = {{0}}, q1 = {{0}}, qi = {{0}}; g256 r = I->rz[i];
        for (size_t j = 0; j < half; j++) {
            g256 A0 = A[2 * j], A1 = A[2 * j + 1], B0 = B[2 * j], B1 = B[2 * j + 1], C0 = C[2 * j], C1 = C[2 * j + 1];
            g256 P0 = g_add(g_mul(A0, B0), C0), P1 = g_add(g_mul(A1, B1), C1), Pi = g_mul(g_add(A0, A1), g_add(B0, B1));
            q0 = g_add(q0, g_mul(E[j], P0)); q1 = g_add(q1, g_mul(E[j], P1)); qi = g_add(qi, g_mul(E[j], Pi));
            A[j] = g_add(A0, g_mul(r, g_add(A0, A1))); B[j] = g_add(B0, g_mul(r, g_add(B0, B1))); C[j] = g_add(C0, g_mul(r, g_add(C0, C1)));
        }
        I->zq[3 * i] = q0; I->zq[3 * i + 1] = q1; I->zq[3 * i + 2] = qi;
        for (size_t j = 0; j < half / 2; j++) E[j] = g_add(E[2 * j], E[2 * j + 1]);
        if (half == 1) E[0] = G_ONE;
    }
    I->zfinal[0] = A[0]; I->zfinal[1] = B[0]; I->zfinal[2] = C[0];
    /* ---------- (2) lookup read-check ---------- */
    eq_table(E, I->rl + 1, ell - 1);
    g256 *G = A;  /* reuse */
    {
        g256 bk0[16], bk1[16]; memset(bk0, 0, sizeof bk0); memset(bk1, 0, sizeof bk1);
        for (size_t j = 0; j < n / 2; j++) { bk0[I->addr[2 * j]] = g_add(bk0[I->addr[2 * j]], E[j]); bk1[I->addr[2 * j + 1]] = g_add(bk1[I->addr[2 * j + 1]], E[j]); }
        g256 q0 = {{0}}, q1 = {{0}};
        for (int v = 0; v < 16; v++) { q0 = g_add(q0, g_mul(bk0[v], I->val[v])); q1 = g_add(q1, g_mul(bk1[v], I->val[v])); }
        I->lq[0] = q0; I->lq[1] = q1;
        /* claim = eq(r_0,0) q0 + eq(r_0,1) q1 */
        I->lclaim = g_add(g_mul(g_eq(I->rl[0], (g256){{0}}), q0), g_mul(g_eq(I->rl[0], G_ONE), q1));
        g256 rv[16]; for (int v = 0; v < 16; v++) rv[v] = g_mul(I->rlk[0], I->val[v]);
        for (size_t j = 0; j < n / 2; j++) G[j] = g_add(I->val[I->addr[2 * j]], g_add(rv[I->addr[2 * j]], rv[I->addr[2 * j + 1]]));
        for (size_t j = 0; j < n / 4; j++) E[j] = g_add(E[2 * j], E[2 * j + 1]);
    }
    for (int i = 1; i < ell; i++) {
        size_t half = n >> (i + 1); g256 q0 = {{0}}, q1 = {{0}}, r = I->rlk[i];
        for (size_t j = 0; j < half; j++) {
            g256 G0 = G[2 * j], G1 = G[2 * j + 1];
            q0 = g_add(q0, g_mul(E[j], G0)); q1 = g_add(q1, g_mul(E[j], G1));
            G[j] = g_add(G0, g_mul(r, g_add(G0, G1)));
        }
        I->lq[2 * i] = q0; I->lq[2 * i + 1] = q1;
        for (size_t j = 0; j < half / 2; j++) E[j] = g_add(E[2 * j], E[2 * j + 1]);
        if (half == 1) E[0] = G_ONE;
    }
    I->lfinal = G[0];
    /* ---------- (3) one-hot opening claims ra~(rho, v) ---------- */
    g256 *F = malloc(n * sizeof(g256));
    eq_table(F, I->rlk, ell);
    for (int v = 0; v < 16; v++) I->ra[v] = (g256){{0}};
    for (size_t x = 0; x < n; x++) I->ra[I->addr[x]] = g_add(I->ra[I->addr[x]], F[x]);
    free(F); free(E); free(A); free(B); free(C);
    I->mults = g256_mults - m0;
}

static void phex(const g256 *g) { printf("\""); for (int i = 3; i >= 0; i--) printf("%016llx", (unsigned long long)g->w[i]); printf("\""); }

typedef struct { int ell, reps; uint64_t seed; double best; long mults; } job_t;
static void *worker(void *p) {
    job_t *J = p; inst_t I; gen(&I, J->ell, J->seed, 0); J->best = 1e30;
    for (int r = 0; r < J->reps; r++) { double t = now(); prove(&I); t = now() - t; if (t < J->best) J->best = t; }
    J->mults = I.mults; return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) return 1;
    int ell = atoi(argv[2]);
    if (!strcmp(argv[1], "check")) {
        inst_t I; gen(&I, ell, 0x5eed + ell, argc > 3 ? atoi(argv[3]) : 0); prove(&I);
        printf("{\"ell\": %d, \"mults\": %ld, \"zq\": [", ell, I.mults);
        for (int i = 0; i < 3 * ell; i++) { if (i) printf(","); phex(&I.zq[i]); }
        printf("], \"zfinal\": ["); for (int i = 0; i < 3; i++) { if (i) printf(","); phex(&I.zfinal[i]); }
        printf("], \"lclaim\": "); phex(&I.lclaim); printf(", \"lq\": [");
        for (int i = 0; i < 2 * ell; i++) { if (i) printf(","); phex(&I.lq[i]); }
        printf("], \"lfinal\": "); phex(&I.lfinal); printf(", \"ra\": [");
        for (int v = 0; v < 16; v++) { if (v) printf(","); phex(&I.ra[v]); }
        printf("]}\n"); return 0;
    }
    int reps = atoi(argv[3]), th = argc > 4 ? atoi(argv[4]) : 1;
    /* single-thread multiply rate */
    g256 x = {{1, 2, 3, 4}}, y = {{5, 6, 7, 8}}; double t0 = now(); for (int i = 0; i < 2000000; i++) x = g_mul(x, y); double mul_ns = (now() - t0) / 2e6 * 1e9; if (x.w[0] == 42) printf(" ");
    job_t *J = calloc(th, sizeof(job_t)); pthread_t *P = calloc(th, sizeof(pthread_t));
    double t1 = now();
    for (int k = 0; k < th; k++) { J[k] = (job_t){ell, reps, 0x1234 + k, 0, 0}; pthread_create(&P[k], NULL, worker, &J[k]); }
    for (int k = 0; k < th; k++) pthread_join(P[k], NULL);
    double wall = now() - t1, sum_best = 0, worst = 0; for (int k = 0; k < th; k++) { sum_best += J[k].best; if (J[k].best > worst) worst = J[k].best; }
    size_t n = (size_t)1 << ell;
    /* mults_per_row: thread 0's own count (I.mults is a difference of a shared counter, so exact only when
       THREADS = 1; the checker pins it at THREADS = 1) */
    printf("{\"ell\": %d, \"rows\": %zu, \"threads\": %d, \"reps\": %d, \"mul_ns\": %.2f, \"best_proof_ms_mean\": %.4f, "
           "\"ns_per_row_one_core\": %.2f, \"aggregate_rows_per_s\": %.4e, \"wall_s\": %.3f, \"mults_per_row\": %.3f}\n",
           ell, n, th, reps, mul_ns, sum_best / th * 1e3, sum_best / th * 1e9 / n, (double)th * n / worst, wall,
           (double)J[0].mults / n);
    (void)x;
    return 0;
}
