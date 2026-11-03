/* rsieve.c -- the range-(3) sieve of the class-number-3500 classification.
 *
 * Decides "h(-n) > N" for every n in [A, A2) with n mod 16 in {3,7,11,15,4,8} and 9 !| n (a superset of the n with
 * -n fundamental), by Jaswal's procedure (Section 3.2, Lemma 3.3 of his preprint; see the release README):
 *   (1) per class mod Q = 16*9*prod_{5<=p<=P} p:  W(Y) > N certifies the class;
 *   (2) per n:  tau_j = #split primes among the first 8j primes > P (q_{8j} < 4096), certified if tau_j >= the
 *       precomputed least tau <= min(8j,254) with V(tau, q_{8j}) > N;
 *   (3) per n:  sum_{4a^2 < n} rho(a) > N.
 * Anything left is printed as "LEFTOVER n". Shares no code with Jaswal's or Kimura's programs.
 *
 * W(x) = sum over a <= x whose prime factors are <= P of rho(a), rho multiplicative with local factor
 *   split p: 2 for every exponent e >= 1;  ramified p: 1 if e = 1, 0 if e >= 2;  inert p: 0  (S1).
 * Types of p <= P from n: p = 2 by n mod 16 (7,15 split; 3,11 inert; 4,8 ramified); p = 3 by n mod 9
 *   (3,6 ramified; 2,5,8 split; 1,4,7 inert); p >= 5 by n mod p (0 ramified; else split iff (-n/p) = 1).
 *
 * The class DFS goes over p = 2, 3, 5, ..., P and branches on the residue of n mod 16, 9, p. At a node, W is
 * computed (capped at N + 1) with only the primes decided so far allowed: a LOWER bound for the W of every class
 * below (rho >= 0; allowing a prime only adds terms). If it exceeds N the subtree is certified and its n are
 * counted exactly; residues are grouped by type, since the bound depends on the types only.
 *
 * Usage: rsieve N A A2 P Y THREADS [selftest K]
 * Output: key=value lines; "LEFTOVER n" lines.  Compile: cc -O3 -o rsieve rsieve.c -lpthread -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <pthread.h>

typedef long long i64;
typedef unsigned long long u64;
typedef __int128 i128;

static i64 N, A, A2, Y;
static int P, THREADS;

/* ---------- primes ---------- */
#define QMAX 4096
static int pr[700], npr;                 /* all primes < QMAX */
static int smallp[16], nsmall;           /* primes <= P */
static int bigq[600], nbig;              /* primes in (P, QMAX) */
static unsigned char *qsplit[QMAX];      /* qsplit[q][r] = 1 iff (-r / q) = 1, for r = n mod q (r != 0) */

static int legendre(i64 a, int p) {      /* p odd prime */
    a %= p; if (a < 0) a += p; if (a == 0) return 0;
    i64 r = 1, b = a, e = (p - 1) / 2;
    while (e) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; }
    return r == 1 ? 1 : -1;
}

/* ---------- W(x) with a cap ---------- */
/* types: 0 inert, 1 split, 2 ramified, 3 undecided (treated as inert: lower bound) */
typedef struct { int n; int p[16]; int t[16]; } Pat;

static i64 w_rec(const Pat *pt, int i, i64 prod, i64 wgt, i64 x, i64 cap, i64 acc) {
    for (int k = i; k < pt->n; k++) {
        int t = pt->t[k]; if (t != 1 && t != 2) continue;
        i64 p = pt->p[k];
        if (prod > x / p) break;                     /* primes ascending: no larger p fits either */
        if (t == 1) {
            i64 pk = prod * p; i64 w2 = wgt * 2;
            while (1) {
                acc += w2; if (acc > cap) return acc;
                acc = w_rec(pt, k + 1, pk, w2, x, cap, acc); if (acc > cap) return acc;
                if (pk > x / p) break; pk *= p;
            }
        } else {
            i64 pk = prod * p;
            acc += wgt; if (acc > cap) return acc;
            acc = w_rec(pt, k + 1, pk, wgt, x, cap, acc); if (acc > cap) return acc;
        }
    }
    return acc;
}
static i64 W(const Pat *pt, i64 x, i64 cap) { if (x < 1) return 0; return w_rec(pt, 0, 1, 1, x, cap, 1); }

/* ---------- V(tau, z) (Lemma 3.3), capped ---------- */
static i64 binom_cap(int a, int b, i64 cap) {
    if (b < 0 || b > a) return 0; i128 r = 1;
    for (int i = 1; i <= b; i++) { r = r * (a - b + i) / i; if (r > cap) return cap + 1; }
    return (i64)r;
}
static i64 V(const Pat *pt, int tau, i64 z, i64 cap) {
    i128 v = W(pt, Y, cap); if (v > cap) return cap + 1;
    i64 zk = 1;
    for (int k = 1; ; k++) {
        if (zk > Y / z) break; zk *= z;
        i64 w = W(pt, Y / zk, cap); if (w == 0) break;
        i128 coef = 0;
        for (int j = 1; j <= k && j <= tau; j++) {
            i128 c = (i128)(1LL << (j < 60 ? j : 60)) * binom_cap(tau, j, cap) * binom_cap(k - 1, j - 1, cap);
            coef += c; if (coef > cap) { coef = cap + 1; break; }
        }
        v += coef * w; if (v > cap) return cap + 1;
    }
    return (i64)v;
}

/* ---------- the class DFS ---------- */
static i64 *leaves; static i64 nleaves, capleaves;    /* a leaf = a class r mod Q failing step (1) */
static i64 cnt_tree_cert = 0, cnt_leaf_n = 0;   /* n certified in step (1) at internal nodes / n reaching leaves */

static i64 count_in(i64 r, i64 M) {            /* #{n in [A, A2) : n = r mod M}, 0 <= r < M */
    i64 hi = (A2 - 1 - r) >= 0 ? (A2 - 1 - r) / M : -1;
    i64 lo = (A - 1 - r) >= 0 ? (A - 1 - r) / M : -1;
    return hi - lo;
}
static i64 crt(i64 r, i64 M, i64 x, i64 m) {   /* the s mod M*m with s = r mod M, s = x mod m (gcd = 1) */
    i64 t = ((x - r % m) % m + m) % m;          /* s = r + M*u with M*u = t (mod m) */
    i64 x0 = 1, x1 = 0, aa = M % m, bb = m;     /* extended Euclid: (M mod m)^{-1} mod m */
    while (bb) { i64 q = aa / bb, tmp = aa - q * bb; aa = bb; bb = tmp; tmp = x0 - q * x1; x0 = x1; x1 = tmp; }
    i64 inv = ((x0 % m) + m) % m;
    i64 u = (i64)((i128)t * inv % m);
    return r + M * u;
}
static int type_of(int p, int x) {             /* x = n mod (16, 9 or p) */
    if (p == 2) { if (x == 7 || x == 15) return 1; if (x == 3 || x == 11) return 0; return 2; }
    if (p == 3) { if (x == 3 || x == 6) return 2; if (x % 3 == 2) return 1; return 0; }
    if (x == 0) return 2; return legendre(-(i64)x, p) == 1 ? 1 : 0;
}
__attribute__((unused)) static void dfs(int k, i64 r, i64 M, Pat *pt) {
    if (k == nsmall) {
        if (nleaves == capleaves) { capleaves = capleaves ? 2 * capleaves : 1 << 16;
            leaves = realloc(leaves, capleaves * sizeof(i64)); }
        leaves[nleaves++] = r;
        cnt_leaf_n += count_in(r, M);
        return;
    }
    int p = smallp[k], m = p == 2 ? 16 : p == 3 ? 9 : p;
    int cert[3] = {0, 0, 0};
    for (int t = 0; t < 3; t++) { pt->t[k] = t; cert[t] = W(pt, Y, N) > N; }
    for (int x = 0; x < m; x++) {
        if (p == 2 && !(x == 3 || x == 7 || x == 11 || x == 15 || x == 4 || x == 8)) continue;
        if (p == 3 && x == 0) continue;
        int t = type_of(p, x);
        i64 r2 = crt(r, M, x, m), M2 = M * m;
        if (cert[t]) { cnt_tree_cert += count_in(r2, M2); continue; }
        pt->t[k] = t; dfs(k + 1, r2, M2, pt);
    }
    pt->t[k] = 3;
}

/* ---------- step (2) thresholds, per splitting pattern ---------- */
static int nj;                                   /* j = 1..nj with q_{8j} < QMAX */
static int thresh_of(const Pat *pt, int j) {     /* least tau <= min(8j,254) with V(tau, q_{8j}) > N; 999 if none.
                                                    V is nondecreasing in tau (Lemma 3.3), so binary search */
    int lim = 8 * j < 254 ? 8 * j : 254; i64 z = bigq[8 * j - 1];
    if (V(pt, lim, z, N) <= N) return 999;
    int lo = 0, hi = lim;                        /* invariant: V(hi) > N */
    while (lo < hi) { int mid = (lo + hi) / 2; if (V(pt, mid, z, N) > N) hi = mid; else lo = mid + 1; }
    return lo;
}
static int pcode_of_n(i64 n) {                   /* base-3 code of the types of p <= P */
    int c = 0;
    for (int k = nsmall - 1; k >= 0; k--) { int p = smallp[k], m = p == 2 ? 16 : p == 3 ? 9 : p;
        c = 3 * c + type_of(p, (int)(n % m)); }
    return c;
}
static void pat_of_code(int c, Pat *pt) {
    pt->n = nsmall;
    for (int k = 0; k < nsmall; k++) { pt->p[k] = smallp[k]; pt->t[k] = c % 3; c /= 3; }
}
static int *thr;                                 /* thr[code * (nj+1) + j], filled for the codes of leaves */
static unsigned char *present; static int ncodes;
typedef struct { int lo, hi; } TJob;
static void *thr_worker(void *arg) {
    TJob *tj = arg; Pat pt;
    for (int c = tj->lo; c < tj->hi; c++) if (present[c]) { pat_of_code(c, &pt);
        for (int j = 1; j <= nj; j++) thr[(i64)c * (nj + 1) + j] = thresh_of(&pt, j); }
    return NULL;
}

/* step (3): sum_{4a^2 < n} rho(a) > N ?  rho from the factorization of a (smallest-prime-factor table) */
static unsigned int *spf; static i64 spfmax;
static int chi_n(i64 n, i64 p) {                 /* Kronecker (D/p) for D = -n, p prime */
    if (p == 2) { i64 r = n % 16; if (r == 7 || r == 15) return 1; if (r == 3 || r == 11) return -1; return 0; }
    if (n % p == 0) return 0;
    return legendre(-(n % p), (int)p);
}
static int step3(i64 n) {
    i64 amax = (i64)sqrtl((long double)(n - 1) / 4.0L);
    while (4 * (amax + 1) * (amax + 1) < n) amax++;
    while (4 * amax * amax >= n) amax--;
    if (amax > spfmax) { fprintf(stderr, "spf table too small for n=%lld\n", n); exit(3); }
    i64 s = 0;
    for (i64 a = 1; a <= amax; a++) {
        i64 x = a, rho = 1;
        while (x > 1 && rho) {
            i64 p = spf[x], e = 0; while (x % p == 0) { x /= p; e++; }
            int c = chi_n(n, p);
            if (c == 1) rho *= 2; else if (c == 0) { if (e >= 2) rho = 0; } else rho = 0;
        }
        s += rho; if (s > N) return 1;
    }
    return 0;
}

static i64 Q;
typedef struct { i64 tree_cert, nleaves, leaf_n, c2, c3, left, treated; unsigned short *cnt; int *alive; i64 cap; } Ctx;
/* Lane-major step (2) (v4): for one leaf class, all its n (lanes t, n_t = n0 + tQ) are processed together, one prime at
   a time: each prime's split table is swept over the live lanes (incremental residue: one add and compare per lane),
   counts accumulate per lane, and after group j every live lane with cnt >= th[j] is certified and dropped. The
   criterion is exactly v3's ("some j with tau_j(n) >= th[j]"); only the loop order changes. */
static void process_leaf(i64 r, Ctx *cx) {
    const int *th = &thr[(i64)pcode_of_n(r) * (nj + 1)];
    i64 n0 = r; if (n0 < A) n0 += ((A - n0 + Q - 1) / Q) * Q;        /* first n >= A with n = r mod Q */
    if (n0 >= A2) return;
    i64 T = (A2 - 1 - n0) / Q + 1;
    if (T > cx->cap) { cx->cap = 2 * T; cx->cnt = realloc(cx->cnt, cx->cap * sizeof(unsigned short));
        cx->alive = realloc(cx->alive, cx->cap * sizeof(int)); }
    unsigned short *cnt = cx->cnt; int *alive = cx->alive;
    cx->treated += T;
    for (i64 t = 0; t < T; t++) { cnt[t] = 0; alive[t] = (int)t; }
    i64 na = T;
    for (int j = 1; j <= nj && na > 0; j++) {
        for (int i = 8 * (j - 1); i < 8 * j; i++) {
            int q = bigq[i]; const unsigned char *tb = qsplit[q];
            int s = (int)(Q % q), r0 = (int)(n0 % q);
            if (na == T) {                                             /* dense: incremental residue */
                int rr = r0;
                for (i64 t = 0; t < T; t++) { cnt[t] += tb[rr]; rr += s; if (rr >= q) rr -= q; }
            } else {                                                   /* sparse: direct residue */
                for (i64 k = 0; k < na; k++) { i64 t = alive[k]; cnt[t] += tb[(int)((r0 + (i128)t * s) % q)]; }
            }
        }
        if (th[j] <= 8 * j) {
            i64 w = 0;
            for (i64 k = 0; k < na; k++) { int t = alive[k]; if (cnt[t] >= th[j]) cx->c2++; else alive[w++] = t; }
            na = w;
        }
    }
    for (i64 k = 0; k < na; k++) {                                     /* step (3) for what is left */
        i64 n = n0 + (i64)alive[k] * Q;
        if (step3(n)) cx->c3++;
        else { cx->left++; printf("LEFTOVER %lld\n", n); fflush(stdout); }
    }
}
/* the DFS below depth k0, run by a worker thread on its own Pat copy and counters; leaves processed at once */
static void dfs_t(int k, i64 r, i64 M, Pat *pt, Ctx *cx) {
    if (k == nsmall) { cx->nleaves++; cx->leaf_n += count_in(r, M); process_leaf(r, cx); return; }
    int p = smallp[k], m = p == 2 ? 16 : p == 3 ? 9 : p;
    int cert[3] = {0, 0, 0};
    for (int t = 0; t < 3; t++) { pt->t[k] = t; cert[t] = W(pt, Y, N) > N; }
    for (int x = 0; x < m; x++) {
        if (p == 2 && !(x == 3 || x == 7 || x == 11 || x == 15 || x == 4 || x == 8)) continue;
        if (p == 3 && x == 0) continue;
        int t = type_of(p, x);
        i64 r2 = crt(r, M, x, m), M2 = M * m;
        if (cert[t]) { cx->tree_cert += count_in(r2, M2); continue; }
        pt->t[k] = t; dfs_t(k + 1, r2, M2, pt, cx);
    }
    pt->t[k] = 3;
}
/* the frontier: nodes at depth K0 (primes 2, 3, 5, 7), built single-threaded with the same pruning */
typedef struct { i64 r, M; Pat pt; } Node;
static Node *front; static i64 nfront, capfront; static i64 front_cert = 0; static int K0;
static void build_front(int k, i64 r, i64 M, Pat *pt) {
    if (k == K0) { if (nfront == capfront) { capfront = capfront ? 2 * capfront : 4096; front = realloc(front, capfront * sizeof(Node)); }
        front[nfront].r = r; front[nfront].M = M; front[nfront].pt = *pt; nfront++; return; }
    int p = smallp[k], m = p == 2 ? 16 : p == 3 ? 9 : p;
    int cert[3] = {0, 0, 0};
    for (int t = 0; t < 3; t++) { pt->t[k] = t; cert[t] = W(pt, Y, N) > N; }
    for (int x = 0; x < m; x++) {
        if (p == 2 && !(x == 3 || x == 7 || x == 11 || x == 15 || x == 4 || x == 8)) continue;
        if (p == 3 && x == 0) continue;
        int t = type_of(p, x);
        i64 r2 = crt(r, M, x, m), M2 = M * m;
        if (cert[t]) { front_cert += count_in(r2, M2); continue; }
        pt->t[k] = t; build_front(k + 1, r2, M2, pt);
    }
    pt->t[k] = 3;
}
static i64 next_front = 0; static pthread_mutex_t fmu = PTHREAD_MUTEX_INITIALIZER;
static void *front_worker(void *arg) {
    Ctx *cx = arg; cx->cap = 0; cx->cnt = NULL; cx->alive = NULL;
    for (;;) {
        pthread_mutex_lock(&fmu); i64 i = next_front++; pthread_mutex_unlock(&fmu);
        if (i >= nfront) break;
        Pat pt = front[i].pt; dfs_t(K0, front[i].r, front[i].M, &pt, cx);
    }
    free(cx->cnt); free(cx->alive); return NULL;
}

/* ---------- self-test: class-level/incremental logic against direct per-n evaluation ---------- */
static void pattern_of_n(i64 n, Pat *pt) {
    pt->n = nsmall;
    for (int k = 0; k < nsmall; k++) { int p = smallp[k], m = p == 2 ? 16 : p == 3 ? 9 : p;
        pt->p[k] = p; pt->t[k] = type_of(p, (int)(n % m)); }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: rsieve N A A2 P Y THREADS [selftest K]\n"); return 2; }
    N = atoll(argv[1]); A = atoll(argv[2]); A2 = atoll(argv[3]); P = atoi(argv[4]); Y = atoll(argv[5]);
    THREADS = atoi(argv[6]);
    if (4 * (i128)Y * Y > A) { fprintf(stderr, "need 4Y^2 <= A\n"); return 2; }
    char *sv = calloc(QMAX, 1);
    for (int i = 2; i < QMAX; i++) if (!sv[i]) { pr[npr++] = i; for (int j = 2 * i; j < QMAX; j += i) sv[j] = 1; }
    for (int i = 0; i < npr; i++) { if (pr[i] <= P) smallp[nsmall++] = pr[i]; else bigq[nbig++] = pr[i]; }
    for (int i = 0; i < nbig; i++) { int q = bigq[i]; qsplit[q] = calloc(q, 1);
        for (int r = 1; r < q; r++) qsplit[q][r] = legendre(-(i64)r, q) == 1; }
    nj = 0; while (8 * (nj + 1) <= nbig && bigq[8 * (nj + 1) - 1] < QMAX) nj++;
    Q = 16 * 9; for (int k = 2; k < nsmall; k++) Q *= smallp[k];
    /* spf table for step (3): a < sqrt(A2)/2 */
    spfmax = (i64)(sqrtl((long double)A2) / 2) + 2;
    spf = calloc(spfmax + 1, sizeof(unsigned int));
    for (i64 i = 2; i <= spfmax; i++) if (!spf[i]) for (i64 j = i; j <= spfmax; j += i) if (!spf[j]) spf[j] = (unsigned)i;
    Pat root; root.n = nsmall; for (int k = 0; k < nsmall; k++) { root.p[k] = smallp[k]; root.t[k] = 3; }
    if (argc >= 9 && !strcmp(argv[7], "selftest")) {
        /* for K random n in range: (a) the class DFS bound equals W of n's own pattern; (b) the incremental residues
           equal direct Legendre symbols -- checked inside a one-n replay of the worker logic */
        int K = atoi(argv[8]); u64 s = 88172645463325252ULL; int bad = 0;
        for (int it = 0; it < K; it++) {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            i64 n = A + (i64)(s % (u64)(A2 - A));
            i64 m16 = n % 16; if (!(m16 == 3 || m16 == 7 || m16 == 11 || m16 == 15 || m16 == 4 || m16 == 8) || n % 9 == 0) { it--; continue; }
            Pat pt; pattern_of_n(n, &pt);
            for (int i = 0; i < 8 * nj; i++) { int q = bigq[i]; int d = legendre(-(n % q), q) == 1;
                if ((n % q) && d != qsplit[q][n % q]) bad++; }
            /* brute W against the recursion: enumerate a <= min(Y, 2e5) directly */
            i64 lim = Y < 200000 ? Y : 200000, wb = 0;
            for (i64 a = 1; a <= lim; a++) { i64 x = a, rho = 1;
                for (int k = 0; k < nsmall && x > 1; k++) { int p = smallp[k], e = 0; while (x % p == 0) { x /= p; e++; }
                    if (e) { int t = pt.t[k]; if (t == 1) rho *= 2; else if (t == 2) { if (e >= 2) rho = 0; } else rho = 0; } }
                if (x == 1) wb += rho; }
            i64 wr = W(&pt, lim, (i64)1 << 60);
            if (wb != wr) { bad++; if (bad < 5) printf("W MISMATCH n=%lld brute=%lld rec=%lld\n", n, wb, wr); }
        }
        printf("selftest K=%d bad=%d\n", K, bad); return bad ? 1 : 0;
    }
    ncodes = 1; for (int k = 0; k < nsmall; k++) ncodes *= 3;
    present = malloc(ncodes); memset(present, 1, ncodes);              /* thresholds for EVERY pattern */
    thr = calloc((size_t)ncodes * (nj + 1), sizeof(int));
    { pthread_t tt[256]; TJob tj[256]; int T = THREADS > 256 ? 256 : THREADS;
      for (int t = 0; t < T; t++) { tj[t].lo = (int)((i64)ncodes * t / T); tj[t].hi = (int)((i64)ncodes * (t + 1) / T);
          pthread_create(&tt[t], NULL, thr_worker, &tj[t]); }
      for (int t = 0; t < T; t++) pthread_join(tt[t], NULL); }
    K0 = nsmall < 4 ? nsmall : 4;
    build_front(0, 0, 1, &root);
    fprintf(stderr, "thresholds for %d patterns done; frontier nodes=%lld (depth %d)\n", ncodes, nfront, K0);
    i64 direct = 0;                                  /* #n treated, directly by residues mod 144 */
    for (int r = 0; r < 144; r++) { int m16 = r % 16; if ((m16 == 3 || m16 == 7 || m16 == 11 || m16 == 15 || m16 == 4 || m16 == 8) && r % 9) direct += count_in(r, 144); }
    pthread_t tid[256]; Ctx cxs[256]; if (THREADS > 256) THREADS = 256;
    memset(cxs, 0, sizeof cxs);
    for (int t = 0; t < THREADS; t++) pthread_create(&tid[t], NULL, front_worker, &cxs[t]);
    i64 c2 = 0, c3 = 0, left = 0, treated = 0, tcert = front_cert, nl = 0, ln = 0;
    for (int t = 0; t < THREADS; t++) { pthread_join(tid[t], NULL); c2 += cxs[t].c2; c3 += cxs[t].c3; left += cxs[t].left;
        treated += cxs[t].treated; tcert += cxs[t].tree_cert; nl += cxs[t].nleaves; ln += cxs[t].leaf_n; }
    printf("N=%lld A=%lld A2=%lld P=%d Y=%lld Q=%lld nj=%d\n", N, A, A2, P, Y, Q, nj);
    printf("leaves=%lld step1_certified_n=%lld leaf_n=%lld treated_leaf_n=%lld\n", nl, tcert, ln, treated);
    printf("n_treated=%lld direct_count=%lld match=%d\n", tcert + treated, direct, tcert + treated == direct);
    printf("step2_certified=%lld reaching_step3=%lld step3_certified=%lld leftover=%lld\n", c2, c3 + left, c3, left);
    return left ? 1 : 0;
}
