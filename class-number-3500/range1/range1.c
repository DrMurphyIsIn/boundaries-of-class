/* range1.c -- range (1) of the class-number-3500 classification, PARI-independent.
 *
 * For every n in [LO, HI) with -n a fundamental discriminant (odd part of n squarefree, and n = 3 mod 4 or
 * n = 4, 8 mod 16), decide h(-n) <= N and, if so, compute h(-n) exactly, by Jaswal's procedure (Lemmas 3.1-3.2
 * of his preprint on the classification with h <= 3000; see the release README for the full citation):
 *   class-order test: omega = omega(n); M = N if omega = 1 else floor(2N / 2^{omega-1}); for the first four
 *       primes p < 2000 with chi(p) = 1, the class g_p of (p, b_p, (b_p^2 + n)/4p): if baby-step/giant-step
 *       shows g_p^k != 1 for 1 <= k <= M, then h > N (Lemma 3.2).
 *   exact count (otherwise): h = #reduced forms = sum_{4a^2 < n} rho(a) + #{reduced (a,b,c) with 4a^2 >= n}
 *       (Lemma 3.1).
 * Output: "n h" for every fundamental n with h <= N (one file per segment), and a summary line per segment:
 *   "SEG lo hi fundamental decided_by_class_order exact_counted recorded sum_h_exact".
 * Usage: range1 N LO HI SEG THREADS OUTDIR            (segments [LO + k*SEG, ...))
 *        range1 test K LO HI                          (unit tests: BSGS vs brute orders; exact h vs brute forms)
 * Compile: cc -O3 -o range1 range1.c -lpthread -lm
 *
 * This implementation shares no code with Jaswal's or Kimura's programs (see the release README).
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

static i64 N;

/* ---------- primes and tables ---------- */
#define PS 2000
static int sprimes[400], nsp;                   /* primes < 2000 */
static unsigned char *qres[PS];                 /* qres[p][r]: (r/p) = 1 */
static int *sqrtmod[PS];                        /* sqrtmod[p][r] = some s with s^2 = r mod p, or -1 */
static int *bigp; static int nbigp;             /* primes <= sqrt(HI) for the segmented sieve and chi */

static int legendre(i64 a, int p) {
    a %= p; if (a < 0) a += p; if (a == 0) return 0;
    i64 r = 1, b = a, e = (p - 1) / 2;
    while (e) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; }
    return r == 1 ? 1 : -1;
}
static int chi(i64 n, int p) {                  /* Kronecker (D/p), D = -n */
    if (p == 2) { int r = (int)(n % 8); if (n % 2 == 0) return 0; return r == 7 ? 1 : -1; }
    if (p < PS) { int r = (int)(n % p); if (r == 0) return 0; return qres[p][(p - r) % p] ? 1 : -1; }
    return legendre(-n, p);
}

/* ---------- forms: (a, b, c), b^2 - 4ac = D < 0, positive definite ---------- */
typedef struct { i64 a, b, c; } Form;

static void normalize_reduce(Form *f, i64 D) {
    for (;;) {
        i64 a = f->a, twoa = 2 * a;
        i64 b = f->b % twoa;                      /* b into (-a, a], same class mod 2a */
        if (b > a) b -= twoa;
        if (b <= -a) b += twoa;
        f->b = b; f->c = (i64)(((i128)b * b - D) / (4 * (i128)a));
        if (f->a > f->c) { i64 t = f->a; f->a = f->c; f->c = t; f->b = -f->b; continue; }
        if (f->a == f->c && f->b < 0) f->b = -f->b;   /* canonical: b >= 0 when a = c (|b| = a gives b = a already) */
        return;
    }
}
static i64 egcd(i64 a, i64 b, i64 *x, i64 *y) {  /* a*x + b*y = g >= 0 */
    i64 x0 = 1, y0 = 0, x1 = 0, y1 = 1;
    while (b) { i64 q = a / b, t = a - q * b; a = b; b = t;
        t = x0 - q * x1; x0 = x1; x1 = t; t = y0 - q * y1; y0 = y1; y1 = t; }
    if (a < 0) { a = -a; x0 = -x0; y0 = -y0; }
    *x = x0; *y = y0; return a;
}
/* composition (Dirichlet / Cohen 5.4.7 in the "three-gcd" form):
   beta = (b1+b2)/2; g = gcd(a1, a2, beta) = u a1 + v a2 + w beta;
   A = a1 a2 / g^2;  B = (u a1 b2 + v a2 b1 + w (b1 b2 + D)/2) / g  mod 2A;  C = (B^2 - D)/4A; then reduce. */
static Form compose(Form f1, Form f2, i64 D) {
    i64 beta = (f1.b + f2.b) / 2;
    i64 x, y; i64 d1 = egcd(f1.a, f2.a, &x, &y);
    i64 x2, y2; i64 g = egcd(d1, beta, &x2, &y2);
    i128 u = (i128)x2 * x, v = (i128)x2 * y, w = y2;
    i128 A = (i128)(f1.a / g) * (f2.a / g);
    i128 num = u * f1.a * f2.b + v * f2.a * f1.b + w * (((i128)f1.b * f2.b + D) / 2);
    i128 B = num / g;
    i128 twoA = 2 * A;
    B %= twoA; if (B < 0) B += twoA;
    Form r; r.a = (i64)A; r.b = (i64)B; r.c = 0;
    if (A > (i128)9e18 || B > (i128)9e18) { fprintf(stderr, "overflow in compose\n"); exit(4); }
    normalize_reduce(&r, D);
    return r;
}
static int is_id(Form f, i64 D) { return f.a == 1 && f.b == (D & 1 ? 1 : 0); }
static int same(Form f, Form g) { return f.a == g.a && f.b == g.b; }

/* S2: does g have g^k != 1 for 1 <= k <= M ?  (baby m = ceil(sqrt M), giant t = ceil(M/m)) */
static int order_exceeds(Form g, i64 M, i64 D) {
    i64 m = (i64)sqrt((double)M); if (m < 1) m = 1; while (m * m < M) m++;      /* m = ceil(sqrt(M)) */
    i64 t = (M + m - 1) / m;
    Form baby[1024]; if (m > 1024) { fprintf(stderr, "m too big\n"); exit(5); }
    Form idf; idf.a = 1; idf.b = D & 1 ? 1 : 0; idf.c = (idf.b * idf.b - D) / 4;
    baby[0] = idf; Form cur = idf;
    for (i64 j = 1; j < m; j++) { cur = compose(cur, g, D); if (is_id(cur, D)) return 0; baby[j] = cur; }
    Form G = compose(cur, g, D);                  /* g^m */
    Form gi = G;
    for (i64 i = 1; i <= t; i++) {
        for (i64 j = 0; j < m; j++) if (same(gi, baby[j])) return 0;
        gi = compose(gi, G, D);
    }
    return 1;
}

/* S1 exact: h(-n) as the number of reduced forms.
   rho(a) (S1 local factors) for a <= amax = floor(sqrt(n/3)) by a multiplicative sieve; forms with 4a^2 < n are counted
   by rho(a); for the boundary a (4a^2 >= n, rho(a) > 0) the rho(a) roots b mod 2a of b^2 = D (mod 4a) are built by CRT
   and kept iff c = (b^2 + n)/4a >= a, with b >= 0 when c = a. */
static i64 modpow(i64 b, i64 e, i64 m) { i128 r = 1, x = b % m; if (x < 0) x += m; while (e) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; } return (i64)r; }
static i64 sqrt_mod_p(i64 r, i64 p) {         /* Tonelli-Shanks, r a nonzero QR mod odd prime p */
    r %= p; if (r < 0) r += p;
    if (p < PS) return sqrtmod[p][r];
    i64 q = p - 1, sexp = 0; while (!(q & 1)) { q >>= 1; sexp++; }
    i64 z = 2; while (modpow(z, (p - 1) / 2, p) != p - 1) z++;
    i64 m = sexp, c = modpow(z, q, p), t = modpow(r, q, p), x = modpow(r, (q + 1) / 2, p);
    while (t != 1) { i64 i = 0, tt = t; while (tt != 1) { tt = (i64)((i128)tt * tt % p); i++; }
        i64 bb = c; for (i64 j = 0; j < m - i - 1; j++) bb = (i64)((i128)bb * bb % p);
        m = i; c = (i64)((i128)bb * bb % p); t = (i64)((i128)t * c % p); x = (i64)((i128)x * bb % p); }
    return x;
}
static int roots_mod_2a(i64 a, i64 D, const unsigned int *spf, i64 *out) {  /* returns #roots b mod 2a */
    i64 cur[4096]; int nc = 1; i64 mod = 1; cur[0] = 0;
    i64 x = a; int e2 = 0; while (!(x & 1)) { x >>= 1; e2++; }
    /* 2-part: x2 mod 2^{e2+1} with x2^2 = D mod 2^{e2+2} */
    { i64 m2 = (i64)1 << (e2 + 1), M2 = m2 * 2; i64 loc[8]; int nl = 0;
      for (i64 t = 0; t < m2 && nl < 8; t++) { i128 v = ((i128)t * t - D) % M2; if (v == 0) loc[nl++] = t; }
      if (nl == 0) return 0;
      int nn = 0; i64 nw[4096];
      for (int i = 0; i < nc; i++) for (int j = 0; j < nl; j++) nw[nn++] = loc[j];
      for (int i = 0; i < nn; i++) cur[i] = nw[i]; nc = nn; mod = m2; }
    while (x > 1) {
        i64 p = spf[x]; int k = 0; i64 pk = 1; while (x % p == 0) { x /= p; k++; pk *= p; }
        i64 loc[2]; int nl = 0;
        if ((-D) % p == 0) { if (k >= 2) return 0; loc[nl++] = 0; }
        else {
            if (legendre(D, (int)p) != 1) return 0;
            i64 r0 = sqrt_mod_p(D, p), r = r0, pj = p;
            for (int j = 1; j < k; j++) {             /* Hensel: r <- r - (r^2 - D) / (2r) mod p^{j+1} */
                i64 pj1 = pj * p; i128 f = ((i128)r * r - D) % pj1; if (f < 0) f += pj1;
                i64 inv = modpow(2 * r % pj1, pj1 / p * (p - 1) - 1, pj1);   /* phi(p^{j+1}) - 1 */
                r = (i64)(((i128)r - f * inv % pj1 + pj1) % pj1); pj = pj1; }
            loc[nl++] = r; loc[nl++] = (pk - r) % pk;
        }
        /* CRT: combine cur (mod `mod`) with loc (mod pk) */
        i64 xi, yi; egcd(mod % pk, pk, &xi, &yi); i64 inv = ((xi % pk) + pk) % pk;
        int nn = 0; static __thread i64 nw[4096];
        for (int i = 0; i < nc; i++) for (int j = 0; j < nl; j++) {
            i64 t = ((loc[j] - cur[i] % pk) % pk + pk) % pk; i64 u = (i64)((i128)t * inv % pk);
            nw[nn++] = cur[i] + mod * u; }
        for (int i = 0; i < nn; i++) cur[i] = nw[i]; nc = nn; mod *= pk;
    }
    for (int i = 0; i < nc; i++) out[i] = cur[i];
    return nc;
}
static unsigned int *SPF; static i64 SPFMAX;
static i64 hexact(i64 n, const int *primes, int np) {
    i64 D = -n;
    i64 amax = (i64)sqrtl((long double)n / 3.0L); while (3 * (amax + 1) * (amax + 1) <= n) amax++;
    while (3 * amax * amax > n) amax--;
    i64 a2 = (i64)sqrtl((long double)(n - 1) / 4.0L); while (4 * (a2 + 1) * (a2 + 1) < n) a2++;
    while (a2 > 0 && 4 * a2 * a2 >= n) a2--;    /* a <= a2 <=> 4a^2 < n */
    i64 L = amax + 1; int *rho = malloc(sizeof(int) * L);
    for (i64 a = 0; a < L; a++) rho[a] = 1;
    for (int k = 0; k < np && primes[k] <= amax; k++) {
        int p = primes[k]; int c = chi(n, p); int f1, fe;
        if (p == 2) { if (n % 2 == 1) { f1 = (n % 8 == 7) ? 2 : 0; fe = f1; } else { f1 = 1; fe = 0; } }
        else if (c == 0) { f1 = 1; fe = 0; } else { f1 = 1 + c; fe = 1 + c; }
        for (i64 a = p; a < L; a += p) rho[a] *= f1;
        if (fe != f1) { i64 pp = (i64)p * p; for (i64 a = pp; a < L; a += pp) rho[a] = 0; }
    }
    i64 h = 0; for (i64 a = 1; a <= a2; a++) h += rho[a];
    i64 roots[4096];
    for (i64 a = a2 + 1; a <= amax; a++) {
        if (!rho[a]) continue;
        int nr = roots_mod_2a(a, D, SPF, roots);
        if (nr != rho[a]) { fprintf(stderr, "ROOT COUNT MISMATCH n=%lld a=%lld nr=%d rho=%d\n", n, a, nr, rho[a]); exit(6); }
        for (int i = 0; i < nr; i++) {
            i64 b = roots[i] % (2 * a); if (b > a) b -= 2 * a; if (b <= -a) b += 2 * a;
            i128 num = (i128)b * b - D; i64 c = (i64)(num / (4 * a));
            if (c < a) continue; if (c == a && b < 0) continue; h++;
        }
    }
    free(rho);
    return h;
}
/* ---------- segmented processing ---------- */
static i64 LO, HI, SEG; static int THREADS; static char OUTDIR[1024];
static i64 nseg; static i64 nextseg = 0; static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;

static void do_segment(i64 lo, i64 hi) {
    i64 S = hi - lo;
    unsigned char *bad = calloc(S, 1); unsigned char *om = calloc(S, 1); u64 *prod = malloc(sizeof(u64) * S);
    for (i64 i = 0; i < S; i++) prod[i] = 1;
    for (int k = 0; k < nbigp; k++) {
        i64 p = bigp[k]; if (p * p > hi) break;
        i64 st = ((lo + p - 1) / p) * p;
        for (i64 x = st; x < hi; x += p) { i64 i = x - lo; om[i]++; prod[i] *= (u64)p; }
        if (p > 2) { i64 pp = p * p; i64 s2 = ((lo + pp - 1) / pp) * pp; for (i64 x = s2; x < hi; x += pp) bad[x - lo] = 1; }
    }
    char fn[1200]; snprintf(fn, sizeof fn, "%s/r%012lld.txt.part", OUTDIR, lo);
    FILE *fo = fopen(fn, "w");
    i64 fund = 0, dec = 0, ex = 0, rec = 0, sumh = 0;
    for (i64 n = (lo < 3 ? 3 : lo); n < hi; n++) {
        i64 i = n - lo; int m16 = (int)(n % 16);
        if (!((n % 4) == 3 || m16 == 4 || m16 == 8)) continue;
        if (bad[i]) continue;
        /* the odd part must be squarefree: for n = 4m (m = 1,2 mod 4) 2^2 or 2^3 divides n exactly, fine */
        fund++;
        int omega = om[i]; u64 pr = prod[i]; u64 oddn = (u64)n; while (!(oddn & 1)) oddn >>= 1;
        { u64 pr_odd = pr; while (!(pr_odd & 1)) pr_odd >>= 1; if (pr_odd < oddn) omega++; }   /* one prime > sqrt */
        i64 D = -n;
        i64 M = (omega <= 1) ? N : (2 * N) >> (omega - 1);
        int decided = 0;
        if (M >= 1) {
            int tried = 0;
            for (int k = 0; k < nsp && tried < 4; k++) {
                int p = sprimes[k]; if (chi(n, p) != 1) continue;
                tried++;
                i64 b;
                if (p == 2) b = 1;
                else { int r = (int)(((D % p) + p) % p); b = sqrtmod[p][r]; if (((b - D) & 1) != 0) b = p - b; }
                Form g; g.a = p; g.b = b; g.c = (i64)(((i128)b * b - D) / (4 * p));
                normalize_reduce(&g, D);
                if (order_exceeds(g, M, D)) { decided = 1; break; }
            }
        }
        if (decided) { dec++; continue; }
        ex++;
        i64 h = hexact(n, bigp, nbigp);
        sumh += h;
        if (h <= N) { rec++; fprintf(fo, "%lld %lld\n", n, h); }
    }
    fclose(fo);
    char fn2[1200]; snprintf(fn2, sizeof fn2, "%s/r%012lld.txt", OUTDIR, lo); rename(fn, fn2);
    snprintf(fn, sizeof fn, "%s/r%012lld.sum", OUTDIR, lo);
    FILE *fs = fopen(fn, "w");
    fprintf(fs, "SEG %lld %lld %lld %lld %lld %lld %lld\n", lo, hi, fund, dec, ex, rec, sumh); fclose(fs);
    free(bad); free(om); free(prod);
}
static void *seg_worker(void *arg) {
    (void)arg;
    for (;;) {
        pthread_mutex_lock(&mu); i64 k = nextseg++; pthread_mutex_unlock(&mu);
        if (k >= nseg) break;
        i64 lo = LO + k * SEG, hi = lo + SEG; if (hi > HI) hi = HI;
        char fn[1200]; snprintf(fn, sizeof fn, "%s/r%012lld.sum", OUTDIR, lo);
        FILE *t = fopen(fn, "r"); if (t) { fclose(t); continue; }     /* resumable */
        do_segment(lo, hi);
    }
    return NULL;
}

static void init_tables(i64 hi) {
    char *sv = calloc(PS, 1);
    for (int i = 2; i < PS; i++) if (!sv[i]) { sprimes[nsp++] = i; for (int j = 2 * i; j < PS; j += i) sv[j] = 1; }
    for (int k = 0; k < nsp; k++) { int p = sprimes[k]; qres[p] = calloc(p, 1); sqrtmod[p] = malloc(sizeof(int) * p);
        for (int r = 0; r < p; r++) sqrtmod[p][r] = -1;
        for (int s = 0; s < p; s++) { int r = (int)((i64)s * s % p); if (r) qres[p][r] = 1; if (sqrtmod[p][r] < 0) sqrtmod[p][r] = s; } }
    i64 lim = (i64)sqrtl((long double)hi) + 2;
    SPFMAX = lim; SPF = calloc(SPFMAX + 1, sizeof(unsigned int));
    for (i64 i = 2; i <= SPFMAX; i++) if (!SPF[i]) for (i64 j = i; j <= SPFMAX; j += i) if (!SPF[j]) SPF[j] = (unsigned)i;
    char *s2 = calloc(lim + 1, 1); bigp = malloc(sizeof(int) * (lim / 2 + 10)); nbigp = 0;
    for (i64 i = 2; i <= lim; i++) if (!s2[i]) { bigp[nbigp++] = (int)i; for (i64 j = i * i; j <= lim; j += i) s2[j] = 1; }
}

/* ---------- unit tests ---------- */
static i64 brute_h(i64 n) {                    /* all reduced forms, directly */
    i64 D = -n, h = 0;
    for (i64 a = 1; 3 * a * a <= n; a++) for (i64 b = -a + 1; b <= a; b++) {
        if (((b - D) & 1) != 0) continue;
        i128 num = (i128)b * b - D; if (num % (4 * a)) continue;
        i64 c = (i64)(num / (4 * a)); if (c < a) continue; if (c == a && b < 0) continue; h++; }
    return h;
}
static i64 brute_order(Form g, i64 D, i64 cap) {
    Form cur = g; for (i64 k = 1; k <= cap; k++) { if (is_id(cur, D)) return k; cur = compose(cur, g, D); } return cap + 1;
}

int main(int argc, char **argv) {
    if (argc >= 5 && !strcmp(argv[1], "test")) {
        int K = atoi(argv[2]); i64 lo = atoll(argv[3]), hi = atoll(argv[4]);
        init_tables(hi);
        u64 s = 0x9E3779B97F4A7C15ULL; int bad_h = 0, bad_o = 0, tested = 0, otested = 0, unsafe = 0;
        for (int it = 0; tested < K && it < 100 * K; it++) {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17; i64 n = lo + (i64)(s % (u64)(hi - lo));
            int m16 = (int)(n % 16); if (!((n % 4) == 3 || m16 == 4 || m16 == 8)) continue;
            int sq = 1; for (int k = 1; k < nbigp && (i64)bigp[k] * bigp[k] <= n; k++) if (n % ((i64)bigp[k] * bigp[k]) == 0) { sq = 0; break; }
            if (!sq) continue;
            tested++;
            i64 hb = brute_h(n), he = hexact(n, bigp, nbigp);
            if (hb != he) { bad_h++; if (bad_h < 5) printf("H MISMATCH n=%lld brute=%lld exact=%lld\n", n, hb, he); }
            /* BSGS conclusion vs the true order of g_p for the first split p, for M = N and smaller M */
            i64 D = -n;
            for (int k = 0; k < nsp; k++) { int p = sprimes[k]; if (chi(n, p) != 1) continue;
                i64 b; if (p == 2) b = 1; else { int r = (int)(((D % p) + p) % p); b = sqrtmod[p][r]; if (((b - D) & 1) != 0) b = p - b; }
                Form g; g.a = p; g.b = b; g.c = (i64)(((i128)b * b - D) / (4 * p)); normalize_reduce(&g, D);
                i64 ord = brute_order(g, D, hb + 1);
                if (ord > hb || hb % ord != 0) { bad_o++; printf("ORDER does not divide h: n=%lld p=%d ord=%lld h=%lld\n", n, p, ord, hb); }
                for (i64 M = 1; M <= 2 * hb + 2 && M <= 1000000; M = M * 2 + 1) {
                    int bs = order_exceeds(g, M, D); otested++;
                    i64 mm = (i64)sqrt((double)M); if (mm < 1) mm = 1; while (mm * mm < M) mm++; i64 tt = (M + mm - 1) / mm;
                    /* Jaswal: the test succeeds exactly when ord > m*t (>= M). UNSAFE would be bs = 1 with ord <= M. */
                    if (bs && ord <= M) { unsafe++; printf("UNSAFE BSGS n=%lld p=%d M=%lld ord=%lld\n", n, p, M, ord); }
                    if (bs != (ord > mm * tt)) { bad_o++; if (bad_o < 5) printf("BSGS MISMATCH n=%lld p=%d M=%lld mt=%lld ord=%lld bsgs=%d\n", n, p, M, mm * tt, ord, bs); }
                }
                break; }
        }
        printf("unit tests: %d discriminants (h: brute vs exact) bad=%d; %d BSGS checks bad=%d unsafe=%d\n", tested, bad_h, otested, bad_o, unsafe);
        return (bad_h || bad_o || unsafe) ? 1 : 0;
    }
    if (argc < 7) { fprintf(stderr, "usage: range1 N LO HI SEG THREADS OUTDIR | range1 test K LO HI\n"); return 2; }
    N = atoll(argv[1]); LO = atoll(argv[2]); HI = atoll(argv[3]); SEG = atoll(argv[4]); THREADS = atoi(argv[5]);
    snprintf(OUTDIR, sizeof OUTDIR, "%s", argv[6]);
    init_tables(HI);
    nseg = (HI - LO + SEG - 1) / SEG;
    pthread_t tid[256]; if (THREADS > 256) THREADS = 256;
    for (int t = 0; t < THREADS; t++) pthread_create(&tid[t], NULL, seg_worker, NULL);
    for (int t = 0; t < THREADS; t++) pthread_join(tid[t], NULL);
    printf("DONE segments=%lld\n", nseg);
    return 0;
}
