/* Independent class numbers for the calibration section of the paper, version 2 statements (not part of any proof).
 *
 * For every fundamental discriminant -D with 3 <= D <= N, count the reduced positive definite forms (a, b, c) with
 * b^2 - 4ac = -D:  |b| <= a <= c, and b >= 0 whenever |b| = a or a = c.  For a fundamental discriminant every form is
 * primitive, so this count is h(-D).  The loop runs over (a, b, c) directly, about (N/4) sqrt(N/3) steps.
 * D is fundamental iff D = 3 mod 4 and squarefree, or D = 4m with m = 1, 2 mod 4 and m squarefree.
 *
 * Output, for the version 2 statements: the smallest value over the range of h divided by the lower bound of
 * (L') (1/3) sqrt D / log D (D >= 2981) and of (P') D^(7/16)/17 (D >= 1000); the largest value of h divided by the
 * upper bound of (U') (1/pi) sqrt D (log D + 7/6) and of the two half-log forms (D >= 5); each with the number of
 * violations; the number of violations of (B') D <= max(2981, (A (log A + log(2 log A)))^2), A = 6h, of (B*) (the
 * minimum of that and max(1000, (17h)^(16/7))), and of the thresholds h <= N => D < X_N for N in {1, 2, 3, 4, 5, 10};
 * and the cumulative maxima max{D : h(-D) <= h} for selected h <= 100.
 * Build: cc -O2 -o classcount2 classcount2.c -lm
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define N 3000000L

static int sqfree(long n, const unsigned char *sf) { return sf[n]; }

int main(void) {
    unsigned char *sf = malloc(N + 1);
    unsigned int *h = calloc(N + 1, sizeof(unsigned int));
    for (long i = 0; i <= N; i++) sf[i] = 1;
    sf[0] = 0;
    for (long p = 2; p * p <= N; p++)
        for (long k = p * p; k <= N; k += p * p) sf[k] = 0;

    /* enumerate reduced forms */
    for (long a = 1; 3 * a * a <= N; a++) {
        for (long b = -a + 1; b <= a; b++) {          /* |b| <= a, with b = -a excluded */
            long c0 = a;
            for (long c = c0;; c++) {
                long D = 4 * a * c - b * b;
                if (D > N) break;
                if (D < 3) continue;
                if (c == a && b < 0) continue;        /* a = c requires b >= 0 */
                h[D]++;
            }
        }
    }

    long cnt = 0, vL = 0, vP = 0, vU = 0, vH = 0, vLL = 0, vB = 0, vBs = 0, vT = 0;
    double rL = 1e9, rP = 1e9, rU = 0, rH = 0, rLL = 0; long aL = 0, aP = 0, aU = 0, aH = 0, aLL = 0;
    long hmaxD[101] = {0};
    const long TN[6] = {1, 2, 3, 4, 5, 10}; const double TX[6] = {660, 2210, 4740, 8310, 13000, 54500};
    for (long D = 3; D <= N; D++) {
        int fund = 0;
        if (D % 4 == 3 && sqfree(D, sf)) fund = 1;
        if (D % 4 == 0) { long m = D / 4; if ((m % 4 == 1 || m % 4 == 2) && sqfree(m, sf)) fund = 1; }
        if (!fund) continue;
        cnt++;
        long hh = h[D];
        if (hh <= 100 && D > hmaxD[hh]) hmaxD[hh] = D;
        double sD = sqrt((double)D), lD = log((double)D), PI = acos(-1.0);
        if (D >= 2981) { double r = hh / (sD / lD / 3.0); if (r < rL) { rL = r; aL = D; } if (r < 1) vL++; }
        if (D >= 1000) { double r = hh / (pow((double)D, 7.0 / 16.0) / 17.0); if (r < rP) { rP = r; aP = D; } if (r < 1) vP++; }
        if (D >= 5) {
            double u = sD * (lD + 7.0 / 6.0) / PI, hl = sD * (lD / 2 + log(lD + 1.0 / 3) + 5.0 / 3) / PI, ll = sD * (lD / 2 + log(lD) + 2) / PI;
            if (hh / u > rU) { rU = hh / u; aU = D; } if (hh > u) vU++;
            if (hh / hl > rH) { rH = hh / hl; aH = D; } if (hh > hl) vH++;
            if (hh / ll > rLL) { rLL = hh / ll; aLL = D; } if (hh > ll) vLL++;
        }
        double A = 6.0 * hh, Dp = A * (log(A) + log(2 * log(A))); Dp = Dp * Dp; if (Dp < 2981) Dp = 2981;
        double Ds = pow(17.0 * hh, 16.0 / 7.0); if (Ds < 1000) Ds = 1000; if (Ds > Dp) Ds = Dp;
        if ((double)D > Dp) vB++;
        if ((double)D > Ds) vBs++;
        for (int k = 0; k < 6; k++) if (hh <= TN[k] && (double)D >= TX[k]) vT++;
    }
    printf("fundamental discriminants -D, 3 <= D <= %ld: %ld\n", N, cnt);
    printf("(L') min h / ((1/3) sqrt D / log D) over D >= 2981: %.6f at D = %ld (h = %u); violations %ld\n", rL, aL, h[aL], vL);
    printf("(P') min h / (D^(7/16)/17) over D >= 1000: %.6f at D = %ld (h = %u); violations %ld\n", rP, aP, h[aP], vP);
    printf("(U') max h / ((1/pi) sqrt D (log D + 7/6)) over D >= 5: %.6f at D = %ld (h = %u); violations %ld\n", rU, aU, h[aU], vU);
    printf("(U'') max h / ((1/pi) sqrt D (log D/2 + log(log D + 1/3) + 5/3)) over D >= 5: %.6f at D = %ld (h = %u); violations %ld\n", rH, aH, h[aH], vH);
    printf("(U'' loglog) max h / ((1/pi) sqrt D (log D/2 + log log D + 2)) over D >= 5: %.6f at D = %ld (h = %u); violations %ld\n", rLL, aLL, h[aLL], vLL);
    printf("violations: (B') %ld, (B*) %ld, (T) for N in {1,2,3,4,5,10}: %ld\n", vB, vBs, vT);
    long cum = 0;
    for (int k = 1; k <= 100; k++) { if (hmaxD[k] > cum) cum = hmaxD[k];
        if (k <= 5 || k == 10 || k == 20 || k == 50 || k == 100) printf("cumulative max D with h <= %d: %ld\n", k, cum); }
    return 0;
}
