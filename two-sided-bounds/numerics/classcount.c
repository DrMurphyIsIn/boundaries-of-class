/* Independent class numbers for the calibration section of the paper (not part of any proof).
 *
 * For every fundamental discriminant -D with 3 <= D <= N, count the reduced positive definite forms (a, b, c) with
 * b^2 - 4ac = -D:  |b| <= a <= c, and b >= 0 whenever |b| = a or a = c.  For a fundamental discriminant every form is
 * primitive, so this count is h(-D).  The loop runs over (a, b, c) directly, about (N/4) sqrt(N/3) steps.
 * D is fundamental iff D = 3 mod 4 and squarefree, or D = 4m with m = 1, 2 mod 4 and m squarefree.
 *
 * Output: the largest D for each h <= 100 (to compare with the PARI table), the extreme values of
 * r1 = h log D / sqrt D and r2 = h / (sqrt D log D) over D >= 2981, and the number of violations of
 * (L) 9/50 sqrt D / log D <= h, (U) h <= 6/5 sqrt D log D (both for D >= 2981) and
 * (B) D <= max(2981, (A (log A + log(2 log A)))^2), A = (100/9) h.
 * Build: cc -O2 -o classcount classcount.c -lm
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

    long cnt = 0, viol_L = 0, viol_U = 0, viol_B = 0;
    long hmaxD[101] = {0}, hcnt[101] = {0};
    double r1min = 1e9, r2max = 0; long r1arg = 0, r2arg = 0;
    for (long D = 3; D <= N; D++) {
        int fund = 0;
        if (D % 4 == 3 && sqfree(D, sf)) fund = 1;
        if (D % 4 == 0) { long m = D / 4; if ((m % 4 == 1 || m % 4 == 2) && sqfree(m, sf)) fund = 1; }
        if (!fund) continue;
        cnt++;
        long hh = h[D];
        if (hh <= 100) { hcnt[hh]++; hmaxD[hh] = D; }
        double sD = sqrt((double)D), lD = log((double)D);
        if (D >= 2981) {
            double r1 = hh * lD / sD, r2 = hh / (sD * lD);
            if (r1 < r1min) { r1min = r1; r1arg = D; }
            if (r2 > r2max) { r2max = r2; r2arg = D; }
            if (9.0 / 50.0 * sD / lD > hh) viol_L++;
            if (hh > 6.0 / 5.0 * sD * lD) viol_U++;
        }
        double A = 100.0 / 9.0 * hh;
        double Dh = A * (log(A) + log(2 * log(A)));
        Dh = Dh * Dh;
        if (Dh < 2981) Dh = 2981;
        if ((double)D > Dh) viol_B++;
    }
    printf("fundamental discriminants -D, 3 <= D <= %ld: %ld\n", N, cnt);
    for (int k = 1; k <= 100; k++) printf("h %d count %ld maxD %ld\n", k, hcnt[k], hmaxD[k]);
    printf("min r1 over D >= 2981: %.6f at D = %ld (h = %u)\n", r1min, r1arg, h[r1arg]);
    printf("max r2 over D >= 2981: %.6f at D = %ld (h = %u)\n", r2max, r2arg, h[r2arg]);
    printf("violations: (L) %ld, (U) %ld, (B) %ld\n", viol_L, viol_U, viol_B);
    return 0;
}
