\\ Calibration (PARI/GP).  For every fundamental discriminant -D, 3 <= D <= N, D not in {3, 4}:
\\ r1 = h log D / sqrt D (statement (L) says r1 >= c1 for D >= 2981), r2 = h / (sqrt D log D) ((U): r2 <= c2),
\\ and the boundary (B): D <= Dfun(h).  Prints the extreme fields.  COMPUTED (qfbclassno; PARI's value is
\\ unconditional for these sizes when cross-checked against data/max_disc_by_class_number.txt, which agrees with Watkins for h <= 100).
\\ The statistics r1, r2 and Dfun use the constants of the first version of the statements (c1 = 9/50, c2 = 6/5,
\\ A = (100/9) h); the paper quotes from this script only the field count.  The version 2 statements are checked
\\ by classcount2.c.
N = 3000000; D0 = 2981; c1 = 9/50; c2 = 6/5;
Dfun(h) = { my(A = 2*h/c1); max(2981, (A*(log(A) + log(2*log(A))))^2) };
r1min = 10^9; r1arg = 0; r1minall = 10^9; r1argall = 0; r2max = 0; r2arg = 0; bviol = 0; cnt = 0;
\\ field-level tamper thresholds: count fields D >= D0 refuting c1' = 1/3 (c1 doubled is 9/25), 1/2, 1 and c2' = c2/10, c2/20
t1 = 0; t2 = 0; t3 = 0; t4 = 0; t5 = 0; t6 = 0;
{
for(D = 5, N, if(isfundamental(-D),
  h = qfbclassno(-D); cnt++;
  r1 = h*log(D)/sqrt(D); r2 = h/(sqrt(D)*log(D));
  if(r1 < r1minall, r1minall = r1; r1argall = D);
  if(D >= D0,
    if(r1 < r1min, r1min = r1; r1arg = D);
    if(r2 > r2max, r2max = r2; r2arg = D);
    if(r1 < 18/25, t1++); if(r1 < 1/2, t2++); if(r1 < 1, t3++);
    if(r2 > c2/10, t4++); if(r2 > c2/20, t5++); if(r2 > c2/40, t6++));
  if(D > Dfun(h), bviol++)));
printf("fields (5 <= D <= %d, fundamental): %d\n", N, cnt);
printf("min r1 = h log D/sqrt D over all D: %.6f at D = %d (h = %d)\n", r1minall, r1argall, qfbclassno(-r1argall));
printf("min r1 over D >= %d: %.6f at D = %d (h = %d); statement c1 = %.4f\n", D0, r1min, r1arg, qfbclassno(-r1arg), c1);
printf("max r2 = h/(sqrt D log D) over D >= %d: %.6f at D = %d (h = %d); statement c2 = %.4f\n", D0, r2max, r2arg, qfbclassno(-r2arg), c2);
printf("violations of (B) d <= D(h): %d\n", bviol);
printf("tamper counts over D >= %d: r1 < 18/25 (c1 x4): %d; r1 < 1/2: %d; r1 < 1: %d\n", D0, t1, t2, t3);
printf("tamper counts over D >= %d: r2 > c2/10: %d; r2 > c2/20: %d; r2 > c2/40: %d\n", D0, t4, t5, t6);
}
