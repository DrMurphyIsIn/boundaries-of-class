\\ Writes data/max_disc_by_class_number.txt: for each h <= 100, h, the number of fundamental discriminants -D with
\\ 3 <= D <= 3000000 and class number h, the largest such D, and isprime(that D).  Run: gp -q < max_disc_by_class_number.gp
\\ For fundamental discriminants -D, D <= N: count fields and the largest D for each class number h <= H.
N = 3000000; H = 100;
cnt = vector(H); mx = vector(H);
for(D = 3, N, if(isfundamental(-D), h = qfbclassno(-D); if(h <= H, cnt[h]++; mx[h] = D)));
for(h = 1, H, printf("%d %d %d %d\n", h, cnt[h], mx[h], isprime(mx[h])));
