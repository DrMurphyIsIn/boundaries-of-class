# numerics: the floating-point checks and the calibration behind the paper

None of this is part of the proof. The Lean kernel never sees these computations, and a wrong number here could not
make the proof pass. They check two things:
- that the numbers the paper quotes about the theorems are right;
- that the 28 kernel-checked statements agree with every imaginary quadratic field we could compute.

Every script reads its inputs from this directory and writes its outputs next to itself. Each output below was rerun
from this directory and is byte-identical to the one the paper was written from.

## What you need

- Python 3 with mpmath (1.3.0 was used) and matplotlib (3.9.4, for the figure only).
- A C compiler.
- PARI/GP, for the two `.gp` scripts.

Pin BLAS and OpenMP to one thread (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`). Every script runs in about a minute or
less.

## The scripts

| script | what it checks | inputs | how to run | output (md5) |
|---|---|---|---|---|
| `classcount2.c` | An independent count of reduced forms, giving h(−d) for every fundamental discriminant −d with 3 ≤ d ≤ 3·10⁶ (911,878 fields). It checks the version 2 statements against every one: (L′), (P′), (U′), the two half-log forms, (B′), (B*) and the thresholds for N ≤ 10. It also gives the extreme ratios quoted in the paper's calibration section, and the cumulative maxima max{d : h(−d) ≤ h}. | none | `cc -O2 -o classcount2 classcount2.c -lm && ./classcount2 > classcount2.out` | `classcount2.out` (`f540e0d1191b00fbacecb7c054300c95`) |
| `classcount.c` | The same count. It prints, for each h ≤ 100, the number of fields and the largest d. This is the table that must agree with PARI's (`data/max_disc_by_class_number.txt`, columns 1–3). It also checks the first version's statements. | none | `cc -O2 -o classcount classcount.c -lm && ./classcount > classcount.out` | `classcount.out` (`20494692526abe4fb0abb9c944b82e89`) |
| `max_disc_by_class_number.gp` | PARI's `qfbclassno` over the same range, giving, for each h ≤ 100, h, the number of fields, the largest d and whether that d is prime. Its output is the data file. | none | `gp -q < max_disc_by_class_number.gp > max_disc_by_class_number.out` | identical to `data/max_disc_by_class_number.txt` (`01d049d643b781fb40bc71308a681acd`) |
| `calib.gp` | PARI over every fundamental discriminant with 5 ≤ d ≤ 3·10⁶. The paper quotes only its field count, 911,876. Its other statistics use the constants of the first version of the statements (9/50, 6/5), and the comment at its top says so. | none | `gp -q < calib.gp > calib.out` | `calib.out` (`6508ca0ac3c13571a253867f55346feb`) |
| `r2_recheck.py` | The two new analytic steps of the lower bounds, in floating point. The K_{1/2} kernel bound is checked against direct quadrature, and the per-class minimum against a grid. H(d, σ) = 1 + P/m is recomputed at the threshold points, and the uniform constant along σ = 1 − min(1/8, 2/log d). | none | `python3 r2_recheck.py` | `r2_recheck.out` (`0d9e41ea981da4362ad2227d2056bc75`) |
| `paper_numbers_v2.py` | Every number the paper quotes about the theorems: the margins of (L′) and (P′), H(X_N, 7/8) for all thirteen thresholds, D′(h), the power form, (B*), their slack against the truth, the ratios to posted thresholds, and the asymptotic constants. | `data/max_disc_by_class_number.txt` | `python3 paper_numbers_v2.py` | `paper_numbers_v2.out` (`1fccca3fdf5bbb6ad2ae44411459614f`) |
| `figure_v2.py` | Draws the paper's Figure 1. | `data/max_disc_by_class_number.txt` | `python3 figure_v2.py` | `fig_boundary.pdf` (`64dbeac7e53bd22acdcd3f6ab6e6fb39`) and `fig_boundary_preview.png` (`9f14ccc732fb7ce9f22276b4ff75c7d2`) |

## The data file

`data/max_disc_by_class_number.txt` holds one line per class number h = 1, …, 100, with four columns:
- h;
- the number of fundamental discriminants −d with 3 ≤ d ≤ 3·10⁶ and class number h;
- the largest such d;
- 1 if that d is prime and 0 if not.

PARI computed it, and `classcount.c` reproduces columns 1–3 independently. By Watkins's determination of all fields
with h ≤ 100 (Math. Comp. 73 (2004)), every such field has d below 3·10⁶, so for h ≤ 100 these maxima are the true ones.

## Notes

- **Floating point.** The Python scripts compute in floating point (mpmath, 30 or 40 digits). They are evidence about
  the numbers, not proofs. The thresholds themselves are proved in Lean, with rational brackets.
- **The figure.** It is written without a creation timestamp, so that its bytes are reproducible. The copy compiled
  into the paper may differ from this one in that metadata field only; the drawing is the same.
- **The thresholds for N ≥ 1000.** The largest discriminants for h ≤ 1000 and h ≤ 2000 (227,932,027 and 1,062,350,083),
  used in the paper's tables and figure, are cited from the published tables of Kimura and Jaswal. They are not
  computed here.

`MD5SUMS.txt` lists every file in this directory.
