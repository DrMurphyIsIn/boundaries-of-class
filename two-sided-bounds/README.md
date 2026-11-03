# Entry 5: explicit two-sided bounds for every imaginary quadratic field

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23924566.svg)](https://doi.org/10.5281/zenodo.23924566)

Entry 5 of [The Boundaries of Class](../README.md), released in v2.0.0 (all versions:
[10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257)). The paper is [`paper/paper.pdf`](paper/paper.pdf).

The earlier entries in this repository each settle one class number: one, then at most two. This entry asks a
different question. Take *any* imaginary quadratic field. How small, and how large, can its class number be, as an
explicit function of its discriminant? And, turned around, how large can the discriminant of a field of class number
h be?

The answers below are explicit, uniform over all fields, and proved in Lean 4 over Mathlib. Two independent kernels
have checked them.

## What it proves

Take K = ℚ(√−m) with m squarefree. Write d = |disc K| and h = h(K). The entry proves 28 statements, all written with
nothing but Mathlib's own definitions. The ones most people will want are these.

**Lower bounds:**
- **(L′)** h ≥ (1/3)·√d / log d, for every d ≥ 2981;
- **(P′)** h ≥ d^{7/16} / 17, for every d ≥ 1000.

**The class number formula and upper bounds:**
- **(CNF)** Dirichlet's class number formula, L(1, χ) = π·h/√d for d ≥ 5, and the general form with the number of
  roots of unity w(K);
- **(U′)** h ≤ (1/π)·√d·(log d + 7/6), for d ≥ 5;
- **(U″)** the textbook bound h ≤ (1/π)·√d·(½ log d + log(log d + 1/3) + 5/3), from the Pólya–Vinogradov inequality
  with an explicit constant.

**Upper bounds for the discriminant:**
- **(B*)** if h(K) ≤ h, then d ≤ min( max(1000, (17h)^{16/7}), max(2981, (6h·(log 6h + log(2 log 6h)))²) );
- **(T)** ten explicit thresholds and three point values:

| class number at most | 1 | 2 | 3 | 4 | 5 | 10 | 100 | 1000 | 2000 | 5000 |
|---|---|---|---|---|---|---|---|---|---|---|
| forces d below | 660 | 2,210 | 4,740 | 8,310 | 13,000 | 54,500 | 8.62·10⁶ | 1.605·10⁹ | 7.8·10⁹ | 6.32·10¹⁰ |

The three point values are: d ≥ 2·10⁹ forces h ≥ 1101; d ≥ 1.98·10¹⁰ forces h ≥ 3007; and d ≥ 2⁴⁰ forces
h ≥ 17,450.

The other statements are the explicit bound for L(1, χ), the Pólya–Vinogradov inequality, the half-log bounds, and the
primitivity and uniqueness of the character of K. They are listed verbatim in an appendix of the paper.

## Why it matters, and why it is not more than it is

For most of the twentieth century, a computable lower bound for h grew only like log d. Siegel's theorem gives
h ≥ c(ε)·d^{1/2−ε}, but nobody can compute c(ε). The proof splits on whether an exceptional real zero of an L-function
exists, and on the branch where one does, it says nothing about the fields not yet seen.

In October 2026 OpenAI posted a manuscript, with a Lean proof, showing that no Dirichlet L-function vanishes when
Re s > 7/8. An argument of Gronwall and Hecke, published by Landau in 1918, turns "no real zero near s = 1" into
"h is at least about √d/log d". The 7/8 theorem supplies that hypothesis for every field at once. So **(L′) is not new
mathematics in kind**. It is that century-old deduction, run with the new input and with every constant written out
and checked.

What *is* worth having is how strong the result is and how it is checked.
- **Among bounds that use the 7/8 input at real points only, the lower bounds are, as far as we know, the strongest explicit ones.**
  - Compared with the thresholds LemmaLab posted in the comments of Terence Tao's challenge, ours are 1.9 to 7.7 times
    smaller.
  - The three point values are larger than the three that Manvir Jaswal posted from Hecke's integral representation: 1101
    against 1096, 3007 against 3002, and 17,450 against 17,358.
  - The uniform constant 1/3 improves on his 1/5.
  - The comparison is as of the thread on 21 October 2026 and the papers on 23 October 2026. The paper has the full table, with every
    column labelled kernel-checked, cited, or our own evaluation.
- **We are plain about where it is not the best.**
  - At class number one the bound 660 is weaker than the 652 already proved in entry 1, and weaker than bounds
    obtained without the 7/8 input.
  - At two points, our own evaluation of Jaswal's method with an optimised parameter, which he did not post, does
    better than our kernel-checked statements: 6.24·10¹⁰ against 6.32·10¹⁰ for h ≤ 5000, and h ≥ 18,208 against 17,450
    at 2⁴⁰.
  - For very large discriminants, the bound h ≥ √|D|/(10π log log |D|) that the repository zeta-lab posted on 8 October
    2026, from the full 7/8 half-plane by Littlewood's method, is better than ours. It is weaker at every point we
    tabulate (at 2⁴⁰ it gives 10,046 against our 17,450), but it overtakes (P′) beyond about 5.3·10¹², (L′) beyond
    about 3.6·10¹⁶, and the inverted (B*) beyond h ≈ 8.5·10⁵. Our statements use the 7/8 theorem only at real points.
- **A bound is not a classification.** Kimura and Jaswal list every field of class number up to 2000 and 3000. That
  is a stronger kind of result. Turning our thresholds into complete lists for small class numbers is future work.
- **Nothing here says that fields of class number h exist near the bound.** For h ≤ 100, where the list of fields is
  complete, the true largest discriminant sits 6 to 13 times below (B*), and 3.6 to 5.3 times below the thresholds.

## How it works

The lower bounds and the upper bounds come from two separate routes.

**The lower bounds.**
- The Dedekind zeta function of K equals ζ(s)·L(s, χ). It also splits into one Epstein zeta function per ideal class.
- A Chowla–Selberg formula, proved for every positive definite form in entry 3, evaluates each class's piece at a real
  point σ ∈ [7/8, 1).
- There the left side is at most zero: ζ(σ) < 0, and the 7/8 theorem makes L(σ, χ) ≥ 0.
- On the right, each class contributes a main term g(a) = a^{−σ}ζ(2σ) − K·a^{−(1−σ)}, depending on its leading
  coefficient a, plus a small remainder.
- The posted bound, like our first version, charged every class the worst case, −K. But g has an exact minimum over a,
  by Bernoulli's inequality, and that minimum is far smaller. Charging each class its minimum is the whole gain: it
  raises the exponent at σ = 7/8 from 3/8 to 7/16.
- A sharper, K_{1/2}-type bound for the remainder does the rest.

**The upper bounds.**
- Mathlib's residue formula for the Dedekind zeta function gives Dirichlet's class number formula.
- Partial summation bounds L(1, χ), alone for (U′), or with the Pólya–Vinogradov inequality for (U″).
- No zero-free region is used anywhere in the upper bounds.

The 7/8 theorem enters the lower bounds through exactly one step of the checked proof, at real points only. Its Lean
proof is inside the checked closure, not assumed. Its manuscript has not been refereed.

## How it builds on the earlier entries

The class partition of the Dedekind zeta function, the Chowla–Selberg formula for a general form, the continuation
lemma and the positivity of L(σ, χ) above 7/8 were all built for entries 1 and 3. They were first published in
[tenth-discriminant](https://github.com/DrMurphyIsIn/tenth-discriminant), concept DOI
[10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257), and the relevant release is version 1.2.0
([10.5281/zenodo.23578359](https://doi.org/10.5281/zenodo.23578359)). This entry vendors those 76 files verbatim from
that release. The checked run compared each one with the release's md5s before anything else ran.

The new work is:
- the per-class minimum;
- the K_{1/2} kernel bound;
- the threshold engine at σ = 7/8;
- the uniform bounds (L′) and (P′);
- the class number formula;
- the Pólya–Vinogradov inequality with an explicit constant;
- the primitivity of the character;
- the bridge to Mathlib's discriminant.

That comes to 37 files and 6,513 lines of Lean.

## What is in this entry

| directory | what it holds |
|---|---|
| `formalization/` | the Lean 4 project: the solution library `BoundariesOfClass`, the challenge `BoundariesOfClassChallenges` (the 28 statements), and the vendored `CN1` and `HCN` modules |
| `numerics/` | floating-point and exact-rational checks of every constant the paper quotes, and the calibration against the class numbers of all 911,876 fundamental discriminants up to 3·10⁶ (PARI/GP, and an independent count of reduced forms in C) |
| `paper/` | the paper, its bibliography and its figure |

## How it was checked

The run of record was on 25 October 2026. It ran under a written plan that fixed every check and its expected output
beforehand.

- **Comparator.** Lean FRO's Comparator accepted all 28 theorems against the challenge, under both nanoda and Lean's
  own kernel: "Your solution is okay!".
  - It ran as a copy of v4.34.0 with one patched hunk. That hunk makes it refuse, rather than build, when a compiled
    module is missing.
  - Before it ran, the challenge was recompiled and checked to be byte-identical.
- **The closure audit.**
  - A walk over the closure of each of the 28 theorems found exactly the three standard axioms, `propext`,
    `Classical.choice` and `Quot.sound`.
  - In the 17 lower-bound statements, OpenAI's 7/8 theorem is reached through exactly one reference, applied at a real
    point.
  - The 11 class-number-formula, upper-bound and Pólya–Vinogradov statements contain no constant of OpenAI's
    development at all.
- **Controls.** The run's controls had to fail, and did:
  - a tampered threshold, 660 → 661;
  - a proof by `sorry`;
  - a false lemma slipped past the elaborator, which both kernels rejected;
  - stale or missing compiled files;
  - a wrong search path.
- **A separate AI session reproduced the whole run** from its own verified copies, with no differences. This is an AI
  review, not a referee's report, and it used the same machine and toolchain.

- **A fresh clone, built by these instructions.** On 3 November 2026 the repository was cloned from GitHub and this
  entry was built exactly as described below, in an empty directory with its own package store. Comparator then
  accepted all 28 theorems again under both kernels. It ran on the same machine and with the same checker binaries, so
  a replay elsewhere would still add something.

## How to build and check it

These are the commands we ran on a clean copy, in a directory with its own package store. Lean `v4.34.1` must be
installed through elan (`lean-toolchain` pins it). The one dependency, openai/math at commit `adc7f124`, brings Mathlib
`d13f23b`; its Lean-v4.34.1 compatibility patches for the packages it builds on are applied by the same script the class
number one entry uses:

      cd two-sided-bounds/formalization
      scripts/apply_oai_patches.sh          # clone the pinned packages and apply openai/math's patches (once)
      lake exe cache get                    # download the Mathlib build cache
      lake build BoundariesOfClass CN1 HCN HCNChallenges BoundariesOfClassChallenges BoundariesOfClassNegControls
      scripts/apply_oai_patches.sh --check  # confirm nothing drifted

Do not run `lake update`: it would move the pins.

- To run Comparator with both kernels, build Comparator `v4.34.0` with its `lean-toolchain` set to `v4.34.1` (there is no
  `v4.34.1` tag), build nanoda, and run `lake env comparator comparator_config.json` from `formalization/`, with
  `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA` and `COMPARATOR_LANDRUN` set. On macOS there is no landrun, so the
  sandbox layer is a pass-through and the run is not sandboxed. `comparator_config.json` lists the challenge module,
  the solution module `BoundariesOfClass.Main`, the 28 theorem names and the three permitted axioms, with nanoda
  enabled.

- To check the axioms, write a file that imports only `BoundariesOfClass.Main` and runs `#print axioms` on the 28
  theorems. Each should list exactly `propext`, `Classical.choice` and `Quot.sound`.
- Import the solution module alone, never together with the challenge. The challenge declares the same names, and Lean
  silently merges same-named declarations of the same type. Entry 3's paper explains why that matters.

The numerical checks are in [`numerics/`](numerics/README.md). They need only Python with mpmath and matplotlib, a C
compiler and PARI/GP, and its README says, for each script, what it checks and the md5 of its expected output. None of
them is part of the proof. The kernel never sees them.

## What is claimed, and what is not

- **Claimed:** a kernel-checked proof of the 28 statements, by these routes, with the record described in the paper.
- **Not claimed:**
  - **The mathematics.** It is due to Gronwall, Hecke, Landau, Dirichlet, Pólya and Vinogradov, and to the class-sum
    route posted in Tao's thread.
  - **Priority.**
  - **Any classification of fields.**
  - **Anything about the Riemann hypothesis,** or about Siegel zeros beyond what the 7/8 theorem itself gives.
  - **That fields of a given class number exist near the bounds.**
- **A caution about the input.** OpenAI's 7/8 manuscript is, as far as we know, not refereed. The kernels have checked
  its Lean proof, which sits inside the closure. A refereed human understanding of it is another matter.

## Credits

- **The 7/8 theorem and its Lean proof** are OpenAI's (openai/math, Apache-2.0).
- **The classical results.**
  - The deduction of class number bounds from zero-free segments is Gronwall's and Hecke's, published by Landau.
  - The class number formula is Dirichlet's.
  - The character-sum inequality is Pólya's and Vinogradov's.
  - The Chowla–Selberg formula is S. Chowla's and A. Selberg's.
- **The challenge** is Terence Tao's.
- **From Tao's thread.**
  - michaelmross gave the principal form's expansion.
  - Tao observed the d < 655 bound.
  - LemmaLab certified d ≤ 653, extended the argument to every class number with posted thresholds, and stated the
    d^{3/8}/12 form at 7/8. The lower bounds here follow that extension.
- **The bounds we compare against.** Manvir Jaswal's paper, linked from an anonymous comment in the thread, is the
  source of the Hecke-integral bound. Iwao Kimura's paper is the source of the explicit zero gap and the Lean-checked
  thresholds.
- **AI use as stated by others.** The commenters' and authors' own statements of their AI use are recorded in the
  paper.
- **Mathlib and the checking tools.** We thank Mathlib and its contributors, among them X. Roblot for the residue
  formula, M. Stoll for Gauss sums and D. Loeffler for the discrete Fourier transform and primitive characters. We also
  thank the authors of the packages OpenAI's proof builds on, Chris Bailey for nanoda, and the authors of Comparator
  and lean4export.

## AI disclosure

The formalization, the numerics, the calibration code and the paper were produced with extensive use of an AI assistant
(Claude, Anthropic) under the direction of the author, in separate sessions. A separate AI session reviewed the plan, the
statements and the delivered parts, and reproduced the run of record from its own copies. The mathematical routes are due
to the people credited above. The Lean kernel is the trusted component. The history, the attributions, the comparisons
and the account of how the work was checked are ours, and we have tried to say how each was obtained.

## The author's check

The author read back the paper and the verification record on 2 November 2026, and approved them.

## Licence

As for the rest of the repository: the mathematics, code and data are Apache-2.0, and the paper and documents are
CC-BY-4.0. See the repository's `LICENSING.md`.
