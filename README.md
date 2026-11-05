# The Boundaries of Class

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23550257.svg)](https://doi.org/10.5281/zenodo.23550257)

This repository collects one line of work on the class numbers of imaginary quadratic fields, from class number one up to
class number 3500. It builds on the arguments against Landau–Siegel zeros that appeared in October 2026, chiefly OpenAI's
Lean-formalized zero-free region Re s > 7/8 for Dirichlet L-functions. Each entry states exactly what a machine has
checked and what it has not.

It started as an entry for Terence Tao's
[experimental AI-math challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/)
of 20 October 2026. The challenge was to take one of the new arguments and use it to bound a hypothetical tenth imaginary
quadratic field of class number one, without Heegner's method, with any use of AI disclosed. Tao asked for quality over
speed: "this is not intended to be a race regarding who is 'first' to claim any given bound." The work here grew outward
from that question.

## Why the class number has a boundary

Fix a class number h. Only finitely many imaginary quadratic fields have class number h, but for most of the twentieth
century nobody could say how large their discriminants might be. Siegel's theorem bounds them, but with a constant no one
can compute, because the proof splits on whether an exceptional real zero of a Dirichlet L-function exists. The effective
bounds that came later, from Goldfeld, Gross and Zagier, grow only like log d.

The October 2026 arguments remove that exceptional zero:
- OpenAI's manuscript and Lean proof that no Dirichlet L-function vanishes when Re s > 7/8;
- its uniform exclusion of Landau–Siegel zeros;
- the proofs of Banks, Kerr and Green that followed.

Once the zero is gone, a class number h forces a discriminant below an explicit bound. Below that bound, the question
becomes a finite computation. Each entry here is that idea at a different scale, and each one is checked as far as we
could manage.

## The entries, in order

| entry | what it proves | how it is checked | where |
|---|---|---|---|
| 1. Class number one, first route | ℚ(√−m) has class number one iff m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}, with no Heegner, Baker, Stark or Gross–Zagier input: the 7/8 theorem and the Chowla–Selberg formula give d ≤ 652, and split-prime certificates settle the rest | **kernel-checked** (Lean's kernel and nanoda), through OpenAI's 7/8 theorem | [`formalization/`](formalization/README.md), [`paper/`](paper/README.md) |
| 2. Class number one, determinant route | the same theorem, with no L-function, zeta function or zero-free theorem in the closure, by Green's derivative determinant made nonzero by van Dijk's finite-field argument | **kernel-checked**; nothing beyond Mathlib | [`determinant/`](determinant/README.md) |
| 3. Class number at most two | the 27 fields of class number at most two, and the eighteen of class number two, by LemmaLab's class-sum extension of the first route | **kernel-checked**, through the 7/8 theorem | [`hcn/`](hcn/README.md) |
| 4. Tenth-discriminant bounds compared | a survey of the bounds posted in the challenge thread, on one scale, and the light-machinery determinant bound improved to the cutoff \|D\| < 548 for class number one | certified in ball arithmetic, reproduced by a second implementation; **not** kernel-checked | [`comparison/`](comparison/README.md) |
| 5. Two-sided bounds for every field | 28 statements: h ≥ (1/3)·√d/log d for d ≥ 2981 and h ≥ d^{7/16}/17 for d ≥ 1000; Dirichlet's class number formula and h ≤ (1/π)·√d·(log d + 7/6); ten thresholds and three point values (e.g. h ≤ 1000 ⇒ d < 1.605·10⁹; d ≥ 2⁴⁰ ⇒ h ≥ 17,450) | **kernel-checked** (Lean's kernel and nanoda), the 7/8 theorem used at real points only | [`two-sided-bounds/`](two-sided-bounds/README.md), [`paper/`](two-sided-bounds/paper/paper.pdf) |
| 6. Class number at most 3500 | under the explicit real-zero bound of Kimura's Theorem 1, exactly 50,299,869 fields with h ≤ 3500, the largest \|D\| being 3,495,584,467 (h = 3477); extends Jaswal's classification by his method and reproduces his and Kimura's lists exactly; the full list is in the Zenodo record | **not** kernel-checked as a whole; see the entry for exactly which parts are | [`class-number-3500/`](class-number-3500/README.md), [`paper/`](class-number-3500/paper/paper.pdf) |

The current release is **v2.0.1** ([10.5281/zenodo.23932214](https://doi.org/10.5281/zenodo.23932214)), which corrects two
bibliographic references in v2.0.0; all versions share the concept DOI
[10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257). Entries 1 to 4 were published while this repository was
called **tenth-discriminant** (releases v1.0.0 to v1.4.0). The repository was renamed on 2 November
2026, when the later entries joined it; links to `DrMurphyIsIn/tenth-discriminant` redirect here, and the paths of
entries 1 to 4 are unchanged. Their original README, with the statements, the trust base, the six-step argument and how
each proof was checked, is [`TENTH_DISCRIMINANT.md`](TENTH_DISCRIMINANT.md).

## Where the line goes, and what "kernel-checked" means here

Entries 1, 2, 3 and 5 are kernel-checked from Mathlib's own definitions. Comparator accepts each proof under two
independent kernels, Lean's and nanoda, and the only axioms are Lean's three standard ones. The runs were local and not
sandboxed. When OpenAI's 7/8 theorem is used, its Lean proof sits inside the checked closure rather than being assumed. The
manuscript it formalises has not been refereed, and the kernel check covers the Lean proof, not the manuscript. Entries 4
and 6 rest on interval arithmetic and on agreement between independent programs and published data, and each says so.
None of this work has been refereed.

As the class number grows, the finite computations grow too, and the kernel can no longer replay them directly. The
classification up to 3500 rests on a sieve over every discriminant from 2⁴⁰ up to about 1.6·10¹⁵. A kernel replay of that sieve with
today's tools would take hundreds of days. That entry therefore does not claim to be kernel-checked. It states, step by
step, what each part rests on:
- a cited zero bound, and our own kernel replay of the stronger 7/8 theorem;
- a published unconditional tabulation;
- two independent programs;
- a sieve cross-checked against the published counts.

The aim is to leave a basis from which a fully kernel-checked classification can be built, by us or by anyone else. We
would be glad to collaborate on that. The design for it, with the per-range certificate format and a worked example,
is in [`class-number-3500/kernel-route/`](class-number-3500/kernel-route/README.md).

## Credits

The challenge is Terence Tao's. The arguments excluding Siegel zeros are OpenAI's (with its Lean formalizations), with
further proofs by William Banks, Bryce Kerr and Ben Green. Entry 2 follows the companion note of
twinheterodox/tenth-discriminant, building on L. Silberman, K. Pratt, B. Green and R. van Dijk; entries 3 and 5 follow
LemmaLab's class-sum extension posted in the challenge thread. Iwao Kimura made the zero bound explicit, checked it in Lean,
and determined all fields with h ≤ 2000. Manvir Jaswal extended that to h ≤ 3000, and entry 6 follows his method. The
sieve goes back to Mark Watkins. The unconditional tabulation of class groups up to 2⁴⁰ is Anton Mosunov's and Michael
Jacobson's. The individual entries credit the people whose routes they follow, including the commenters on Tao's post
whose ideas they use.

## How this was made

This work was produced with extensive use of Claude (Anthropic) under the direction of the author, who is responsible
for it. A separate AI session reviewed each entry before release. That review is not a substitute for a
human referee. The mathematical routes are due to the people credited above.

## Licensing

The mathematics, code and data are Apache-2.0. The papers and documents are CC-BY-4.0. The certificate engine
[Telperion](https://github.com/DrMurphyIsIn/telperion) is vendored in [`telperion/`](telperion/), a verbatim copy pinned in
`telperion/VENDORED.json`, under the Business Source License 1.1, which permits research, teaching, review and evaluation
outright. See [`LICENSING.md`](LICENSING.md).
