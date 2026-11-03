# The paper of entry 5

`paper.pdf` is built from `paper.tex` and `refs.bib` with

    pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper

`fig_boundary.pdf` is the figure that `../numerics/figure_v2.py` writes, and `statements_v2_extract.lean` is the
appendix's verbatim extract of the 28 statements from `../formalization/BoundariesOfClassChallenges/BoundaryV2.lean`.
The paper is licensed under CC-BY-4.0.
