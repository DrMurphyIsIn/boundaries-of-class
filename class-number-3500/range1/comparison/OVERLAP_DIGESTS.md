# The h <= 3000 overlap below 10^7

The fields with `h <= 3000` and `|D| < 10^7`, extracted the same way from our range-(1) list and from Manvir Jaswal's
published list (Zenodo, doi:10.5281/zenodo.23251366), are byte-identical: 2,956,309 lines each, with SHA-256

    f5970eb2f627bdf6bc3a609c15c064899b3daa8ba16317e3f85aae5e020440bf

The extracts are not stored here. Jaswal's data belongs to his own deposit, and ours is a subset of the full list
deposited with this release. To regenerate either one, keep the lines `n h` with `n < 10000000` and `h <= 3000` of
the normalised list, in the list's own order, and hash the result with `shasum -a 256`.
