"""The exception list for gen_asm.py: every squarefree uncertified lane m listed by gen_blocks.py
(exceptions_<fam>_<k0>.txt), with the smallest Y (from checkat_mirror.py's grid) at which `checkAt N` settles it, or 0
if m is in the W list (the fields the split-prime count cannot certify at any Y; they need an exact class number,
pillar 3). Real mode REFUSES an m that is neither. Y is DATA: the assembly check re-runs `checkAt` in the kernel.

    python3 make_xs.py <xs.json> <N> <exceptions.txt> [...] [--w <W.txt>] [--test]

--w <W.txt>: the W list, one radicand per line (default: empty).
--test: an uncertifiable lane gets Y = 0 (it becomes the assembly's W list) instead of a refusal.
"""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from checkat_mirror import certify
argv = sys.argv[1:]; test = "--test" in argv; argv = [a for a in argv if a != "--test"]
W = set()
if "--w" in argv:
    i = argv.index("--w"); W = {int(l) for l in Path(argv[i + 1]).read_text().split()}; del argv[i:i + 2]
out, N, files = Path(argv[0]), int(argv[1]), argv[2:]
ms = sorted({int(l) for f in files for l in Path(f).read_text().split()})
xs, bad = [], []
for m in ms:
    if m in W and not test: xs.append([m, 0]); continue
    y = certify(m, N)
    if y is None:
        if test: xs.append([m, 0])
        else: bad.append(m)
    else: xs.append([m, y])
if bad:
    sys.exit(f"REFUSED: {len(bad)} exception lane(s) neither in W nor settled by checkAt {N}: {bad[:10]}")
out.write_text(json.dumps({"N": N, "xs": xs}, indent=0) + "\n")
print(f"{len(xs)} exception lanes ({sum(1 for _, y in xs if y == 0)} with Y = 0), max Y {max([y for _, y in xs] or [0])}")
