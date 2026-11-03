"""Figure 1 of revision 3: upper bounds for |disc K| when h(K) <= h, against the truth.

Plotted:
- D'(h) of (B') and the power form max(1000, (17h)^(16/7)) of (B*) (the theorem is their minimum);
- the ten kernel-checked thresholds X_N;
- the cumulative truth max{d : h(-d) <= h} for h <= 100 (data/max_disc_by_class_number.txt, from PARI, reproduced by
  classcount.c; complete by Watkins), and at h = 1000 and 2000 from Kimura's and Jaswal's tables (cited);
- LemmaLab's posted thresholds (comment 698478; ball arithmetic, not Lean).
Output: fig_boundary.pdf (the paper's Figure 1) and fig_boundary_preview.png, next to this script.
"""
import math
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE, ORANGE, AQUA, YELLOW, MAGENTA = "#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"
INK, MUTED = "#1f1f1e", "#6b6a63"
HERE = os.path.dirname(os.path.abspath(__file__))

hm = {}
for line in open(os.path.join(HERE, "data", "max_disc_by_class_number.txt")):
    h, cnt, mx, isp = map(int, line.split())
    hm[h] = mx
cum, c = {}, 0
for h in range(1, 101):
    c = max(c, hm[h])
    cum[h] = c
cited_cum = {1000: 227932027, 2000: 1062350083}


def Dp(h):
    A = 6 * h
    return max(2981.0, (A * (math.log(A) + math.log(2 * math.log(A)))) ** 2)


def Pw(h):
    return max(1000.0, (17 * h) ** (16 / 7))


XN = {1: 660, 2: 2210, 3: 4740, 4: 8310, 5: 13000, 10: 54500, 100: 8.62e6, 1000: 1.605e9, 2000: 7.8e9, 5000: 6.32e10}
posted = {2: 4164, 10: 2.81e5, 100: 6.64e7, 1000: 1.18e10, 2000: 5.42e10, 5000: 4.02e11}

hs = [10 ** (k / 100) for k in range(0, 371)]
plt.rcParams.update({"font.family": "serif", "font.size": 9, "axes.edgecolor": MUTED, "axes.labelcolor": INK,
                     "xtick.color": MUTED, "ytick.color": MUTED})
fig, ax = plt.subplots(figsize=(6.0, 4.0))
ax.grid(True, which="major", color="#e4e3dc", linewidth=0.6)
ax.set_axisbelow(True)
ax.plot(hs, [Dp(h) for h in hs], color=BLUE, linewidth=2.0)
ax.plot(hs, [Pw(h) for h in hs], color=ORANGE, linewidth=1.5, linestyle="--")
ax.plot(list(cum), list(cum.values()), linestyle="none", marker="o", markersize=2.6, color=AQUA,
        markeredgecolor="white", markeredgewidth=0.3)
ax.plot(list(cited_cum), list(cited_cum.values()), linestyle="none", marker="o", markersize=4.5, markerfacecolor="white",
        markeredgecolor=AQUA, markeredgewidth=1.2)
ax.plot(list(posted), list(posted.values()), linestyle="none", marker="D", markersize=5, color=YELLOW,
        markeredgecolor=INK, markeredgewidth=0.5)
ax.plot(list(XN), list(XN.values()), linestyle="none", marker="s", markersize=5.5, color=MAGENTA,
        markeredgecolor=INK, markeredgewidth=0.5)
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlim(0.9, 7000)
ax.set_ylim(100, 3e12)
ax.set_xlabel("class number $h$")
ax.set_ylabel("$|\\mathrm{disc}\\,K|$")
ax.text(1.05, 1.0e10, "solid: $D'(h)$ of (B$'$); dashed: $(17h)^{16/7}$ of (B*)", color=INK, fontsize=8.5)
ax.text(1.05, 2.6e9, "squares: kernel-checked thresholds $X_N$", color=INK, fontsize=8.5)
ax.text(1.05, 6.8e8, "diamonds: posted in comment 698478 (ball arithmetic)", color=INK, fontsize=8.5)
ax.text(1.05, 1.8e8, "dots: largest $|\\mathrm{disc}\\,K|$ with $h(K) \\leq h$", color=INK, fontsize=8.5)
ax.text(1.05, 4.7e7, "(open dots at $h = 1000, 2000$: from published tables)", color=INK, fontsize=8.5)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "fig_boundary.pdf"), metadata={"CreationDate": None})  # no timestamp: reproducible bytes
fig.savefig(os.path.join(HERE, "fig_boundary_preview.png"), dpi=160)
