"""Steps 1-3: validate sign characterization, confirm the critical-point /
e-interval picture, and map the clipping structure.

Run:  nice -n 10 .venv/bin/python src/quartic_structure.py
"""

import json
import os
import sys

import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from quartic_common import (  # noqa: E402
    crit_points,
    d_band,
    e_interval,
    e_length_clipped,
    four_real_by_signs,
    g_of,
    quartic_discriminant,
)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = {}

# ---------------------------------------------------------------- 0. symbolic
print("=== 0. sympy check of hard-coded discriminant ===")
x, b, c, d, e = sp.symbols("x b c d e")
Delta_sym = sp.discriminant(x**4 + b * x**3 + c * x**2 + d * x + e, x)
print("sympy Delta =", sp.expand(Delta_sym))
# compare with our numeric routine on random rationals
rng = np.random.default_rng(12345)
maxrel = 0.0
for _ in range(200):
    vals = rng.uniform(-2, 2, 4)
    sym = float(Delta_sym.subs(dict(zip((b, c, d, e), map(sp.Float, vals)))))
    num = float(quartic_discriminant(*vals))
    maxrel = max(maxrel, abs(sym - num) / max(1.0, abs(sym)))
print("max rel diff hardcoded vs sympy discriminant:", maxrel)
OUT["discriminant_max_rel_diff_vs_sympy"] = maxrel

# ------------------------------------------------- 1. validate sign condition
print("\n=== 1. sign characterization vs numpy.roots (200k samples) ===")
N = 200_000
rng = np.random.default_rng(2024)
B, C, D, E = rng.uniform(-1, 1, (4, N))
pred = four_real_by_signs(B, C, D, E)

# ground truth by numpy.roots (companion-matrix eigenvalues), batched
coeffs = np.stack([np.ones(N), B, C, D, E], axis=1)
comp = np.zeros((N, 4, 4))
comp[:, 0, :] = -coeffs[:, 1:]
comp[:, 1, 0] = 1.0
comp[:, 2, 1] = 1.0
comp[:, 3, 2] = 1.0
rts = np.linalg.eigvals(comp)
TOL = 1e-9
truth_real = np.sum(np.abs(rts.imag) < TOL, axis=1) == 4
# distinctness: min pairwise gap among the (real parts of) roots
rr = np.sort(rts.real, axis=1)
gaps = np.min(np.diff(rr, axis=1), axis=1)
truth = truth_real & (gaps > 1e-8)

mismatch = np.nonzero(pred != truth)[0]
print(f"predicted count = {pred.sum()}, truth count = {truth.sum()}")
print(f"mismatches = {mismatch.size}")
if mismatch.size:
    print("examples (b,c,d,e, pred, truth, min|Im|, gap):")
    for i in mismatch[:15]:
        print(
            f"  {B[i]:+.6f} {C[i]:+.6f} {D[i]:+.6f} {E[i]:+.6f}  "
            f"{pred[i]} {truth[i]}  {np.max(np.abs(rts[i].imag)):.3e} {gaps[i]:.3e}"
        )
OUT["step1_N"] = N
OUT["step1_mismatches"] = int(mismatch.size)
OUT["step1_pred_count"] = int(pred.sum())
OUT["step1_truth_count"] = int(truth.sum())
OUT["step1_mc_estimate"] = float(pred.mean())

# ------------------------------------------ 2. critical-point characterization
print("\n=== 2. critical-point / e-interval characterization ===")
# (a) does the crit-point criterion agree with the sign criterion?
lo, hi = e_interval(B, C, D)
crit_pred = np.isfinite(lo) & (E > lo) & (E < hi)
mis2 = int(np.count_nonzero(crit_pred != pred))
print(f"crit-point criterion vs sign criterion mismatches (200k): {mis2}")
OUT["step2_crit_vs_sign_mismatches"] = mis2

mis2b = int(np.count_nonzero(crit_pred != truth))
print(f"crit-point criterion vs numpy.roots mismatches (200k):   {mis2b}")
OUT["step2_crit_vs_roots_mismatches"] = mis2b

# (b) confirm the d-band: f' has 3 distinct real roots iff c < 3b^2/8 and
#     d in (d_lo, d_hi).
dl, dh = d_band(B, C)
band_pred = np.isfinite(dl) & (D > dl) & (D < dh)
# ground truth: cubic discriminant of f'
disc_fp = (
    18 * (4.0) * (3 * B) * (2 * C) * D
    - 4 * (3 * B) ** 3 * D
    + (3 * B) ** 2 * (2 * C) ** 2
    - 4 * 4.0 * (2 * C) ** 3
    - 27 * 16.0 * D**2
)
mis3 = int(np.count_nonzero(band_pred != (disc_fp > 0)))
print(f"d-band vs cubic discriminant of f' mismatches (200k):    {mis3}")
OUT["step2_dband_mismatches"] = mis3

# (c) sanity: is the unclipped e-interval always nonempty on the band?
onband = np.isfinite(lo)
print(f"fraction of (b,c,d) cube with 3 real crit pts: {onband.mean():.6f}")
print(f"min unclipped interval length on band: {np.min(hi[onband]-lo[onband]):.3e}")
OUT["frac_bcd_three_crit"] = float(onband.mean())
OUT["min_unclipped_len"] = float(np.min(hi[onband] - lo[onband]))

# ------------------------------------------------------ 3. clipping structure
print("\n=== 3. clipping structure ===")
# Monte-Carlo over (b,c,d) restricted to the band, measuring clipping.
M = 4_000_000
rng = np.random.default_rng(777)
bb, cc, dd = rng.uniform(-1, 1, (3, M))
lo, hi = e_interval(bb, cc, dd)
on = np.isfinite(lo)
clip_lo = on & (lo < -1.0)
clip_hi = on & (hi > 1.0)
clip_any = clip_lo | clip_hi
empty = on & (np.minimum(hi, 1.0) <= np.maximum(lo, -1.0))
print(f"|band| / 8 (frac of (b,c,d)-cube with 3 crit pts) = {on.mean():.6f}")
print(f"clip fraction of band (any side)  = {clip_any.sum()/on.sum():.6f}")
print(f"clip fraction of band (lower e<-1)= {clip_lo.sum()/on.sum():.6f}")
print(f"clip fraction of band (upper e>+1)= {clip_hi.sum()/on.sum():.6f}")
print(f"both sides clipped                = {(clip_lo&clip_hi).sum()/on.sum():.6f}")
print(f"interval entirely outside [-1,1]  = {empty.sum()/on.sum():.6f}")
# measure-weighted: how much e-length is lost to clipping?
raw = np.where(on, hi - lo, 0.0)
kept = e_length_clipped(bb, cc, dd)
print(f"mean raw length over cube  = {raw.mean():.8f}")
print(f"mean kept length over cube = {kept.mean():.8f}")
print(f"fraction of e-measure lost to clipping = {1-kept.sum()/raw.sum():.6f}")
OUT["clip"] = {
    "M": M,
    "band_frac": float(on.mean()),
    "clip_any_frac_of_band": float(clip_any.sum() / on.sum()),
    "clip_lo_frac_of_band": float(clip_lo.sum() / on.sum()),
    "clip_hi_frac_of_band": float(clip_hi.sum() / on.sum()),
    "clip_both_frac_of_band": float((clip_lo & clip_hi).sum() / on.sum()),
    "empty_after_clip_frac_of_band": float(empty.sum() / on.sum()),
    "mean_raw_len": float(raw.mean()),
    "mean_kept_len": float(kept.mean()),
    "measure_lost_frac": float(1 - kept.sum() / raw.sum()),
    "PB_from_this_mc": float(kept.mean() / 2.0),
}

# where does clipping happen? extremes of lo and hi
i = np.argmin(np.where(on, lo, np.inf))
print(f"min e_lo = {lo[i]:.6f} at (b,c,d)=({bb[i]:.4f},{cc[i]:.4f},{dd[i]:.4f})")
j = np.argmax(np.where(on, hi, -np.inf))
print(f"max e_hi = {hi[j]:.6f} at (b,c,d)=({bb[j]:.4f},{cc[j]:.4f},{dd[j]:.4f})")
OUT["clip"]["min_e_lo"] = float(lo[i])
OUT["clip"]["min_e_lo_at"] = [float(bb[i]), float(cc[i]), float(dd[i])]
OUT["clip"]["max_e_hi"] = float(hi[j])
OUT["clip"]["max_e_hi_at"] = [float(bb[j]), float(cc[j]), float(dd[j])]

os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
with open(os.path.join(ROOT, "results", "quartic_structure.json"), "w") as f:
    json.dump(OUT, f, indent=2)
print("\nwrote results/quartic_structure.json")
