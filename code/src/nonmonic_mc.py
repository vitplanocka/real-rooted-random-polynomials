"""Monte Carlo for P(a x^3 + b x^2 + c x + d has 3 real roots), iid U[-1,1].

Two estimators:

RAW      -- sign of the cubic discriminant
            Delta = 18abcd - 4b^3 d + b^2 c^2 - 4 a c^3 - 27 a^2 d^2 > 0.
            No use of any of this project's theory: it is the independent check.

COND     -- Rao-Blackwellised: sample (a,b,c) only, integrate d exactly using
            the proven band [d_lo, d_hi] (THEOREMS.md S1/S2):
                d_hi = (b-sig)^2 (b+2 sig)/(27 a^2),
                d_lo = (b+sig)^2 (b-2 sig)/(27 a^2),  sig = sqrt(b^2-3ac),
            estimator = len([d_lo,d_hi] n [-1,1]) / 2.  Much lower variance.

Chunked + multiprocess, modest RAM (each worker holds a few x 10^6 doubles).

Usage: python nonmonic_mc.py [n_total] [n_workers] [chunk]
Output: results/nonmonic_mc.json
"""
import json
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "nonmonic_mc.json")


def _worker(args):
    seed, n, chunk = args
    rng = np.random.Generator(np.random.PCG64(seed))
    hits_raw = 0
    sum_cond = 0.0
    sumsq_cond = 0.0
    done = 0
    while done < n:
        m = int(min(chunk, n - done))
        a = rng.uniform(-1.0, 1.0, m)
        b = rng.uniform(-1.0, 1.0, m)
        c = rng.uniform(-1.0, 1.0, m)
        d = rng.uniform(-1.0, 1.0, m)
        # --- raw discriminant
        disc = (18.0 * a * b * c * d - 4.0 * b ** 3 * d + b * b * c * c
                - 4.0 * a * c ** 3 - 27.0 * a * a * d * d)
        hits_raw += int(np.count_nonzero(disc > 0.0))
        # --- conditional (integrate d out exactly); reuse a,b,c
        q = b * b - 3.0 * a * c
        ok = q > 0.0
        sig = np.sqrt(np.where(ok, q, 0.0))
        u = 27.0 * a * a
        with np.errstate(divide="ignore", invalid="ignore"):
            hi = (b - sig) ** 2 * (b + 2.0 * sig) / u
            lo = (b + sig) ** 2 * (b - 2.0 * sig) / u
        # a<0 flips which critical point is the max: swap so lo<=hi
        lo2 = np.where(a > 0.0, lo, -hi)
        hi2 = np.where(a > 0.0, hi, -lo)
        ln = np.minimum(hi2, 1.0) - np.maximum(lo2, -1.0)
        ln = np.where(ok & np.isfinite(ln), np.maximum(ln, 0.0), 0.0)
        est = 0.5 * ln
        sum_cond += float(est.sum())
        sumsq_cond += float((est * est).sum())
        done += m
    return hits_raw, sum_cond, sumsq_cond, n


def main():
    n_total = int(float(sys.argv[1])) if len(sys.argv) > 1 else 1_000_000_000
    nw = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    chunk = int(float(sys.argv[3])) if len(sys.argv) > 3 else 4_000_000
    per = n_total // nw
    t0 = time.time()
    tasks = [(20260817 + 7919 * k, per, chunk) for k in range(nw)]
    with Pool(nw) as pool:
        res = pool.map(_worker, tasks)
    hits = sum(r[0] for r in res)
    s1 = sum(r[1] for r in res)
    s2 = sum(r[2] for r in res)
    n = sum(r[3] for r in res)
    p_raw = hits / n
    se_raw = (p_raw * (1 - p_raw) / n) ** 0.5
    p_cond = s1 / n
    var_cond = max(s2 / n - p_cond ** 2, 0.0)
    se_cond = (var_cond / n) ** 0.5
    dt = time.time() - t0

    import math
    cand1 = 641.0 / 2430.0 - math.log(3.0) / 24.0
    cand2 = 0.217993225
    out = {
        "n_samples": n, "n_workers": nw, "chunk": chunk,
        "elapsed_seconds": round(dt, 1),
        "raw": {"p": p_raw, "se": se_raw,
                "z_vs_dxdy": (p_raw - cand1) / se_raw,
                "z_vs_sweep": (p_raw - cand2) / se_raw},
        "cond": {"p": p_cond, "se": se_cond,
                 "z_vs_dxdy": (p_cond - cand1) / se_cond,
                 "z_vs_sweep": (p_cond - cand2) / se_cond},
        "candidates": {"dxdy_641_2430_minus_log3_24": cand1,
                       "sweep": cand2},
    }
    print(json.dumps(out, indent=2))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=2)


if __name__ == "__main__":
    main()
