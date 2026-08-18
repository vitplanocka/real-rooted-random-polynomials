"""Fast vectorized ground-truth Monte Carlo for
       I16 = Int_{[-1,1]^3} L(b,c,d) db dc dd,      P_B = I16/16,
with L = g(x2) - max(g(x1),g(x3)) (0 where f' lacks 3 real crit points).

Two variants, both computed on the SAME samples:
  L_unclipped : ignores the e in [-1,1] clipping  -> I16
  L_clipped   : intersects the e-window with [-1,1] (should be identical)

Usage: nice -n 10 python src/quartic_gt_mc.py [n_chunks_per_worker] [nproc]
"""
import json, multiprocessing as mp, os, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.dirname(HERE)

CHUNK = 5_000_000


def _worker(args):
    seed, nch = args
    from quartic_common import crit_points, g_of
    rng = np.random.default_rng(seed)
    s = s2 = sc = 0.0
    n = 0
    nclip = 0
    mn_lo = np.inf
    mx_hi = -np.inf
    for _ in range(nch):
        b = rng.random(CHUNK) * 2.0 - 1.0
        c = rng.random(CHUNK) * 2.0 - 1.0
        d = rng.random(CHUNK) * 2.0 - 1.0
        x1, x2, x3 = crit_points(b, c, d)
        g1 = g_of(x1, b, c, d); g2 = g_of(x2, b, c, d); g3 = g_of(x3, b, c, d)
        elo = -g2
        ehi = -np.maximum(g1, g3)
        L = np.where(np.isfinite(elo), ehi - elo, 0.0)
        L = np.maximum(L, 0.0)
        Lc = np.minimum(np.where(np.isfinite(ehi), ehi, 0.0), 1.0) - np.maximum(
            np.where(np.isfinite(elo), elo, 0.0), -1.0)
        Lc = np.where(np.isfinite(elo), Lc, 0.0)
        Lc = np.maximum(Lc, 0.0)
        ok = np.isfinite(elo) & (L > 0)
        if ok.any():
            mn_lo = min(mn_lo, float(elo[ok].min()))
            mx_hi = max(mx_hi, float(ehi[ok].max()))
        nclip += int(np.count_nonzero(ok & ((elo < -1.0) | (ehi > 1.0))))
        s += float(L.sum()); s2 += float((L * L).sum()); sc += float(Lc.sum())
        n += CHUNK
    return s, s2, sc, n, nclip, mn_lo, mx_hi


if __name__ == "__main__":
    nch = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    t0 = time.time()
    with mp.Pool(nproc) as pool:
        res = pool.map(_worker, [(770_000 + i, nch) for i in range(nproc)])
    S = sum(r[0] for r in res); S2 = sum(r[1] for r in res)
    SC = sum(r[2] for r in res); N = sum(r[3] for r in res)
    NCL = sum(r[4] for r in res)
    mn_lo = min(r[5] for r in res); mx_hi = max(r[6] for r in res)
    m = S / N
    var = max(S2 / N - m * m, 0.0)
    sig = np.sqrt(var / N)
    I16 = 8.0 * m
    I16sig = 8.0 * sig
    out = {"N": N, "I16": I16, "I16_sigma": I16sig,
           "PB": I16 / 16.0, "PB_sigma": I16sig / 16.0,
           "I16_clipped": 8.0 * SC / N,
           "n_samples_with_e_clipping": NCL,
           "min_e_lo_seen": mn_lo, "max_e_hi_seen": mx_hi,
           "sec": time.time() - t0}
    print(json.dumps(out, indent=2))
    with open(os.path.join(ROOT, "results", "quartic_gt_mc.json"), "w") as f:
        json.dump(out, f, indent=2)
