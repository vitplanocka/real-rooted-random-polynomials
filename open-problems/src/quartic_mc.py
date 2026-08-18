"""From-scratch Monte Carlo cross-checks for P_B.

Three structurally different estimators:
  (A) plain 4-D MC on (b,c,d,e) using ONLY the sign conditions
      Delta>0, P<0, D<0  (no critical-point machinery at all);
  (B) Rao-Blackwellised 3-D MC: P_B = E_{b,c,d}[ |admissible e-interval| ] / 2,
      with the interval length from the critical points (variance-reduced);
  (C) 2-D MC in (b,u) with the s-integral (i.e. the d- and e-integrals) done
      exactly via Psi -- same integrand the quadrature uses, independent sampling.

Usage: nice -n 10 python src/quartic_mc.py [n_batches]
"""

import json
import multiprocessing as mp
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.dirname(HERE)

CHUNK = 4_000_000


def _worker_A(seed):
    from quartic_common import four_real_by_signs
    rng = np.random.default_rng(seed)
    hits = 0
    for _ in range(N_CHUNKS_PER_WORKER):
        b = rng.random(CHUNK) * 2.0 - 1.0
        c = rng.random(CHUNK) * 2.0 - 1.0
        d = rng.random(CHUNK) * 2.0 - 1.0
        e = rng.random(CHUNK) * 2.0 - 1.0
        hits += int(np.count_nonzero(four_real_by_signs(b, c, d, e)))
    return hits, N_CHUNKS_PER_WORKER * CHUNK


def _worker_B(seed):
    from quartic_common import e_length_clipped
    rng = np.random.default_rng(seed)
    s = 0.0
    s2 = 0.0
    n = 0
    for _ in range(N_CHUNKS_PER_WORKER):
        b = rng.random(CHUNK) * 2.0 - 1.0
        c = rng.random(CHUNK) * 2.0 - 1.0
        d = rng.random(CHUNK) * 2.0 - 1.0
        L = e_length_clipped(b, c, d) * 0.5      # divide by e-density support
        s += float(L.sum())
        s2 += float((L * L).sum())
        n += CHUNK
    return s, s2, n


def _worker_C(seed):
    from quartic_quad import Psi, s_limits, CONST
    rng = np.random.default_rng(seed)
    s = 0.0
    s2 = 0.0
    n = 0
    for _ in range(N_CHUNKS_PER_WORKER):
        b = rng.random(CHUNK) * 2.0 - 1.0
        Umax = np.sqrt(9.0 * b * b + 24.0)
        u = rng.random(CHUNK) * Umax
        sl, sh = s_limits(b, u)
        # estimator of (1/16)*(1/CONST)*Int db du : measure = 2 * Umax
        val = u ** 8 * (Psi(sh) + Psi(-sl)) * (2.0 * Umax) / (16.0 * CONST)
        s += float(val.sum())
        s2 += float((val * val).sum())
        n += CHUNK
    return s, s2, n


if __name__ == "__main__":
    NPROC = 26
    N_CHUNKS_PER_WORKER = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    globals()["N_CHUNKS_PER_WORKER"] = N_CHUNKS_PER_WORKER
    out = {}

    for tag, worker in (("A", _worker_A), ("B", _worker_B), ("C", _worker_C)):
        t0 = time.time()
        seeds = [10_000_000 + 1000 * ord(tag) + i for i in range(NPROC)]
        with mp.Pool(NPROC, initializer=None) as pool:
            res = pool.map(worker, seeds)
        dt = time.time() - t0
        if tag == "A":
            hits = sum(r[0] for r in res)
            N = sum(r[1] for r in res)
            p = hits / N
            sig = np.sqrt(p * (1 - p) / N)
            print(f"[A] plain 4-D sign MC : N={N:,}  P_B={p:.9f} +/- {sig:.2e}"
                  f"   ({dt:.0f}s)")
            out["A"] = {"N": N, "hits": hits, "PB": p, "sigma": sig, "sec": dt}
        else:
            S = sum(r[0] for r in res)
            S2 = sum(r[1] for r in res)
            N = sum(r[2] for r in res)
            p = S / N
            var = max(S2 / N - p * p, 0.0)
            sig = np.sqrt(var / N)
            name = ("Rao-Blackwellised 3-D" if tag == "B"
                    else "2-D (b,u) with exact Psi")
            print(f"[{tag}] {name}: N={N:,}  P_B={p:.12f} +/- {sig:.2e}"
                  f"   ({dt:.0f}s)")
            out[tag] = {"N": N, "PB": p, "sigma": sig, "sec": dt}

    with open(os.path.join(ROOT, "results", "quartic_mc.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("wrote results/quartic_mc.json")
