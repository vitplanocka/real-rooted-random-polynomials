"""Post-mortem: can the literature sweep's 0.217993225 +- 5e-8 be reproduced?

The sweep's recorded method (results/literature_sweep_raw.json) is
"scipy 1e-12 dblquad / tplquad on the exact interval-length reduction", with
its own note that "the scipy/dblquad error estimates were optimistic by ~4e-11
near C^1 kinks".  Here we run exactly that: nested scipy adaptive quadrature on

    P = (1/16) int int int  len([d_lo,d_hi] n [-1,1])  dc db da

with no kink splitting and no special treatment of the a -> 0 endpoint, at a few
tolerance settings, and compare with the exact value 641/2430 - ln(3)/24.

Output: results/sweep_postmortem.json
"""
import json
import math
import os
import time

import numpy as np
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "sweep_postmortem.json")

EXACT = 641.0 / 2430.0 - math.log(3.0) / 24.0
SWEEP = 0.217993225


def L(a, b, c):
    q = b * b - 3.0 * a * c
    if q <= 0.0:
        return 0.0
    s = math.sqrt(q)
    u = 27.0 * a * a
    hi = (b - s) ** 2 * (b + 2 * s) / u
    lo = (b + s) ** 2 * (b - 2 * s) / u
    v = min(hi, 1.0) - max(lo, -1.0)
    return v if v > 0.0 else 0.0


def P_nested(eps, limit, alo=0.0):
    """(1/16)*2*int_0^1 da int_-1^1 db int_-1^1 dc L   -- plain adaptive nesting."""
    def f_c(c, a, b):
        return L(a, b, c)

    def f_b(b, a):
        return quad(f_c, -1.0, 1.0, args=(a, b), epsabs=eps, epsrel=eps,
                    limit=limit)[0]

    def f_a(a):
        return quad(f_b, -1.0, 1.0, args=(a,), epsabs=eps, epsrel=eps,
                    limit=limit)[0]

    val, err = quad(f_a, alo, 1.0, epsabs=eps, epsrel=eps, limit=limit)
    return 2.0 * val / 16.0, 2.0 * err / 16.0


def main():
    res = {"exact": EXACT, "sweep_claim": SWEEP, "runs": []}
    for eps, limit in ((1e-8, 50), (1e-10, 100), (1e-12, 200)):
        t = time.time()
        v, e = P_nested(eps, limit)
        row = {"epsabs_epsrel": eps, "limit": limit, "value": v,
               "scipy_error_estimate": e, "value_minus_exact": v - EXACT,
               "value_minus_sweep": v - SWEEP, "seconds": round(time.time() - t, 1)}
        res["runs"].append(row)
        print(f"eps={eps:g} limit={limit}: P={v:.12f}  scipy err est {e:.1e}  "
              f"P-exact={v-EXACT:+.3e}  P-sweep={v-SWEEP:+.3e}  "
              f"({row['seconds']}s)", flush=True)

    # how much of the damage is the a -> 0 endpoint?
    for alo in (1e-6, 1e-4, 1e-3, 1e-2):
        t = time.time()
        v, e = P_nested(1e-10, 100, alo=alo)
        # exact tail contribution of [0, alo] is <= 0.6272*alo/8*... (bounded)
        print(f"  a-range [{alo},1] at eps=1e-10: P={v:.12f}  "
              f"({time.time()-t:.0f}s)", flush=True)
        res["runs"].append({"a_lower_cut": alo, "value": v,
                            "scipy_error_estimate": e})

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
