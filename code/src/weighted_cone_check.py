"""Second, independent derivation of the same decomposition -- weighted cone.

For FIXED leading coefficient a, the substitution x -> x/lambda shows

    (a, b, c, d)  ->  (a, lambda b, lambda^2 c, lambda^3 d)

preserves real-rootedness.  So the real-rooted set in (b,c,d) is a cone for the
WEIGHTED scaling with weights (1,2,3).  The Euler field F = (b, 2c, 3d)/6 has
div F = 1 and F . grad(Disc) = 6 Disc = 0 on the boundary (Disc is
weighted-homogeneous of degree 6 in these weights), so

    6 * 8 p(a) = (A_b^+ + A_b^-) + 2 (A_c^+ + A_c^-) + 3 (A_d^+ + A_d^-)

with A_X^s = area of the real-rooted set on the face X = s (s = +-1) of
[-1,1]^2.  At FIXED a the only available sign symmetry is
(b,c,d) -> (-b,c,-d) (that is x -> -x followed by negating the polynomial),
which gives A_b^- = A_b^+ and A_d^- = A_d^+ but leaves the c-faces DISTINCT --
`c` is even under it.  So

    8 p(a) = (1/3) A_b + (1/3)(A_c^+ + A_c^-) + A_d.

(The 4D decomposition used elsewhere is the unweighted cone, where the central
symmetry (a,b,c,d)->(-a,-b,-c,-d) does pair up all eight faces.)

This script verifies the fixed-a identity numerically (grid areas, ~1e-4).

Output: results/weighted_cone_check.json
"""
import json
import os
import sys

import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nonmonic_vt as M  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "weighted_cone_check.json")

N = 6000


def real_rooted(a, b, c, d):
    """vectorised: does a x^3 + b x^2 + c x + d have 3 real roots?"""
    return (18 * a * b * c * d - 4 * b ** 3 * d + b * b * c * c
            - 4 * a * c ** 3 - 27 * a * a * d * d) > 0


def area(a, which, sign, n=N):
    """midpoint-grid area of the real-rooted set on the face `which` = sign."""
    g = (np.arange(n) + 0.5) / n * 2 - 1
    X, Y = np.meshgrid(g, g, indexing="ij")
    if which == "b":       # b = sign fixed; (c,d) free
        ok = real_rooted(a, sign, X, Y)
    elif which == "c":     # c = sign fixed; (b,d) free
        ok = real_rooted(a, X, sign, Y)
    else:                  # d = sign fixed; (b,c) free
        ok = real_rooted(a, X, Y, sign)
    return float(ok.mean()) * 4.0


def main():
    res = {"grid": N, "rows": []}
    for a in (0.2, 0.5, 0.9):
        Abp, Abm = area(a, "b", 1.0), area(a, "b", -1.0)
        Acp, Acm = area(a, "c", 1.0), area(a, "c", -1.0)
        Adp, Adm = area(a, "d", 1.0), area(a, "d", -1.0)
        rhs = ((Abp + Abm) + 2 * (Acp + Acm) + 3 * (Adp + Adm)) / 6
        M._set_prec_for(mp.mpf(a))
        lhs = float(8 * M.p_of_a(mp.mpf(str(a)), degree=8))
        row = {"a": a, "A_b_plus": Abp, "A_b_minus": Abm,
               "A_c_plus": Acp, "A_c_minus": Acm,
               "A_d_plus": Adp, "A_d_minus": Adm,
               "rhs_weighted_faces": rhs, "lhs_8p(a)": lhs, "diff": rhs - lhs}
        res["rows"].append(row)
        print(f"a={a}: A_b+-=({Abp:.6f},{Abm:.6f}) A_c+-=({Acp:.6f},{Acm:.6f}) "
              f"A_d+-=({Adp:.6f},{Adm:.6f})", flush=True)
        print(f"      rhs={rhs:.6f}  8p(a)={lhs:.6f}  diff={rhs-lhs:+.2e}",
              flush=True)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
