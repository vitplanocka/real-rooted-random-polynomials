"""High-accuracy table of V(t) itself, t >= 1 (clipping active for every t > 1).

`nonmonic_vt.V_of_t` scans for A-kinks on a purely linear grid, which starts
missing structure once t is large (its t = 5, 10 values are only ~1e-11
consistent with the scaling identity). Here the same computation is redone with
a linear+logarithmic A-grid, and cross-checked against

    V(t) = 8 p(1/t) / (1/t)^3 = 8 t^3 p(1/t)

which comes from a completely different integration order (b before A).

Also emits the exact anchors V(1) = 766/1215 + ln3/6 and the depressed-cubic
anchor 2 sqrt(3)/45.

Output: results/vt_table.json
"""
import json
import os
import sys

import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nonmonic_vt as M  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "vt_table.json")
mp.mp.dps = 40
M.DPS = 40


def A_grid(t, nlin=801, nlog=401):
    return np.unique(np.concatenate([
        np.linspace(0.0, t, nlin),
        np.geomspace(max(1e-12, t * 1e-12), t, nlog)]))


def V_of_t(t, degree=9):
    tf = float(t)

    def sig(A):
        return M.case_signature(
            A, 27.0, 27.0 * tf,
            float(np.sqrt(max(A * A - 3 * tf, 0.0))),
            float(np.sqrt(A * A + 3 * tf)))

    cuts = M._find_cuts(sig, 0.0, tf, nbis=60, grid=A_grid(tf))
    tot = mp.mpf(0)
    for x0, x1 in zip(cuts[:-1], cuts[1:]):
        if x1 - x0 < 1e-14:
            continue
        tot += mp.quad(lambda A: M.V_inner_A(A, mp.mpf(t)),
                       [mp.mpf(x0), mp.mpf(x1)], maxdegree=degree)
    return 2 * mp.mpf(2) / 3 * tot


def main():
    res = {}
    V1x = mp.mpf(766) / 1215 + mp.log(3) / 6
    dep = M.inner_sigma_integral(mp.mpf(0), mp.mpf(27), mp.mpf(27),
                                 mp.mpf(0), mp.sqrt(3)) * mp.mpf(2) / 3 / 4
    res["anchor_depressed"] = {"computed": mp.nstr(dep, 30),
                               "exact_2sqrt3_over_45":
                                   mp.nstr(2 * mp.sqrt(3) / 45, 30),
                               "abs_err": mp.nstr(abs(dep - 2 * mp.sqrt(3) / 45), 5)}
    print("depressed anchor:", res["anchor_depressed"])

    rows = []
    for t in (1, 1.25, 1.5, 2, 3, 4, 5, 7, 10, 20, 50):
        a = 1 / mp.mpf(t)
        M._set_prec_for(a)
        v_p = 8 * M.p_of_a(a, degree=9) / a ** 3
        mp.mp.dps = 40
        M.DPS = 40
        v_d = V_of_t(t)
        rel = abs(v_d - v_p) / abs(v_d)
        rows.append({"t": t, "V_direct_A_order": mp.nstr(v_d, 28),
                     "V_via_p_b_order": mp.nstr(v_p, 28),
                     "rel_diff": mp.nstr(rel, 5)})
        extra = ""
        if t == 1:
            extra = f"   exact 766/1215+ln3/6 = {mp.nstr(V1x, 25)}  |err| " \
                    f"{mp.nstr(abs(v_d - V1x), 4)}"
        print(f"V({t:<5}) = {mp.nstr(v_d, 25)}  via p {mp.nstr(v_p, 25)}"
              f"  reldiff {mp.nstr(rel, 4)}{extra}", flush=True)
    res["V_table"] = rows
    res["V1_exact"] = mp.nstr(V1x, 30)

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
