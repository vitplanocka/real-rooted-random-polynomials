"""Assemble results/nonmonic_quadrature.json -- deliverable 1 of TASK.md.

Collects, in one place:
  * the anchors, recomputed live through the route-1 code path
    (V(1) = 766/1215+ln3/6, depressed cubic 2 sqrt(3)/45, p(1) = 383/4860+ln3/48,
     p(0+) = 1/2+5/72+ln2/12),
  * the V(t) table for t >= 1 (clipping active), both integration orders,
  * P from route 1 (leading coefficient / V(t) route) with its
    degree-doubling and method-comparison evidence,
  * P from route 2 (face decomposition), exact and by quadrature,
  * the Monte Carlo, and the comparison against both candidates.
"""
import json
import os
import sys

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
R = os.path.join(HERE, "..", "results")
sys.path.insert(0, HERE)
import nonmonic_vt as M  # noqa: E402

mp.mp.dps = 40
M.DPS = 40


def load(name):
    p = os.path.join(R, name)
    if not os.path.exists(p):
        return None
    with open(p) as fh:
        return json.load(fh)


def main():
    out = {"quantity": "P(a x^3 + b x^2 + c x + d has 3 real roots), "
                       "(a,b,c,d) iid U[-1,1]"}

    # ---------------- anchors, live through the route-1 code path
    V1 = M.V_of_t(1)
    V1x = mp.mpf(766) / 1215 + mp.log(3) / 6
    dep = M.inner_sigma_integral(mp.mpf(0), mp.mpf(27), mp.mpf(27),
                                 mp.mpf(0), mp.sqrt(3)) * mp.mpf(2) / 3 / 4
    depx = 2 * mp.sqrt(3) / 45
    p1 = M.p_of_a(mp.mpf(1), degree=8)
    p1x = mp.mpf(383) / 4860 + mp.log(3) / 48
    p0x = mp.mpf(1) / 2 + mp.mpf(5) / 72 + mp.log(2) / 12
    out["anchors"] = {
        "V(1)": {"computed": mp.nstr(V1, 30), "exact_766_1215_plus_log3_6":
                 mp.nstr(V1x, 30), "abs_err": mp.nstr(abs(V1 - V1x), 5)},
        "depressed_cubic": {"computed": mp.nstr(dep, 30),
                            "exact_2sqrt3_over_45": mp.nstr(depx, 30),
                            "abs_err": mp.nstr(abs(dep - depx), 5)},
        "p(1)": {"computed": mp.nstr(p1, 30),
                 "exact_383_4860_plus_log3_48": mp.nstr(p1x, 30),
                 "abs_err": mp.nstr(abs(p1 - p1x), 5)},
        "p(0+)_limit_exact_1_2+5_72+log2_12": mp.nstr(p0x, 30),
        "note": "p(a) = p(0+) - (2/3) sqrt(a) + ... ; the sqrt endpoint is why "
                "plain Gauss nodes must not be used on the outer a-integral",
    }

    vt = load("vt_table.json")
    if vt:
        out["V_of_t_table"] = vt["V_table"]

    r1 = load("route1_closed_a.json")
    if r1:
        out["route1_leading_coefficient"] = {
            "description": "P = (1/6) int db int sigma G(b,sigma) dsigma, the "
                           "V(t)/leading-coefficient integral with the a-integral "
                           "in closed form; uses no part of the face "
                           "decomposition",
            "b_panels": len(r1["b_panels"]) - 1,
            "P_by_method_and_degree": r1["P_by_method"],
            "P": r1["P"],
            "method_spread": r1.get("method_spread"),
            "P_minus_exact": r1["P_minus_exact"],
            "P_minus_sweep": r1["P_minus_sweep"],
        }

    fe = load("face_exact.json")
    if fe:
        out["route2_face_decomposition"] = {
            "description": "P = (V(1)+S_b)/16 by the cone/divergence identity; "
                           "S_b evaluated in closed form",
            "S_b_exact": fe["S_b_exact"], "P_exact": fe["P_exact"],
            "P_numeric": fe["P_numeric"],
            "P_equals_dxdy_symbolically": fe["P_equals_dxdy"],
        }
    fv = load("face_verify.json")
    if fv:
        out["route2_verification"] = {
            "cone_identity_exact_on_quadratic_analogue":
                fv["cone_identity_quadratic_analogue"]["exact_match"],
            "S_b_by_quadrature_minus_exact": fv["S_b"]["diff_F"],
            "S_b_blind_pslq": fv["pslq"]["S_b"]["pslq"],
        }
    mc = load("nonmonic_mc.json")
    if mc:
        out["monte_carlo"] = {"n_samples": mc["n_samples"],
                              "raw_discriminant": mc["raw"],
                              "conditional": mc["cond"]}

    exact = mp.mpf(641) / 2430 - mp.log(3) / 24
    out["ANSWER"] = {
        "closed_form": "641/2430 - log(3)/24",
        "value_30_digits": mp.nstr(exact, 30),
        "dxdy_candidate": "641/2430 - log(3)/24  -> CONFIRMED (identical)",
        "literature_sweep_value": "0.217993225 +- 5e-8  -> REFUTED",
        "sweep_error": mp.nstr(exact - mp.mpf("0.217993225"), 6),
    }

    path = os.path.join(R, "nonmonic_quadrature.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out["anchors"], indent=2))
    print(json.dumps(out["ANSWER"], indent=2))
    print("written", os.path.abspath(path))


if __name__ == "__main__":
    main()
