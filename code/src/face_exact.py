"""EXACT evaluation of the face-decomposition route.

    P = (V(1) + S_b)/16,  V(1) = 766/1215 + ln(3)/6   (Theorem 1)
    S_b = vol_3{(a,c,d) in [-1,1]^3 : a x^3 + x^2 + c x + d has 3 real roots}

Derivation (all steps re-verified numerically at the bottom of this file):

b = 1 fixed, a > 0 (the map (a,c,d) -> (-a,-c,d), i.e. x -> -x, doubles),
sigma = s = sqrt(1 - 3 a c) > 0, c = (1-s^2)/(3a), dc = -(2s/(3a)) ds, u = 27a^2:

    d_hi = K_p / u,   K_p = (s-1)^2 (2s+1)
    d_lo = -K_m / u,  K_m = (s+1)^2 (2s-1)          (K_p + K_m = 4 s^3)

    S_b = 2 * int_0^1 da (2/(3a)) int s * L(a,s) ds,
    L = max(0, min(d_hi,1) - max(d_lo,-1)).

The (a,s) domain is {0 < a < 1, |s^2-1|/3 <= a}, i.e. s in (0,2) and
a in [a0(s), 1] with a0 = |s^2-1|/3.  Swapping the order:

    S_b = (4/3) int_0^2 s F(s) ds,   F(s) = int_{a0}^1 L(a,s)/a da.

Two lemmas (proved by elementary algebra, checked numerically below):

 L1 (top never clips):  d_hi <= 1 on the whole domain, because
    alpha_p := sqrt(K_p/27) < a0(s) for every s in (0,2)
    [ (s-1)^2(2s+1)/27 < (s^2-1)^2/9  <=>  2s+1 < 3(s+1)^2, always true ].
    This is the b=1-face analogue of the never-clipped lemma of Theorem 1.

 L2 (bottom clips exactly on s in (2/3,2)):  alpha_m := sqrt(K_m/27) > a0
    <=>  2s-1 > 3(s-1)^2  <=>  (3s-2)(s-2) < 0  <=>  s in (2/3, 2);
    and alpha_m < 1 <=> (s+1)^2(2s-1) < 27 <=> s < 2.  (equality at s=2)

Hence, with 1/a0^2 = 9/(s^2-1)^2,

    s in (0, 2/3]:  F = (2 s^3/27)(1/a0^2 - 1)
    s in (2/3, 2):  F = K_p/(54 a0^2) + 1/2 + ln(alpha_m/a0) - 2 s^3/27

(the middle constant 1/2 is where -K_p/(2K_m) + 2s^3/K_m collapses, using
K_p + K_m = 4s^3; F is continuous at s = 2/3, value 0.96 -> checked below), and

    ln(alpha_m/a0) = (1/2) ln(2s-1) - (1/2) ln 3 - ln|s-1|.

Everything is elementary; sympy integrates it in closed form.

Output: results/face_exact.json
"""
import json
import os

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "face_exact.json")

s = sp.symbols("s", positive=True)


def build():
    Kp = (s - 1) ** 2 * (2 * s + 1)
    # piece 1: s in (0, 2/3),  a0 = (1-s^2)/3
    inv_a0sq = 9 / (s ** 2 - 1) ** 2
    F1 = sp.Rational(2, 27) * s ** 3 * (inv_a0sq - 1)
    # piece 2: s in (2/3, 2)
    log_ratio = sp.Rational(1, 2) * sp.log(2 * s - 1) \
        - sp.Rational(1, 2) * sp.log(3) - sp.log(sp.Abs(s - 1))
    F2 = Kp * inv_a0sq / 54 + sp.Rational(1, 2) + log_ratio \
        - sp.Rational(2, 27) * s ** 3
    return F1, F2


def main():
    F1, F2 = build()
    res = {}

    # continuity check at s = 2/3
    c1 = sp.simplify(F1.subs(s, sp.Rational(2, 3)))
    c2 = sp.simplify(F2.subs(s, sp.Rational(2, 3)))
    res["continuity_at_s_2_3"] = {"from_below": str(c1), "from_above": str(c2),
                                  "equal": bool(sp.simplify(c1 - c2) == 0)}
    print("continuity at s=2/3:", c1, c2, res["continuity_at_s_2_3"]["equal"])

    # ---- integrals.  On (2/3,2) the |s-1| splits at s=1.
    I1 = sp.integrate(sp.expand(s * F1), (s, 0, sp.Rational(2, 3)))
    F2a = F2.subs(sp.Abs(s - 1), 1 - s)          # 2/3 < s < 1
    F2b = F2.subs(sp.Abs(s - 1), s - 1)          # 1 < s < 2
    I2a = sp.integrate(sp.expand(s * F2a), (s, sp.Rational(2, 3), 1))
    I2b = sp.integrate(sp.expand(s * F2b), (s, 1, 2))

    Sb = sp.nsimplify(sp.Rational(4, 3) * (I1 + I2a + I2b))
    Sb = sp.simplify(sp.expand(sp.logcombine(sp.expand(Sb), force=True)))
    print("S_b exact =", Sb)
    print("S_b num   =", sp.N(Sb, 30))
    res["I1"] = str(sp.simplify(I1))
    res["I2a"] = str(sp.simplify(I2a))
    res["I2b"] = str(sp.simplify(I2b))
    res["S_b_exact"] = str(Sb)
    res["S_b_numeric"] = str(sp.N(Sb, 30))

    V1 = sp.Rational(766, 1215) + sp.log(3) / 6
    P = sp.simplify(sp.expand((V1 + Sb) / 16))
    P = sp.simplify(sp.logcombine(sp.expand(P), force=True))
    print("P exact =", P)
    print("P num   =", sp.N(P, 30))
    res["V1_exact"] = str(V1)
    res["P_exact"] = str(P)
    res["P_numeric"] = str(sp.N(P, 30))

    cand = sp.Rational(641, 2430) - sp.log(3) / 24
    diff = sp.simplify(sp.expand(P - cand))
    res["dxdy_candidate"] = str(cand)
    res["P_minus_dxdy_symbolic"] = str(diff)
    res["P_equals_dxdy"] = bool(diff == 0)
    print("P - (641/2430 - ln3/24) =", diff, " -> equal:", res["P_equals_dxdy"])
    print("sweep 0.217993225 diff  =", sp.N(P - sp.Float("0.217993225"), 12))
    res["P_minus_sweep_numeric"] = str(sp.N(P - sp.Float("0.217993225"), 12))

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print("written", os.path.abspath(OUT))


if __name__ == "__main__":
    main()
