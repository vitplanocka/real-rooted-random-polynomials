"""Exact anchor values for the real-rooted random polynomial project.

Derives, in exact arithmetic (sympy), the classical closed forms that our
Monte Carlo and quadrature machinery must reproduce, plus the structural
identities the monic-cubic reduction rests on.

Anchors:
  A1. Depressed cubic x^3 + p x + q, (p,q) iid U[-1,1]:
        P(3 real roots) = 2*sqrt(3)/45  ~ 0.0684
  A2. Monic quadratic x^2 + b x + c, (b,c) iid U[-1,1]:
        P(real roots) = 13/24
  A3. Full quadratic a x^2 + b x + c, iid U[-1,1]:
        P(real roots) = 41/72 + log(2)/12  ~ 0.627
  A4. Full quadratic, iid U[0,1]:
        P(real roots) = 5/36 + log(2)/6  ~ 0.2544134190  (D'Aurizio)

Structural identities (foundation of reduce_monic.py):
  S1. For f = x^3 + a x^2 + b x + c with s = sqrt(a^2-3b) (b < a^2/3),
      critical points x_mp = (-a -+ s)/3, and g(x) = x^3 + a x^2 + b x:
        c_lo = -g(x_minus),  c_hi = -g(x_plus)
        c_hi - c_lo = (4/27) s^3
  S2. Disc_x(f) = -27*(c - c_lo)*(c - c_hi)   (as polynomials in c)
      hence  Disc >= 0  <=>  c in [c_lo, c_hi]   (for b < a^2/3).
  S3. Unclipped main term W = Int_{[-1,1]} Int_{-1}^{a^2/3} (4/27) s^3 db da
      in closed form (upper bound scaffold for the clipped volume).

Output: results/exact_anchors.json
"""
import json
import os

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "exact_anchors.json")

results = {}


def record(key, expr, expected=None, note=""):
    expr = sp.nsimplify(sp.simplify(expr))
    val = sp.N(expr, 30)
    ok = None
    if expected is not None:
        ok = sp.simplify(expr - expected) == 0
    results[key] = {
        "exact": str(expr),
        "value_30dps": str(val),
        "matches_expected": ok,
        "note": note,
    }
    print(f"{key:24s} = {expr}  ~ {sp.N(expr, 20)}"
          + ("" if ok is None else f"   [expected match: {ok}]"))


p, q, a, b, c, x, u, v = sp.symbols("p q a b c x u v", real=True)

# ---------------------------------------------------------------- A1
# Depressed cubic: 3 real roots <=> 4p^3 + 27q^2 <= 0, i.e. p <= 0 and
# |q| <= 2(-p/3)^{3/2}.  Band width (4/27)(-3p)^{3/2} < 1 on p in [-1,0],
# so the band is never clipped by the window [-1,1].
width_dep = sp.Rational(4, 27) * (-3 * p) ** sp.Rational(3, 2)
area_dep = sp.integrate(width_dep, (p, -1, 0))
record("A1_depressed_cubic", area_dep / 4, 2 * sp.sqrt(3) / 45,
       "P(3 real roots), x^3+px+q, (p,q) iid U[-1,1]")

# ---------------------------------------------------------------- A2
# Monic quadratic: real roots <=> c <= b^2/4; c-window [-1,1].
P_A2 = sp.integrate(sp.Min(1, b**2 / 4) - (-1), (b, -1, 1)) / 4
record("A2_monic_quadratic", P_A2, sp.Rational(13, 24),
       "P(real roots), x^2+bx+c, (b,c) iid U[-1,1]")

# ---------------------------------------------------------------- A3
# Full quadratic iid U[-1,1]: P(b^2 >= 4ac).
# P(ac <= 0) = 1/2 (then always real).  Conditioned on ac > 0 (prob 1/2),
# (|a|,|c|) =: (u,v) iid U(0,1) and P_b(|b| >= 2 sqrt(uv)) = (1-2 sqrt(uv))^+.
J = (sp.integrate(sp.integrate(1 - 2 * sp.sqrt(u * v), (u, 0, 1)),
                  (v, 0, sp.Rational(1, 4)))
     + sp.integrate(sp.integrate(1 - 2 * sp.sqrt(u * v),
                                 (u, 0, 1 / (4 * v))),
                    (v, sp.Rational(1, 4), 1)))
P_A3 = sp.Rational(1, 2) + J / 2
record("A3_full_quadratic_sym", P_A3,
       sp.Rational(41, 72) + sp.log(2) / 12,
       "P(real roots), ax^2+bx+c iid U[-1,1]")

# ---------------------------------------------------------------- A4
# Full quadratic iid U[0,1]: P(b^2 >= 4ac) = Int_0^1 P(ac <= b^2/4) db,
# with P(uv <= t) = t - t log t for t in (0,1].
t = b**2 / 4
P_A4 = sp.integrate(t * (1 - sp.log(t)), (b, 0, 1))
record("A4_full_quadratic_unit", P_A4,
       sp.Rational(5, 36) + sp.log(2) / 6,
       "P(real roots), ax^2+bx+c iid U[0,1] (D'Aurizio ~0.2544134190)")

# ---------------------------------------------------------------- S1/S2
# The c-band reduction for the monic cubic.
s = sp.sqrt(a**2 - 3 * b)
xm = (-a - s) / 3          # local max of f (leading coeff > 0)
xp = (-a + s) / 3          # local min
g = x**3 + a * x**2 + b * x
c_lo = -g.subs(x, xm)
c_hi = -g.subs(x, xp)

band_width = sp.simplify(sp.expand(c_hi - c_lo))
s1_ok = sp.simplify(band_width - sp.Rational(4, 27) * s**3) == 0
print(f"S1  c_hi - c_lo = (4/27) s^3 :  {s1_ok}")
results["S1_band_width"] = {"holds": s1_ok,
                            "band_width": str(band_width)}

f = x**3 + a * x**2 + b * x + c
disc = sp.discriminant(f, x)
s2_diff = sp.simplify(sp.expand(disc - (-27) * (c - c_lo) * (c - c_hi)))
s2_ok = s2_diff == 0
print(f"S2  Disc = -27 (c - c_lo)(c - c_hi) :  {s2_ok}")
results["S2_disc_factorization"] = {
    "holds": s2_ok,
    "disc": str(sp.expand(disc)),
    "note": "Disc>=0 <=> c in [c_lo, c_hi] when b < a^2/3; "
            "when b > a^2/3 the roots c_lo,c_hi are complex and Disc<0.",
}

# Explicit c_lo, c_hi for the numeric pipeline (documented reference):
results["S1_c_band"] = {
    "c_lo": str(sp.simplify(c_lo)),
    "c_hi": str(sp.simplify(c_hi)),
}
print(f"    c_lo = {sp.simplify(c_lo)}")
print(f"    c_hi = {sp.simplify(c_hi)}")

# ---------------------------------------------------------------- S3
# Unclipped main term (upper bound for the clipped favourable volume):
W_inner = sp.integrate(sp.Rational(4, 27) * (a**2 - 3 * b) ** sp.Rational(3, 2),
                       (b, -1, a**2 / 3))
W = sp.integrate(W_inner, (a, -1, 1))
W = sp.simplify(W)
record("S3_unclipped_main_term", W, None,
       "Int of full band width over (a,b) in [-1,1]x[-1,a^2/3]; "
       "favourable volume <= this; P_upper_bound = W/8")
results["S3_upper_bound_P"] = {
    "exact": str(sp.simplify(W / 8)),
    "value_30dps": str(sp.N(W / 8, 30)),
}
print(f"S3  P(monic cubic) <= W/8 = {sp.N(W / 8, 20)}  (unclipped upper bound)")

# ---------------------------------------------------------------- quartic disc
# Reference: discriminant and auxiliary quantities for x^4+ax^3+bx^2+cx+d
# (used by mc_engine.py's all-real-roots test: Disc>0 & P<0 & D<0).
d4 = sp.Symbol("d", real=True)
f4 = x**4 + a * x**3 + b * x**2 + c * x + d4
disc4 = sp.expand(sp.discriminant(f4, x))
results["quartic_discriminant"] = {"expr": str(disc4)}
print("quartic discriminant computed (see JSON)")

os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w") as fh:
    json.dump(results, fh, indent=2)
print(f"\nwritten: {os.path.abspath(OUT)}")
