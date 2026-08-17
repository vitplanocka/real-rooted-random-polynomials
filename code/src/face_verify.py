"""Independent checks of every step of the face-decomposition route.

1. The divergence/cone identity itself, tested EXACTLY on the quadratic
   analogue, where all three faces and the answer are known in closed form:
       vol_3{(p,q,r) in [-1,1]^3 : q^2 > 4pr} = (1/3)*2*(S_p + S_q + S_r)
   with S_p = S_r = 13/6, S_q = 5/2 + ln 2, and the exact volume
       8*(1/2 + 5/72 + ln2/12) = 4 + 5/9 + (2/3) ln 2.
2. F(s) closed form vs. brute-force numerical  int_{a0}^1 L(a,s)/a da.
3. Lemmas L1 / L2 (never-clipped-above; clipping window s in (2/3,2)) by scan.
4. S_b exact vs. brute-force 2D quadrature.
5. S_c (the c=1 face) numerically vs. S_b -- tests the reversal symmetry
   S_b = S_c that the decomposition uses.
6. PSLQ identification of the numeric S_b.

Output: results/face_verify.json
"""
import json
import os

import numpy as np
import sympy as sp
import mpmath as mp
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "face_verify.json")
mp.mp.dps = 30

res = {}

# ---------------------------------------------------------------- 1. cone id
print("=== 1. divergence/cone identity on the quadratic analogue ===")
p, q, r = sp.symbols("p q r", real=True)
# S_p = area{(q,r) in [-1,1]^2 : q^2 > 4 r} = int_{-1}^1 (min(1,q^2/4)+1) dq
S_p = sp.integrate(1 + q ** 2 / 4, (q, -1, 1))
S_r = S_p
# S_q = area{(p,r) in [-1,1]^2 : 1 > 4 p r}
S_q = 4 - 2 * sp.integrate(1 - 1 / (4 * p), (p, sp.Rational(1, 4), 1))
vol_faces = sp.Rational(1, 3) * 2 * (S_p + S_q + S_r)
vol_exact = 8 * (sp.Rational(1, 2) + sp.Rational(5, 72) + sp.log(2) / 12)
ok1 = sp.simplify(vol_faces - vol_exact) == 0
print(f"  S_p = S_r = {S_p},  S_q = {sp.simplify(S_q)}")
print(f"  faces  -> {sp.simplify(vol_faces)} = {sp.N(vol_faces, 20)}")
print(f"  direct -> {sp.simplify(vol_exact)} = {sp.N(vol_exact, 20)}")
print(f"  IDENTITY EXACT MATCH: {ok1}")
res["cone_identity_quadratic_analogue"] = {
    "S_p": str(S_p), "S_q": str(sp.simplify(S_q)),
    "from_faces": str(sp.simplify(vol_faces)),
    "direct": str(sp.simplify(vol_exact)), "exact_match": bool(ok1)}

# ---------------------------------------------------------------- 2. F(s)
print("=== 2. F(s) closed form vs brute force ===")


def L_of(a, s):
    u = 27.0 * a * a
    d_hi = (s - 1.0) ** 2 * (2 * s + 1.0) / u
    d_lo = -((s + 1.0) ** 2 * (2 * s - 1.0)) / u
    return max(0.0, min(d_hi, 1.0) - max(d_lo, -1.0))


def F_brute(s):
    a0 = abs(s * s - 1.0) / 3.0
    v, _ = quad(lambda a: L_of(a, s) / a, a0, 1.0, limit=800,
                epsabs=1e-14, epsrel=1e-13, points=None)
    return v


def F_closed(s, ctx=None):
    """closed form; the s -> 1 removable part K_p/a0^2 = 9(2s+1)/(s+1)^2 is
    written in its cancelled form so that s = 1 is safe."""
    lg, ab = (np.log, abs) if ctx is None else (ctx.log, ctx.fabs)
    one = 1.0 if ctx is None else ctx.mpf(1)
    if s <= (2 * one) / 3:
        # (2/27) s^3 (9/(s^2-1)^2 - 1)
        return (2 * one / 27) * s ** 3 * (9 / (s * s - 1) ** 2 - 1)
    Kp_over_a0sq = 9 * (2 * s + 1) / (s + 1) ** 2
    lr = lg(2 * s - 1) / 2 - lg(3 * one) / 2 - lg(ab(s - 1))
    return Kp_over_a0sq / 54 + one / 2 + lr - (2 * one / 27) * s ** 3


f_tab = []
worst = 0.0
for s in (0.05, 0.2, 0.4, 0.6, 0.66, 0.7, 0.8, 0.95, 1.05, 1.2, 1.5, 1.8, 1.99):
    fb, fc = F_brute(s), F_closed(s)
    worst = max(worst, abs(fb - fc))
    f_tab.append({"s": s, "brute": fb, "closed": fc, "diff": fb - fc})
    print(f"  s={s:5.2f}  brute={fb:.12f}  closed={fc:.12f}  diff={fb-fc:+.2e}")
res["F_of_s_check"] = {"table": f_tab, "max_abs_diff": worst}

# ---------------------------------------------------------------- 3. lemmas
print("=== 3. lemmas L1 / L2 by scan ===")
ss = np.linspace(1e-6, 2 - 1e-9, 2000001)
a0 = np.abs(ss ** 2 - 1) / 3
alpha_p = np.sqrt((ss - 1) ** 2 * (2 * ss + 1) / 27)
Km = (ss + 1) ** 2 * (2 * ss - 1)
L1_ok = bool(np.all(alpha_p < a0))
L1_margin = float(np.min(a0 - alpha_p))
clip = (Km > 0) & (np.sqrt(np.maximum(Km, 0) / 27) > a0)
lo_edge = float(ss[clip].min()) if clip.any() else None
hi_edge = float(ss[clip].max()) if clip.any() else None
alpha_m_max = float(np.sqrt(max(Km.max(), 0) / 27))
print(f"  L1 alpha_p < a0 everywhere: {L1_ok}  (min gap {L1_margin:.3e})")
print(f"  L2 clipping window: s in [{lo_edge:.10f}, {hi_edge:.10f}]"
      f"  (claim 2/3={2/3:.10f} .. 2)")
print(f"  max alpha_m on the range = {alpha_m_max:.12f}  (claim <= 1)")
res["lemmas"] = {"L1_holds": L1_ok, "L1_min_gap": L1_margin,
                 "L2_clip_lo": lo_edge, "L2_clip_hi": hi_edge,
                 "L2_claim_lo": 2 / 3, "alpha_m_max": alpha_m_max}

# ---------------------------------------------------------------- 4. S_b
print("=== 4. S_b exact vs brute force ===")
Sb_exact = mp.mpf(1454) / 405 - 5 * mp.log(3) / 6
Sb_int = mp.mpf(4) / 3 * mp.quad(
    lambda s: s * F_closed(s, ctx=mp),
    [0, mp.mpf(2) / 3, 1, 2])


def Sb_inner(a):
    u = 27.0 * a * a
    s_lo = np.sqrt(max(0.0, 1.0 - 3.0 * a))
    s_hi = np.sqrt(1.0 + 3.0 * a)

    def f(s):
        d_hi = (s - 1.0) ** 2 * (2 * s + 1.0) / u
        d_lo = -((s + 1.0) ** 2 * (2 * s - 1.0)) / u
        return (2.0 / (3.0 * a)) * s * max(0.0, min(d_hi, 1.0)
                                           - max(d_lo, -1.0))
    v, _ = quad(f, s_lo, s_hi, limit=600, epsabs=1e-14, epsrel=1e-13)
    return v


Sb_brute = 2 * quad(Sb_inner, 0.0, 1.0, limit=600,
                    epsabs=1e-13, epsrel=1e-12)[0]
print(f"  S_b exact (1454/405 - 5ln3/6) = {mp.nstr(Sb_exact, 22)}")
print(f"  S_b from F(s) quadrature      = {mp.nstr(Sb_int, 22)}"
      f"   diff {mp.nstr(Sb_int - Sb_exact, 4)}")
print(f"  S_b brute 2D (a,s) quadrature = {Sb_brute:.16f}"
      f"   diff {Sb_brute - float(Sb_exact):+.2e}")
res["S_b"] = {"exact": mp.nstr(Sb_exact, 25),
              "from_F_quadrature": mp.nstr(Sb_int, 25),
              "diff_F": mp.nstr(Sb_int - Sb_exact, 5),
              "brute_2d": Sb_brute, "diff_brute": Sb_brute - float(Sb_exact)}

# ---------------------------------------------------------------- 5. S_c
print("=== 5. S_c (c=1 face) vs S_b -- reversal symmetry check ===")
# a x^3 + b x^2 + x + d ; sigma^2 = b^2 - 3a ; band formula is sign(a)-agnostic
# symmetry (a,b,d) -> (a,-b,-d)  =>  integrate b in [0,1] and double


def Sc_inner(b):
    # a ranges over [-1, min(1, b^2/3)]
    a_hi = min(1.0, b * b / 3.0)

    def f(a):
        if a == 0.0:
            return 0.0
        s = np.sqrt(max(b * b - 3.0 * a, 0.0))
        u = 27.0 * a * a
        hi = (b - s) ** 2 * (b + 2 * s) / u
        lo = (b + s) ** 2 * (b - 2 * s) / u
        return max(0.0, min(hi, 1.0) - max(lo, -1.0))
    v1, _ = quad(f, -1.0, 0.0, limit=600, epsabs=1e-13, epsrel=1e-12)
    v2, _ = quad(f, 0.0, a_hi, limit=600, epsabs=1e-13, epsrel=1e-12)
    return v1 + v2


Sc = 2 * quad(Sc_inner, 0.0, 1.0, limit=400, epsabs=1e-11, epsrel=1e-10)[0]
print(f"  S_c = {Sc:.14f}   S_b = {float(Sb_exact):.14f}   "
      f"diff {Sc - float(Sb_exact):+.2e}")
res["S_c_vs_S_b"] = {"S_c_numeric": Sc, "S_b_exact": float(Sb_exact),
                     "diff": Sc - float(Sb_exact)}

# ---------------------------------------------------------------- 6. PSLQ
print("=== 6. PSLQ on the numeric S_b and P ===")
mp.mp.dps = 25
ident = {}
for name, val in (("S_b", Sb_int), ("P", (mp.mpf(766) / 1215
                                          + mp.log(3) / 6 + Sb_int) / 16)):
    basis = [val, mp.mpf(1), mp.log(3), mp.log(2), mp.pi, mp.sqrt(3)]
    rel = mp.pslq(basis, maxcoeff=10 ** 8, maxsteps=10 ** 5, tol=mp.mpf(10) ** -18)
    ident[name] = {"value": mp.nstr(val, 22), "pslq": None if rel is None
                   else [int(z) for z in rel],
                   "basis": ["target", "1", "log3", "log2", "pi", "sqrt3"]}
    print(f"  {name}: {mp.nstr(val, 22)}  pslq -> {ident[name]['pslq']}")
res["pslq"] = ident

os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w") as fh:
    json.dump(res, fh, indent=2, default=str)
print("written", os.path.abspath(OUT))
