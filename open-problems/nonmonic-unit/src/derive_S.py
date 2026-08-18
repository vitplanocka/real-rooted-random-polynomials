"""Derivation of S = F_b = vol_3{(a,c,d) in [0,1]^3 : a x^3 + x^2 + c x + d has 3 real roots}.

SET-UP (re-derived from scratch, every step checked below in exact arithmetic).

f(x) = a x^3 + x^2 + c x + d,  a,c,d in [0,1],  a > 0.
f'(x) = 3a x^2 + 2x + c has two distinct real roots iff 1 - 3ac > 0.
Put s = sqrt(1 - 3ac).  Since a,c in [0,1] we have ac >= 0, hence s in (0,1].
Critical points  x_- = -(1+s)/(3a) (local max) < x_+ = (s-1)/(3a) <= 0 (local min).
With g(x) = a x^3 + x^2 + c x (so f = g + d) and c = (1-s^2)/(3a), u = 27 a^2:

    d_hi := -g(x_+) =  K_p/u,   K_p = (s-1)^2 (2s+1) >= 0
    d_lo := -g(x_-) = -K_m/u,   K_m = (s+1)^2 (2s-1)
    K_p + K_m = 4 s^3          (band width 4s^3/u)

3 real roots  <=>  f(x_-) >= 0 >= f(x_+)  <=>  d in [d_lo, d_hi].

DOMAIN: c = (1-s^2)/(3a) in [0,1] <=> s <= 1 and a >= a0(s) := (1-s^2)/3 (<= 1/3).
Jacobian: at fixed a, dc = -(2s/(3a)) ds.

CLIPPING against the window d in [0,1]:
  (L1) top never clips: d_hi < 1 on the whole domain, because alpha_p := sqrt(K_p/27) < a0(s):
       (s-1)^2(2s+1)/27 < (1-s^2)^2/9  <=>  2s+1 < 3(1+s)^2, true for all s >= 0.
  (L2) bottom clips exactly when K_m > 0, i.e. s > 1/2 (then d_lo < 0 -> replaced by 0);
       for s < 1/2, K_m < 0 so 0 < d_lo < d_hi < 1 and the band is entirely inside the window.
Hence with C(s) := K_p + min(K_m, 0):
       L(a,s) = C(s)/(27 a^2),   C(s) = 4 s^3 (s <= 1/2),  C(s) = (s-1)^2(2s+1) (s >= 1/2).

    S = int_0^1 da int L (2s/(3a)) ds = (2/3) int_0^1 s F(s) ds,
    F(s) = int_{a0(s)}^1 L(a,s)/a da = C(s)/54 * (1/a0(s)^2 - 1),  1/a0^2 = 9/(1-s^2)^2.
The (s-1)^2 in K_p cancels the (1-s)^-2 pole, so the integrand is RATIONAL in s.
"""
import sympy as sp

s, a, c, d, x = sp.symbols('s a c d x', real=True)

def main():
    ok = True
    def check(name, cond):
        nonlocal ok
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}")
        ok = ok and bool(cond)

    print("=== exact algebraic identities ===")
    A, C = sp.symbols('A C', positive=True)      # a, c generic positive
    ss = sp.sqrt(1 - 3*A*C)
    g = A*x**3 + x**2 + C*x
    xm = -(1 + ss)/(3*A); xp = (ss - 1)/(3*A)
    fp = sp.diff(A*x**3 + x**2 + C*x + d, x)
    check("x_- is a critical point", sp.simplify(fp.subs(x, xm)) == 0)
    check("x_+ is a critical point", sp.simplify(fp.subs(x, xp)) == 0)
    u = 27*A**2
    Kp = (s-1)**2*(2*s+1); Km = (s+1)**2*(2*s-1)
    # substitute c = (1-s^2)/(3a) so that sqrt(1-3ac) = s
    subC = {C: (1-s**2)/(3*A)}
    sss = sp.sqrt(sp.simplify((1-3*A*C).subs(subC)))     # = sqrt(s^2)
    check("s^2 = 1-3ac under c=(1-s^2)/(3a)", sp.simplify((1-3*A*C).subs(subC) - s**2) == 0)
    xm_s = -(1+s)/(3*A); xp_s = (s-1)/(3*A)
    g_s = (A*x**3 + x**2 + ((1-s**2)/(3*A))*x)
    check("d_hi = K_p/(27a^2)", sp.simplify(-g_s.subs(x, xp_s) - Kp/u) == 0)
    check("d_lo = -K_m/(27a^2)", sp.simplify(-g_s.subs(x, xm_s) + Km/u) == 0)
    check("K_p + K_m = 4 s^3", sp.expand(Kp + Km - 4*s**3) == 0)
    # discriminant factorisation in d  (analogue of identity S2)
    Delta = 18*A*1*C*d - 4*1**3*d + 1**2*C**2 - 4*A*C**3 - 27*A**2*d**2
    dhi = Kp/u; dlo = -Km/u
    check("Delta = -27 a^2 (d-d_lo)(d-d_hi)",
          sp.simplify(sp.expand(Delta.subs(subC) + 27*A**2*(d-dlo)*(d-dhi))) == 0)
    # never-clip-above lemma
    a0 = (1-s**2)/3
    check("L1: K_p/27 < a0^2 on 0<s<1",
          sp.simplify(sp.factor(sp.expand(a0**2 - Kp/27))) is not None and
          all(sp.expand(a0**2 - Kp/27).subs(s, sp.Rational(k,20)) > 0 for k in range(1,20)))
    print("   a0^2 - K_p/27 factored:", sp.factor(sp.expand(a0**2 - Kp/27)))
    # 3(1+s)^2 - (2s+1) > 0 is the clean statement
    print("   3(1+s)^2-(2s+1) =", sp.expand(3*(1+s)**2 - (2*s+1)), "(positive for s>=0)")
    check("L2: K_m sign flips exactly at s=1/2 on (0,1)",
          sorted(sp.solve(sp.Eq(Km, 0), s)) == [-1, sp.Rational(1,2)]
          and all(Km.subs(s, sp.Rational(k,100)) < 0 for k in range(1,50))
          and all(Km.subs(s, sp.Rational(k,100)) > 0 for k in range(51,100)))

    print("\n=== the s-integral ===")
    inv_a0sq = 9/(1-s**2)**2
    F_low  = sp.Rational(1,54)*(4*s**3)*(inv_a0sq - 1)     # s in (0,1/2)
    F_high = sp.Rational(1,54)*Kp*(inv_a0sq - 1)           # s in (1/2,1)
    print("  F_low  =", sp.simplify(F_low))
    print("  F_high =", sp.simplify(sp.cancel(F_high)))
    check("F continuous at s=1/2",
          sp.simplify(F_low.subs(s, sp.Rational(1,2)) - F_high.subs(s, sp.Rational(1,2))) == 0)
    lim = sp.limit(s*F_high, s, 1, '-')
    print("  lim_{s->1-} s*F_high =", lim, " (finite: pole cancels)")

    I1 = sp.integrate(sp.cancel(s*F_low),  (s, 0, sp.Rational(1,2)))
    I2 = sp.integrate(sp.cancel(s*F_high), (s, sp.Rational(1,2), 1))
    print("  I1 =", sp.simplify(I1))
    print("  I2 =", sp.simplify(I2))
    S = sp.Rational(2,3)*(I1 + I2)
    S = sp.simplify(sp.logcombine(sp.expand(S), force=True))
    print("\nS exact   =", S)
    print("S numeric =", sp.N(S, 30))
    P = sp.Rational(1,5760) + S/2
    P = sp.simplify(sp.logcombine(sp.expand(P), force=True))
    print("P = 1/5760 + S/2 =", P)
    print("P numeric        =", sp.N(P, 30))
    print("\nMC target        = 1.8603554e-02 +/- 3.0e-06")
    print("P - MC           =", sp.N(P - sp.Float('0.018603554'), 10))
    print("\nALL IDENTITY CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
    return S, P

if __name__ == '__main__':
    main()
