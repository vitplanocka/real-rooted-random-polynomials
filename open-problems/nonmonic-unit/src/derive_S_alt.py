"""SECOND, INDEPENDENT symbolic derivation of S, in the OPPOSITE integration order.

derive_S.py integrates a first (at fixed s) and then s.  Here we integrate the
leading coefficient a first AT FIXED c, then c -- different limits, different
antiderivatives, different special values.  Agreement of the two closed forms is a
genuine cross-check of the case analysis, not a re-run of it.

At fixed c in (0,1], put r = sqrt(1-3ac) (so a = (1-r^2)/(3c), da = -2r dr/(3c)).
  a in (0, min(1, 1/(3c)))  <->  r in (r_lo(c), 1),  r_lo(c) = sqrt(max(0, 1-3c)).
  bottom-clip boundary ac = 1/4  <->  r = 1/2.
  L = C(r)/(27 a^2),  C = K_p = (r-1)^2(2r+1) for r > 1/2,  C = 4r^3 for r < 1/2.
  L da = (2c/9) * C(r) * r/(1-r^2)^2 dr.
Note K_p(r) r/(1-r^2)^2 = r(2r+1)/(1+r)^2 -- regular on [0,1].
  r_lo(c) < 1/2  <=>  c > 1/4.
"""
import sympy as sp

r, c = sp.symbols('r c', positive=True)

def main():
    Kp = (r-1)**2*(2*r+1)
    intg_hi = sp.cancel(Kp*r/(1-r**2)**2)          # r > 1/2 branch
    intg_lo = sp.cancel(4*r**3*r/(1-r**2)**2)      # r < 1/2 branch
    print("K_p * r/(1-r^2)^2 =", intg_hi)
    A_hi = sp.integrate(intg_hi, r)                # antiderivatives
    A_lo = sp.integrate(intg_lo, r)
    print("antiderivative (hi):", sp.simplify(A_hi))
    print("antiderivative (lo):", sp.simplify(A_lo))

    rl = sp.symbols('rl', nonnegative=True)        # r_lo
    # inner integral as a function of r_lo
    inner_upper = sp.simplify(A_hi.subs(r, 1) - A_hi.subs(r, rl))          # r_lo > 1/2
    half = sp.Rational(1, 2)
    inner_lower = sp.simplify((A_hi.subs(r, 1) - A_hi.subs(r, half))
                              + (A_lo.subs(r, half) - A_lo.subs(r, rl)))   # r_lo < 1/2
    print("inner (r_lo>1/2):", inner_upper)
    print("inner (r_lo<1/2):", sp.simplify(inner_lower))

    # ---- c in (0,1/4): r_lo = sqrt(1-3c) in (1/2,1).  substitute c = (1-rl^2)/3,
    # dc = -(2 rl/3) drl ; c: 0->1/4 corresponds to rl: 1->1/2.
    cc = (1 - rl**2)/3
    w = sp.Rational(2, 9)*cc*inner_upper*(sp.Rational(2, 3)*rl)   # (2c/9)*inner*|dc/drl|
    J1 = sp.integrate(sp.cancel(sp.expand(w)), (rl, half, 1))
    print("J1 (c in (0,1/4))  =", sp.simplify(J1))

    # ---- c in (1/4,1/3): r_lo = sqrt(1-3c) in (0,1/2)
    w2 = sp.Rational(2, 9)*cc*inner_lower*(sp.Rational(2, 3)*rl)
    J2 = sp.integrate(sp.cancel(sp.expand(w2)), (rl, 0, half))
    print("J2 (c in (1/4,1/3))=", sp.simplify(J2))

    # ---- c in (1/3,1): r_lo = 0 (a runs up to 1/(3c) < 1), integrand indep. of c
    J3 = sp.integrate(sp.Rational(2, 9)*c*inner_lower.subs(rl, 0), (c, sp.Rational(1, 3), 1))
    print("J3 (c in (1/3,1))  =", sp.simplify(J3))

    S_alt = sp.simplify(sp.logcombine(sp.expand(J1 + J2 + J3), force=True))
    print("\nS (alt route) =", S_alt)
    print("S numeric     =", sp.N(S_alt, 30))
    S_ref = sp.Rational(479, 960) - sp.Rational(2, 3)*sp.log(2)
    diff = sp.simplify(sp.expand(S_alt - S_ref))
    print("S_alt - (479/960 - (2/3)ln2) =", diff, " -> equal:", diff == 0)
    P = sp.simplify(sp.logcombine(sp.expand(sp.Rational(1, 5760) + S_alt/2), force=True))
    print("P = 1/5760 + S/2 =", P, "=", sp.N(P, 30))

if __name__ == '__main__':
    main()
