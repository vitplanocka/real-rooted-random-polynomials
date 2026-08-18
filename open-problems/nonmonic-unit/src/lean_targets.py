"""Exact targets for the Lean proof of vol(FaceB0) = 479/960 - (2/3) log 2.

Route chosen for Lean (Theorem2.lean-style, NOT Theorem3Proof-style):
  vol(FaceB0) = int_0^1 A(a) da,  A(a) = area of the (c,d)-slice at fixed a
              = int_0^{cmax a} (dHi(a,c) - max(dLo(a,c),0)) dc,  cmax a = min 1 (1/(3a)).
The integrand in c is a polynomial in (1-3ac) and (1-3ac)^{3/2}, so the inner
integral is ELEMENTARY (no substitution needed).  Cases in a: a<=1/4, 1/4<=a<=1/3, a>=1/3.
"""
import sympy as sp

a, c, u, d = sp.symbols('a c u d', positive=True)

r = sp.sqrt(1 - 3*a*c)
Kp = (r-1)**2*(2*r+1)          # = 2 r^3 - 3 r^2 + 1
Km = (r+1)**2*(2*r-1)
dHi = Kp/(27*a**2)
dLo = -Km/(27*a**2)

print("Kp expanded in (1-3ac):", sp.simplify(sp.expand(Kp) - (2*(1-3*a*c)**sp.Rational(3,2) - 3*(1-3*a*c) + 1)))
print("Kp+Km-4r^3:", sp.simplify(Kp + Km - 4*r**3))

# integrands
IclipL = sp.expand(2*(1-3*a*c)**sp.Rational(3,2) - 3*(1-3*a*c) + 1)   # clipped: L = Kp/(27a^2)
Ifull  = 4*(1-3*a*c)**sp.Rational(3,2)                                # unclipped: L = 4r^3/(27a^2)

def A_of(lo, hi, expr):
    return sp.integrate(expr, (c, lo, hi))

cstar = 1/(4*a)
# --- case a <= 1/4 : cmax = 1, no unclipped part (ac <= 1/4 everywhere)
A1 = sp.simplify(A_of(0, 1, IclipL)/(27*a**2))
# --- case 1/4 <= a <= 1/3 : cmax = 1, split at c* = 1/(4a)
A2 = sp.simplify((A_of(0, cstar, IclipL) + A_of(cstar, 1, Ifull))/(27*a**2))
# --- case a >= 1/3 : cmax = 1/(3a), split at c*
A3 = sp.simplify((A_of(0, cstar, IclipL) + A_of(cstar, 1/(3*a), Ifull))/(27*a**2))
print("\nA1 (a<=1/4)  =", sp.simplify(A1))
print("A2 (1/4..1/3)=", sp.simplify(A2))
print("A3 (a>=1/3)  =", sp.simplify(A3))

# hand-derived closed forms -- check they match
A1h = (sp.Rational(4,15)/a*(1-(1-3*a)**sp.Rational(5,2)) - 2 + sp.Rational(9,2)*a)/(27*a**2)
A2h = (sp.Rational(9,160) - sp.Rational(8,15)*(1-3*a)**sp.Rational(5,2))/(27*a**3)
A3h = 1/(480*a**3)
for nm,x,y in (("A1",A1,A1h),("A2",A2,A2h),("A3",A3,A3h)):
    print(f"  {nm} matches hand form:", sp.simplify(sp.expand(x-y))==0)

# --- outer integral, by pieces
I3 = sp.integrate(A3h, (a, sp.Rational(1,3), 1))
print("\nI3 = int_{1/3}^1 A3 =", I3)

# pieces 1 and 2 via u = sqrt(1-3a)  (a = (1-u^2)/3, da = -(2u/3) du)
sub = lambda e: sp.simplify(e.subs(a, (1-u**2)/3))
f1 = sp.cancel(sp.simplify(sub(A1h)*sp.Rational(2,3)*u))   # integrand in u on [1/2,1] (orientation flipped)
f2 = sp.cancel(sp.simplify(sub(A2h)*sp.Rational(2,3)*u))   # integrand in u on [0,1/2]
print("f1(u) =", f1)
print("f2(u) =", f2)
I1 = sp.integrate(f1, (u, sp.Rational(1,2), 1))
I2 = sp.integrate(f2, (u, 0, sp.Rational(1,2)))
print("I1 = int_{1/2}^1 f1 =", sp.simplify(I1))
print("I2 = int_0^{1/2} f2 =", sp.simplify(I2))
S = sp.simplify(sp.logcombine(sp.expand(I1+I2+I3), force=True))
print("\nS = I1+I2+I3 =", S, "=", sp.N(S,25))
print("target 479/960-(2/3)log2 :", sp.simplify(S - (sp.Rational(479,960) - sp.Rational(2,3)*sp.log(2))) == 0)

# antiderivatives in u (for the Lean HasDerivAt lemmas)
print("\nantiderivative of f1:", sp.simplify(sp.integrate(f1, u)))
print("antiderivative of f2:", sp.simplify(sp.integrate(f2, u)))
