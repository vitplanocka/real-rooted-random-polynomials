"""Exact constants for the Lean file Face4B.lean.

Route: for a>0, Δ₃ 1 (a c) (a² d) = a² Δ₄ a 1 c d, so the face b=1 problem is the
MONIC problem with (b,c) -> (ac, a²d).  Hence the (c,d)-slice area at fixed a is
   sliceB a = (1/a³) * ∫_0^{min(a,1/3)} (cHi 1 - max(cLo 1, 0)) dB
with cHi 1 B = (9B - 2 + 2(1-3B)^{3/2})/27, cLo 1 B = (9B - 2 - 2(1-3B)^{3/2})/27.
"""
import sympy as sp
B, a, u = sp.symbols('B a u', nonnegative=True)

p32 = lambda x: x*sp.sqrt(x)
p52 = lambda x: x**2*sp.sqrt(x)
cHi1 = (9*B - 2 + 2*p32(1-3*B))/27
cLo1 = (9*B - 2 - 2*p32(1-3*B))/27

print("cHi1-cLo1 - 4/27 p32(1-3B):", sp.simplify(cHi1-cLo1 - sp.Rational(4,27)*p32(1-3*B)))
print("cLo1 <= 0 boundary  (cLo1=0 at B=?):", sp.solve(sp.Eq(sp.simplify(cLo1),0), B))

# G(B) = ∫_0^B (cHi1 - max(cLo1,0)) dB'
G_low  = sp.integrate(cHi1, (B, 0, a))                      # a <= 1/4  (cLo1 <= 0)
G_quarter = sp.simplify(G_low.subs(a, sp.Rational(1,4)))
G_high = sp.simplify(G_quarter + sp.integrate(sp.Rational(4,27)*p32(1-3*B), (B, sp.Rational(1,4), a)))
print("\nG(a) for a<=1/4 :", sp.simplify(G_low))
print("G(1/4)          :", G_quarter, "=", sp.nsimplify(G_quarter))
print("G(a) for 1/4..1/3:", sp.simplify(G_high))
print("G(1/3)          :", sp.simplify(G_high.subs(a, sp.Rational(1,3))), " (should be 1/480)")

# candidate Lean formulas
N1 = a**2/6 - 2*a/27 + sp.Rational(4,405) - sp.Rational(4,405)*p52(1-3*a)
N2 = sp.Rational(1,480) - sp.Rational(8,405)*p52(1-3*a)
print("\nLean N1 - G_low  :", sp.simplify(sp.expand(N1 - G_low)))
print("Lean N2 - G_high :", sp.simplify(sp.expand(N2 - G_high)))
print("continuity at a=1/4:", sp.simplify(N1.subs(a,sp.Rational(1,4)) - N2.subs(a,sp.Rational(1,4))))
print("N2 at a=1/3 :", sp.simplify(N2.subs(a,sp.Rational(1,3))), "(should be 1/480)")

# the u-forms (u = sqrt(1-3a), a = (1-u^2)/3)
sub = lambda e: sp.simplify(e.subs(a, (1-u**2)/3).rewrite(sp.Pow))
A1u = sp.simplify(sp.cancel(sp.simplify((N1/a**3).subs(a,(1-u**2)/3).subs(sp.sqrt((1-u**2)),0*u+sp.sqrt(1-u**2)))))
print("\n-- u-forms --")
A1u = sp.simplify(sp.cancel(((N1/a**3).subs(a,(1-u**2)/3)).subs(sp.sqrt(1-3*(1-u**2)/3), u)))
print("A1 in u :", sp.factor(sp.cancel(A1u)), " target (8u^2+9u+3)/(30(1+u)^3):",
      sp.simplify(sp.cancel(A1u - (8*u**2+9*u+3)/(30*(1+u)**3))))
A2u = sp.simplify(sp.cancel(((N2/a**3).subs(a,(1-u**2)/3)).subs(sp.sqrt(1-3*(1-u**2)/3), u)))
print("A2 in u :", sp.cancel(A2u), " target (9/160-(8/15)u^5)/(1-u^2)^3:",
      sp.simplify(sp.cancel(A2u - (sp.Rational(9,160)-sp.Rational(8,15)*u**5)/(1-u**2)**3)))

# antiderivatives (in a, via u)
R1 = -(8*u**3+16*u**2-u-8)/(45*(1+u)**2)
H1 = R1 + sp.log(1+u)/3
R2 = -((-1152*u**3+896*u+27)/(2880*(1-u**2)**2) + sp.Rational(16,45)*u)
H2 = R2 - (sp.log(1-u)-sp.log(1+u))/3
uu = sp.sqrt(1-3*a)
for nm, H, A in (("H1", H1, sp.cancel(A1u)), ("H2", H2, sp.cancel(A2u))):
    dH = sp.simplify(sp.diff(H.subs(u, uu), a))
    print(f"\nd{nm}/da - A (should be 0):", sp.simplify(sp.cancel(dH - A.subs(u, uu))))
print("\nH1(1/4)-H1(0) =", sp.simplify(H1.subs(u,sp.Rational(1,2)) - H1.subs(u,1)),
      "=", sp.N(H1.subs(u,sp.Rational(1,2)) - H1.subs(u,1),20))
print("H2(1/3)-H2(1/4) =", sp.simplify(H2.subs(u,0) - H2.subs(u,sp.Rational(1,2))),
      "=", sp.N(H2.subs(u,0) - H2.subs(u,sp.Rational(1,2)),20))
tot = sp.simplify(sp.logcombine(sp.expand(
    (H1.subs(u,sp.Rational(1,2)) - H1.subs(u,1)) + (H2.subs(u,0) - H2.subs(u,sp.Rational(1,2)))
    + sp.Rational(1,120)), force=True))
print("\nTOTAL S =", tot, "=", sp.N(tot,25))
print("equals 479/960-(2/3)log2 :", sp.simplify(tot - (sp.Rational(479,960)-sp.Rational(2,3)*sp.log(2)))==0)
