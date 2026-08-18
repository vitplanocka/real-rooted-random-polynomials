"""INDEPENDENT verification of the claimed 1D integral representation for P_A.
Nothing is taken from the write-up except the CLAIMED formulas, each of which is
re-derived here from first principles.

Setup re-derived from scratch:
  f(x) = x^3 + a x^2 + b x + c,  (a,b,c) ~ N(0,1) iid
  q(x) = x^4 + x^2 + 1,  u(x) = (x^2, x, 1)/sqrt(q)   [unit vector]
  Z(x) = (a,b,c) . u(x) ~ N(0,1) pointwise
  f(x) = x^3 + sqrt(q) Z(x),  so f(x)=0  <=>  Z(x) = -h(x),  h = x^3/sqrt(q)
"""
import sympy as sp

x = sp.symbols('x', real=True)
q = x**4 + x**2 + 1
u = sp.Matrix([x**2, x, 1]) / sp.sqrt(q)

print("=== 0. u is a unit vector ===")
print("   ||u||^2 - 1 =", sp.simplify((u.T*u)[0] - 1))

up = sp.diff(u, x)
print("\n=== 0b. Cov(Z,Z') = u.u' = 0  (so Z, Z' independent) ===")
print("   u.u' =", sp.simplify((u.T*up)[0]))

print("\n=== 1. v^2 = ||u'||^2  vs claimed (x^4+4x^2+1)/q^2 ===")
v2 = sp.simplify((up.T*up)[0])
claim_v2 = (x**4 + 4*x**2 + 1)/q**2
print("   computed  =", sp.simplify(v2))
print("   residual  =", sp.simplify(v2 - claim_v2))

print("\n=== 2. h' vs claimed x^2(x^4+2x^2+3)/q^(3/2) ===")
h = x**3/sp.sqrt(q)
hp = sp.diff(h, x)
claim_hp = x**2*(x**4 + 2*x**2 + 3)/q**sp.Rational(3,2)
print("   residual  =", sp.simplify(sp.radsimp(hp - claim_hp)))

print("\n=== 3. eq(7): h^2 + z^2 with z = h'/v, vs x^4(x^4+4x^2+9)/(x^4+4x^2+1) ===")
v = sp.sqrt(v2)
z = sp.simplify(hp/v)
lhs = sp.simplify(h**2 + z**2)
claim7 = x**4*(x**4 + 4*x**2 + 9)/(x**4 + 4*x**2 + 1)
print("   residual  =", sp.simplify(sp.together(lhs - claim7)))

print("\n=== 4. eq(8): v + theta' with theta = atan(z/h), vs claim ===")
th = sp.atan(z/h)
lhs8 = sp.simplify(v + sp.diff(th, x))
claim8 = 2*(x**4 + 6*x**2 + 3)/(sp.sqrt(x**4 + 4*x**2 + 1)*(x**4 + 4*x**2 + 9))
d8 = sp.simplify(lhs8 - claim8)
print("   symbolic residual =", d8)
print("   numeric residuals at sample points (should be ~0):")
for pt in [sp.Rational(1,3), sp.Rational(1,2), 1, sp.Rational(3,2), 2, 5]:
    val = sp.N((lhs8 - claim8).subs(x, pt), 40)
    print(f"      x={pt}:  {val}")
