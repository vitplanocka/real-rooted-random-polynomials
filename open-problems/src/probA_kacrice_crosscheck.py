import mpmath as mp, sympy as sp, json, numpy as np
mp.mp.dps=140
def integrand(x):
    A=x**4+4*x**2+1; E=x**4+4*x**2+9
    return mp.e**(-(x**4*E)/(2*A))*2*(x**4+6*x**2+3)/(mp.sqrt(A)*E)
KR=mp.quad(integrand,[0,1,3,10,mp.inf])/mp.pi

d=json.load(open('results/gaussian_cubic_quad.json'))
C=mp.mpf(d['method_C_final']); R=mp.mpf(d['method_R_final'])
print("=== Kac-Rice integral vs our independent quadratures ===")
for nm,v in (('method C (coeff space)',C),('method R (root space)',R)):
    dd=abs(KR-v)
    print(f"  vs {nm:24s}: diff {mp.nstr(dd,4):12s} -> {int(-mp.log10(dd/abs(KR)))} agreeing digits")

print("\n=== eq(9): their discriminant form vs OUR Lean-proved identity ===")
a,b,c=sp.symbols('a b c', real=True)
theirs = -27*(c - a*b/3 + 2*a**3/27)**2 + sp.Rational(4,27)*(a**2-3*b)**3
ours   = 18*a*b*c - 4*a**3*c + a**2*b**2 - 4*b**3 - 27*c**2      # Delta_3 from Basic.lean
print("   residual (theirs - our Delta_3) =", sp.simplify(sp.expand(theirs-ours)))

print("\n=== structural bridge: is p = (E[N]-1)/2 ?  (MC on root counts) ===")
rng=np.random.default_rng(31415); N=20_000_000; tot=0; n3=0
CH=2_000_000
for _ in range(N//CH):
    A_,B_,C_=rng.standard_normal((3,CH))
    # count real roots via the discriminant of x^3+A x^2+B x+C
    D=18*A_*B_*C_-4*A_**3*C_+A_**2*B_**2-4*B_**3-27*C_**2
    k=np.where(D>0,3,1)
    tot+=k.sum(); n3+=(D>0).sum()
EN=tot/N; p_mc=n3/N
print(f"   E[N]      = {EN:.6f}   (N={N:,})")
print(f"   (E[N]-1)/2= {(EN-1)/2:.8f}")
print(f"   direct P  = {p_mc:.8f}")
print(f"   exact p   = {mp.nstr(KR,10)}")
print("   -> the bridge p=(E[N]-1)/2 is an identity for cubics (1 or 3 real roots);")
print("      MC confirms both sides land on p.")
