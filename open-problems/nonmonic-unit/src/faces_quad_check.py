# Deterministic nested-quadrature cross-check of F_a, F_b, F_c (float64, scipy).
import numpy as np
from scipy.integrate import quad

def band(A, B, C):
    disc2 = B*B - 3.0*A*C
    if disc2 <= 0.0 or A <= 0.0:
        return 0.0
    s = np.sqrt(disc2)
    xm = -(B + s)/(3.0*A)
    xp = -C/(B + s)
    g = lambda x: ((A*x + B)*x + C)*x
    lo = max(0.0, -g(xm))
    hi = min(1.0, -g(xp))
    return max(0.0, hi - lo)

OPT = dict(epsabs=1e-12, epsrel=1e-11, limit=400)

# F_a : x^3 + b x^2 + c x + d, vars (b,c,d).  need b^2>3c  =>  c < b^2/3
Fa = quad(lambda b: quad(lambda c: band(1.0, b, c), 0.0, b*b/3.0, **OPT)[0],
          0.0, 1.0, **OPT)[0]

# F_b : a x^3 + x^2 + c x + d, vars (a,c,d). need 1>3ac => c < 1/(3a)
def inner_b(a):
    hi = min(1.0, 1.0/(3.0*a))
    return quad(lambda c: band(a, 1.0, c), 0.0, hi, **OPT)[0]
Fb = quad(inner_b, 0.0, 1.0, **OPT)[0]

# F_c : a x^3 + b x^2 + x + d, vars (a,b,d). need b^2>3a => a < b^2/3
Fc = quad(lambda b: quad(lambda a: band(a, b, 1.0), 0.0, b*b/3.0, **OPT)[0],
          0.0, 1.0, **OPT)[0]

print(f"F_a (quad)  = {Fa:.12f}   1/2880 = {1/2880:.12f}   diff = {Fa-1/2880:+.3e}")
print(f"F_b (quad)  = {Fb:.12f}")
print(f"F_c (quad)  = {Fc:.12f}")
print(f"F_b - F_c   = {Fb-Fc:+.3e}")
print(f"(1/4)(Fa+Fb+Fc+Fa) = {(2*Fa+Fb+Fc)/4:.12f}")
print(f"1/5760 + F_b/2     = {1/5760 + Fb/2:.12f}")
print(f"1/5760 + F_c/2     = {1/5760 + Fc/2:.12f}")
