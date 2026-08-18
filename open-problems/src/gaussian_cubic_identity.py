"""Symbolic (sympy) confirmation of the band reduction actually used.

With s = sqrt(a^2 - 3b)  (i.e. b = (a^2 - s^2)/3, s >= 0),
   27 c_hi = (a-s)^2 (a+2s),   27 c_lo = (a+s)^2 (a-2s),
the cubic discriminant satisfies the polynomial identity

   Delta3(a,b,c) = -27 (c - c_hi)(c - c_lo).

Since the leading coefficient in c is -27 < 0, Delta3 > 0 <=> c_lo < c < c_hi,
which is exactly the reduction the quadrature uses.
"""
import sympy as sp

a, c, s = sp.symbols("a c s", real=True)
b = (a ** 2 - s ** 2) / 3
c_hi = (a - s) ** 2 * (a + 2 * s) / 27
c_lo = (a + s) ** 2 * (a - 2 * s) / 27
D3 = 18 * a * b * c - 4 * a ** 3 * c + a ** 2 * b ** 2 - 4 * b ** 3 - 27 * c ** 2

CHECKS = {
    "Delta3 == -27 (c-c_hi)(c-c_lo)": sp.expand(D3 + 27 * (c - c_hi) * (c - c_lo)),
    "c_hi - c_lo == 4 s^3/27": sp.simplify(c_hi - c_lo - 4 * s ** 3 / 27),
    "c_hi + c_lo == (18ab - 4a^3)/27": sp.simplify(c_hi + c_lo - (18 * a * b - 4 * a ** 3) / 27),
    "c_hi == (9ab - 2a^3 + 2 s^3)/27": sp.simplify(c_hi - (9 * a * b - 2 * a ** 3 + 2 * s ** 3) / 27),
}

if __name__ == "__main__":
    for name, expr in CHECKS.items():
        print(f"{name:38s} : {sp.simplify(expr) == 0}")
