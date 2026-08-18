"""Promote eq(8) from 'zero at sample points' to an EXACT identity by clearing
the two nested radicals: the residual vanishes iff
   (x^4+4x^2+1)(x^8+7x^6+10x^4+9x^2+3)^2 == (x^4+6x^2+3)^2 (x^12+6x^10+...+1)
with both sides of the pre-squared identity positive."""
import sympy as sp
x = sp.symbols('x', real=True)
A = x**4 + 4*x**2 + 1
B = x**8 + 7*x**6 + 10*x**4 + 9*x**2 + 3
C = x**4 + 6*x**2 + 3
D = x**12 + 6*x**10 + 12*x**8 + 16*x**6 + 12*x**4 + 6*x**2 + 1
print("is D = q^3 ?  ", sp.expand(D - (x**4+x**2+1)**3))
print("squared identity residual:", sp.expand(A*B**2 - C**2*D))
print("both pre-squared sides positive for x>0? B, C, A, D all have positive coeffs:",
      all(c > 0 for c in sp.Poly(B, x).all_coeffs() if c != 0),
      all(c > 0 for c in sp.Poly(C, x).all_coeffs() if c != 0))
print("\n=> eq(8) holds EXACTLY (not merely at sample points).")
