import mpmath as mp
OURS = ("0.16992938262347950265644315713176190213405726145463153"  # 54-digit campaign value
        )
def integrand(x):
    A = x**4 + 4*x**2 + 1
    E = x**4 + 4*x**2 + 9
    return mp.e**(-(x**4*E)/(2*A)) * 2*(x**4 + 6*x**2 + 3)/(mp.sqrt(A)*E)
for dps in (60, 90, 120):
    mp.mp.dps = dps
    val = mp.quad(integrand, [0, 1, 3, 10, mp.inf])/mp.pi
    print(f"dps={dps:3d}: p = {mp.nstr(val, dps-8)}")
mp.mp.dps = 120
val = mp.quad(integrand, [0, 1, 3, 10, mp.inf])/mp.pi
ours = mp.mpf(OURS)
print(f"\nour 54-digit campaign value : {OURS}")
print(f"Kac-Rice integral (120 dps) : {mp.nstr(val, 60)}")
d = abs(val - ours)
print(f"difference                  : {mp.nstr(d, 5)}")
print(f"agreeing significant digits : {int(-mp.log10(d/abs(ours)))}")
