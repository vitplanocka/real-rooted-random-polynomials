"""Problem B in ROOT SPACE — structurally independent of every coefficient-space
route (no critical points, no cubic solver, no band length L, no d* kink).

f = prod (x - r_i) = x^4 - e1 x^3 + e2 x^2 - e3 x + e4, so
    (b,c,d,e) = (-e1, e2, -e3, e4)
and |b|,|c|,|d|,|e| <= 1  <=>  |e_i| <= 1 for i=1..4.

The map (r1<r2<r3<r4) -> (e1,e2,e3,e4) is a bijection onto the all-real region
with |Jacobian| = |V| = prod_{i<j} (r_i - r_j).  Hence

    16 P_B = Int_{r1<r2<r3<r4, |e_i|<=1} V(r) dr.

All roots are bounded there: sum r_i^2 = e1^2 - 2 e2 <= 1 + 2 = 3, so |r_i| <= sqrt(3).
"""
import json, os, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = np.sqrt(3.0)

def esym(r):                      # r shape (4, N), sorted ascending
    r1, r2, r3, r4 = r
    e1 = r1 + r2 + r3 + r4
    e2 = r1*r2 + r1*r3 + r1*r4 + r2*r3 + r2*r4 + r3*r4
    e3 = r1*r2*r3 + r1*r2*r4 + r1*r3*r4 + r2*r3*r4
    e4 = r1*r2*r3*r4
    return e1, e2, e3, e4

def run(N, seed):
    rng = np.random.default_rng(seed)
    r = rng.uniform(-R, R, (4, N))
    r = np.sort(r, axis=0)                       # induces r1<r2<r3<r4
    e1, e2, e3, e4 = esym(r)
    ok = (np.abs(e1) <= 1) & (np.abs(e2) <= 1) & (np.abs(e3) <= 1) & (np.abs(e4) <= 1)
    r1, r2, r3, r4 = r
    V = ((r2-r1)*(r3-r1)*(r4-r1)*(r3-r2)*(r4-r2)*(r4-r3))
    f = np.where(ok, V, 0.0)
    # sorting 4 uniforms => density 4!/(2R)^4 on the ordered simplex, so the
    # ordered-region volume element carries weight (2R)^4/4!
    W = (2*R)**4 / 24.0
    I16 = W * f.mean()
    se  = W * f.std(ddof=1) / np.sqrt(N)
    return I16, se

if __name__ == "__main__":
    N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000
    out = []
    for seed in (11, 22, 33):
        I16, se = run(N, seed)
        out.append({"seed": seed, "N": N, "I16": I16, "se_I16": se,
                    "PB": I16/16.0, "se_PB": se/16.0})
        print(f"seed {seed}: 16P_B = {I16:.7f} +- {se:.7f}   P_B = {I16/16:.8f} +- {se/16:.8f}")
    vals = np.array([o["I16"] for o in out]); ses = np.array([o["se_I16"] for o in out])
    w = 1/ses**2
    pooled = (vals*w).sum()/w.sum(); pse = 1/np.sqrt(w.sum())
    print(f"\npooled: 16P_B = {pooled:.7f} +- {pse:.7f}   P_B = {pooled/16:.8f} +- {pse/16:.8f}")
    json.dump({"method": "root space, Vandermonde, |e_i|<=1", "runs": out,
               "pooled_I16": pooled, "pooled_se_I16": pse,
               "pooled_PB": pooled/16.0, "pooled_se_PB": pse/16.0},
              open(os.path.join(ROOT, "results", "rootspaceB_check.json"), "w"), indent=2)
