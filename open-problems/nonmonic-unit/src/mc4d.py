"""Step 1: independent raw Monte Carlo for
   P = Pr( a x^3 + b x^2 + c x + d has three real roots ),  (a,b,c,d) iid U[0,1].

Criterion: sign of the cubic discriminant
   Delta = 18 a b c d - 4 b^3 d + b^2 c^2 - 4 a c^3 - 27 a^2 d^2 > 0
(three distinct real roots; a=0 has measure zero).

Usage: mc4d.py <N_total> <n_proc> <seed>
Prints hits, N, phat, stderr.
"""
import sys, numpy as np
from multiprocessing import Pool

def chunk(args):
    seed, n = args
    rng = np.random.Generator(np.random.PCG64(seed))
    hits = 0
    B = 20_000_000
    done = 0
    while done < n:
        m = min(B, n - done)
        a = rng.random(m); b = rng.random(m); c = rng.random(m); d = rng.random(m)
        delta = 18*a*b*c*d - 4*b**3*d + b*b*c*c - 4*a*c**3 - 27*a*a*d*d
        hits += int(np.count_nonzero(delta > 0))
        done += m
    return hits

if __name__ == "__main__":
    N = int(float(sys.argv[1])); P = int(sys.argv[2]); seed0 = int(sys.argv[3])
    per = N // P
    tasks = [(seed0 + 1000*i, per) for i in range(P)]
    with Pool(P) as pool:
        res = pool.map(chunk, tasks)
    hits = sum(res); Ntot = per*P
    phat = hits/Ntot
    se = (phat*(1-phat)/Ntot)**0.5
    print(f"N={Ntot} hits={hits} phat={phat:.10e} se={se:.3e}  ({phat/se:.1f} sigma)")
    print(f"95% CI: [{phat-1.96*se:.10e}, {phat+1.96*se:.10e}]")
    print(f"1/5760 = {1/5760:.10e};  implied S = 2*(phat-1/5760) = {2*(phat-1/5760):.10e}")
