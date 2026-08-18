"""
Independent Monte-Carlo verification of the four face volumes F_a, F_b, F_c, F_d
for the non-monic real-rooted cubic problem on [0,1]^4.

F_a = vol{(b,c,d) in [0,1]^3 : 1*x^3 + b x^2 + c x + d has 3 real roots}
F_b = vol{(a,c,d) in [0,1]^3 : a*x^3 + 1*x^2 + c x + d has 3 real roots}
F_c = vol{(a,b,d) in [0,1]^3 : a*x^3 + b x^2 + 1*x + d has 3 real roots}
F_d = vol{(a,b,c) in [0,1]^3 : a*x^3 + b x^2 + c x + 1 has 3 real roots}

Real-rootedness test (critical-point test), for leading coeff A > 0:
    A x^3 + B x^2 + C x + D  has 3 real roots
    <=>  s2 := B^2 - 3 A C > 0   and   f(x_-)*f(x_+) <= 0,
    x_pm = (-B +- sqrt(B^2-3AC)) / (3A).

Numerical notes (see report):
  * All of B, C, D lie in [0,1] here, so B >= 0 always.  We therefore use the
    numerically stable ("Citardauq") form for the critical point of smaller
    magnitude,
        s = sqrt(B^2 - 3AC),   x_+ = -C / (B + s),   x_- = -(B + s)/(3A),
    which avoids catastrophic cancellation in x_+ when 3AC << B^2 (the regime
    A -> 0).  This is algebraically identical to the formula above.
  * A = a can be ~0 on the b/c/d faces.  A == 0.0 exactly is measure zero;
    numpy's Generator.random() can emit exactly 0.0 with probability 2^-53, so
    we mask it out explicitly (counted as NOT real-rooted) and evaluate the
    remaining arithmetic under np.errstate(...,'ignore') so that any stray
    inf/nan cannot propagate a warning.  For the smallest representable
    positive draw (2^-53 ~ 1.1e-16) we get |x_-| ~ 6e15 and x_-^3 ~ 2e47:
    no overflow in float64.
  * Instead of the product f(x_-)*f(x_+) (which can overflow-free but is
    numerically wasteful) we use the equivalent test f(x_-) >= 0 AND
    f(x_+) <= 0.  Since A > 0 and x_- < x_+, f(x_-) is the local max and
    f(x_+) the local min, so f(x_-) >= f(x_+) always and
    f(x_-)*f(x_+) <= 0  <=>  f(x_-) >= 0 >= f(x_+).
"""
import sys
import time
import numpy as np
from multiprocessing import Pool

N_PER_FACE = 2_000_000_000
N_WORKERS = 6
CHUNK = 5_000_000
BASE_SEED = 20260818_314159

FACES = ("a", "b", "c", "d")


def three_real(A, B, C, D):
    """Boolean array: does A x^3 + B x^2 + C x + D have three real roots?
    Assumes A >= 0, B >= 0 (true for all four faces here)."""
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        disc2 = B * B - 3.0 * A * C
        ok = disc2 > 0.0
        s = np.sqrt(np.where(ok, disc2, 0.0))
        Bs = B + s                      # >= 0; == 0 only if B == s == 0
        # smaller-magnitude critical point (local min, since A>0)
        xp = -C / Bs
        # larger-magnitude critical point (local max)
        xm = -Bs / (3.0 * A)
        fp = ((A * xp + B) * xp + C) * xp + D
        fm = ((A * xm + B) * xm + C) * xm + D
        res = ok & (fm >= 0.0) & (fp <= 0.0)
    # guard: A == 0 exactly (degenerate, measure zero) or any non-finite value
    good = np.isfinite(fp) & np.isfinite(fm) & (A > 0.0)
    return res & good


def face_arrays(face, u, v, w):
    """Map three U[0,1] draws to (A,B,C,D) for the requested face."""
    one = 1.0
    if face == "a":      # A = 1, (b,c,d) = (u,v,w)
        return one, u, v, w
    if face == "b":      # B = 1, (a,c,d) = (u,v,w)
        return u, one, v, w
    if face == "c":      # C = 1, (a,b,d) = (u,v,w)
        return u, v, one, w
    if face == "d":      # D = 1, (a,b,c) = (u,v,w)
        return u, v, w, one
    raise ValueError(face)


def worker(args):
    face, n, seed_entropy, stream = args
    rng = np.random.Generator(np.random.PCG64(
        np.random.SeedSequence([seed_entropy, ord(face), stream])))
    hits = 0
    done = 0
    degenerate = 0
    while done < n:
        m = min(CHUNK, n - done)
        u = rng.random(m)
        v = rng.random(m)
        w = rng.random(m)
        A, B, C, D = face_arrays(face, u, v, w)
        A_arr = A if isinstance(A, np.ndarray) else np.full(m, A)
        B_arr = B if isinstance(B, np.ndarray) else np.full(m, B)
        C_arr = C if isinstance(C, np.ndarray) else np.full(m, C)
        D_arr = D if isinstance(D, np.ndarray) else np.full(m, D)
        degenerate += int(np.count_nonzero(A_arr == 0.0))
        hits += int(np.count_nonzero(three_real(A_arr, B_arr, C_arr, D_arr)))
        done += m
    return hits, done, degenerate


def crosscheck(face, n, seed_entropy, tol=1e-9):
    """Compare the critical-point test against numpy.roots on n samples."""
    rng = np.random.Generator(np.random.PCG64(
        np.random.SeedSequence([seed_entropy, ord(face), 999_999])))
    u, v, w = rng.random(n), rng.random(n), rng.random(n)
    A, B, C, D = face_arrays(face, u, v, w)
    A_arr = A if isinstance(A, np.ndarray) else np.full(n, A)
    B_arr = B if isinstance(B, np.ndarray) else np.full(n, B)
    C_arr = C if isinstance(C, np.ndarray) else np.full(n, C)
    D_arr = D if isinstance(D, np.ndarray) else np.full(n, D)
    mine = three_real(A_arr, B_arr, C_arr, D_arr)
    disagree = 0
    theirs_cnt = 0
    for i in range(n):
        r = np.roots([A_arr[i], B_arr[i], C_arr[i], D_arr[i]])
        nreal = int(np.count_nonzero(np.abs(r.imag) <=
                                     tol * np.maximum(1.0, np.abs(r.real))))
        t = (len(r) == 3 and nreal == 3)
        theirs_cnt += t
        if t != bool(mine[i]):
            disagree += 1
    return int(mine.sum()), theirs_cnt, disagree, n


def main():
    out = []

    def emit(line=""):
        print(line, flush=True)
        out.append(line)

    emit("Independent Monte-Carlo of the four face volumes")
    emit("=" * 72)
    emit(f"numpy {np.__version__}, N per face = {N_PER_FACE:,}, "
         f"{N_WORKERS} worker processes, chunk = {CHUNK:,}")
    emit(f"base seed entropy = {BASE_SEED}; per-worker SeedSequence"
         f"([BASE_SEED, ord(face), stream])")
    emit("test: B^2-3AC>0 and f(x_-)>=0>=f(x_+) with stable x_+ = -C/(B+s)")
    emit()

    # ---- cross-check against numpy.roots on a subsample ----
    emit("Cross-check vs numpy.roots (20,000 independent samples per face):")
    for face in FACES:
        a, b, dis, n = crosscheck(face, 20_000, BASE_SEED)
        emit(f"  face {face}: critical-point test {a:6d}/{n}, "
             f"numpy.roots {b:6d}/{n}, disagreements = {dis}")
    emit()

    # ---- main run ----
    splits = []
    for face in FACES:
        base = N_PER_FACE // N_WORKERS
        rem = N_PER_FACE - base * N_WORKERS
        for k in range(N_WORKERS):
            splits.append((face, base + (1 if k < rem else 0), BASE_SEED, k))

    results = {}
    with Pool(N_WORKERS) as pool:
        for face in FACES:
            t0 = time.time()
            jobs = [s for s in splits if s[0] == face]
            parts = pool.map(worker, jobs)
            hits = sum(p[0] for p in parts)
            tot = sum(p[1] for p in parts)
            deg = sum(p[2] for p in parts)
            p_hat = hits / tot
            se = np.sqrt(p_hat * (1.0 - p_hat) / tot)
            results[face] = (p_hat, se, hits, tot, deg)
            emit(f"F_{face} = {p_hat:.9f}  +/- {se:.3e}   "
                 f"(hits {hits:,} / {tot:,}, A==0 draws: {deg}, "
                 f"{time.time()-t0:.0f}s)")
    emit()

    Fa, sa = results["a"][0], results["a"][1]
    Fb, sb = results["b"][0], results["b"][1]
    Fc, sc = results["c"][0], results["c"][1]
    Fd, sd = results["d"][0], results["d"][1]

    emit("Symmetry checks (reciprocal map (a,b,c,d)->(d,c,b,a)):")
    dad, sad = Fa - Fd, np.hypot(sa, sd)
    dbc, sbc = Fb - Fc, np.hypot(sb, sc)
    emit(f"  F_a - F_d = {dad:+.3e} +/- {sad:.3e}   ({abs(dad)/sad:.2f} sigma)")
    emit(f"  F_b - F_c = {dbc:+.3e} +/- {sbc:.3e}   ({abs(dbc)/sbc:.2f} sigma)")
    emit()

    emit("Comparison of F_a against Theorem 2 = 1/2880 = "
         f"{1/2880:.9f}:")
    emit(f"  F_a - 1/2880 = {Fa-1/2880:+.3e} +/- {sa:.3e}  "
         f"({abs(Fa-1/2880)/sa:.2f} sigma)")
    emit()

    P_ref, se_ref = 1.8603554e-2, 3.0e-6

    q = 0.25 * (Fa + Fb + Fc + Fd)
    sq = 0.25 * np.sqrt(sa**2 + sb**2 + sc**2 + sd**2)
    r = 1.0 / 5760.0 + Fb / 2.0
    sr = sb / 2.0

    emit(f"Reference 4-D value          P = {P_ref:.9f} +/- {se_ref:.1e}")
    emit(f"(1/4)(F_a+F_b+F_c+F_d)         = {q:.9f} +/- {sq:.3e}")
    d1 = q - P_ref
    c1 = np.hypot(sq, se_ref)
    emit(f"    difference from P          = {d1:+.3e} +/- {c1:.3e}  "
         f"({abs(d1)/c1:.2f} sigma)")
    emit(f"1/5760 + F_b/2                 = {r:.9f} +/- {sr:.3e}")
    d2 = r - P_ref
    c2 = np.hypot(sr, se_ref)
    emit(f"    difference from P          = {d2:+.3e} +/- {c2:.3e}  "
         f"({abs(d2)/c2:.2f} sigma)")
    emit()
    emit(f"raw sum F_a+F_b+F_c+F_d        = {Fa+Fb+Fc+Fd:.9f} "
         f"+/- {np.sqrt(sa**2+sb**2+sc**2+sd**2):.3e}")

    with open("/home/vit-planocka/math/nonmonic-01/results/faces_mc.txt", "w") as fh:
        fh.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
