"""High-precision evaluation of P(x^3 + a x^2 + b x + c has 3 real roots),
(a,b,c) iid uniform, via the exact 2D reduction.

Reduction (verified symbolically in exact_anchors.py):
  For b < a^2/3, with s = sqrt(a^2-3b), g(x) = x^3+ax^2+bx,
  x_minus = (-a-s)/3 (local max), x_plus = (-a+s)/3 (local min):
      3 real roots  <=>  c in [c_lo, c_hi],
      c_lo = -g(x_minus),  c_hi = -g(x_plus),
      Disc = -27 (c - c_lo)(c - c_hi).
  Hence for a c-window [w_lo, w_hi]:
      Vol = Int Int  max(0, min(c_hi, w_hi) - max(c_lo, w_lo)) db da
  over the (a,b) box intersected with {b < a^2/3}.

Numerics:
  Inner integral over b: locate all breakpoints where c_lo or c_hi crosses
  w_lo or w_hi (kinks of the overlap function) by dense scan + bisection,
  then tanh-sinh quadrature (mpmath) on each smooth piece.
  Outer integral over a: detect the finitely many a-values where the
  breakpoint pattern changes (piecewise-analyticity boundaries), then
  composite Gauss-Legendre on each smooth piece, with node-doubling
  error control.

Validation: the same pipeline with a frozen at 0 and b-range [-1,0]
reproduces the depressed-cubic anchor 8*sqrt(3)/45 / 4 = 2*sqrt(3)/45.

Cases computed:
  P_sym  : (a,b,c) iid U[-1,1]   (uses a -> -a symmetry, integrates a in [0,1])
  P_unit : (a,b,c) iid U[0,1]

Then: inverse symbolic identification attempts (mpmath.identify / PSLQ).

Output: results/reduce_monic.json
"""
import json
import os
import time

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "results", "reduce_monic.json")

mp.mp.dps = 30


# ---------------------------------------------------------------- band
def c_band_f(a, b):
    """float band (c_lo, c_hi); requires b <= a*a/3."""
    s = np.sqrt(max(a * a - 3 * b, 0.0))
    xm = (-a - s) / 3.0
    xp = (-a + s) / 3.0
    g = lambda x: ((x + a) * x + b) * x
    return -g(xm), -g(xp)


def c_band_mp(a, b):
    a = mp.mpf(a)
    b = mp.mpf(b)
    s = mp.sqrt(max(a * a - 3 * b, mp.mpf(0)))
    xm = (-a - s) / 3
    xp = (-a + s) / 3
    g = lambda x: ((x + a) * x + b) * x
    return -g(xm), -g(xp)


def overlap_mp(a, b, w_lo, w_hi):
    lo, hi = c_band_mp(a, b)
    v = min(hi, w_hi) - max(lo, w_lo)
    return v if v > 0 else mp.mpf(0)


# ---------------------------------------------------------------- inner
def _bisect(fn, x0, x1, iters=80):
    f0 = fn(x0)
    for _ in range(iters):
        xm = 0.5 * (x0 + x1)
        fm = fn(xm)
        if (f0 < 0) == (fm < 0):
            x0, f0 = xm, fm
        else:
            x1 = xm
    return 0.5 * (x0 + x1)


def inner_breakpoints(a, b_lo, b_hi, w_lo, w_hi, ngrid=1601):
    """b-values in (b_lo, b_hi) where the overlap integrand kinks."""
    if b_hi <= b_lo:
        return []
    grid = np.linspace(b_lo, b_hi, ngrid)
    lo = np.empty(ngrid)
    hi = np.empty(ngrid)
    for i, bb in enumerate(grid):
        lo[i], hi[i] = c_band_f(a, bb)
    pts = set()
    for vals, w in ((lo, w_lo), (lo, w_hi), (hi, w_lo), (hi, w_hi)):
        f = vals - w
        idx = np.nonzero(np.signbit(f[:-1]) != np.signbit(f[1:]))[0]
        for i in idx:
            which = 0 if vals is lo else 1
            fn = lambda bb: c_band_f(a, bb)[which] - w
            pts.add(_bisect(fn, grid[i], grid[i + 1]))
    return sorted(pts)


def inner_integral(a, b_lo, b_hi, w_lo, w_hi):
    """Int_{b_lo}^{b_hi} overlap(a,b) db to full working precision."""
    if b_hi <= b_lo:
        return mp.mpf(0)
    pts = ([b_lo] + inner_breakpoints(a, b_lo, b_hi, w_lo, w_hi) + [b_hi])
    total = mp.mpf(0)
    for x0, x1 in zip(pts[:-1], pts[1:]):
        if x1 - x0 < 1e-14:
            continue
        total += mp.quad(lambda bb: overlap_mp(a, bb, w_lo, w_hi),
                         [mp.mpf(x0), mp.mpf(x1)])
    return total


# ---------------------------------------------------------------- outer
def pattern_signature(a, b_lo_fn, w_lo, w_hi, ngrid=400):
    b_hi = a * a / 3.0
    b_lo = b_lo_fn(a)
    if b_hi <= b_lo:
        return ("empty",)
    grid = np.linspace(b_lo, b_hi, ngrid)
    lo = np.empty(ngrid)
    hi = np.empty(ngrid)
    for i, bb in enumerate(grid):
        lo[i], hi[i] = c_band_f(a, bb)
    sig = []
    for vals, w in ((lo, w_lo), (lo, w_hi), (hi, w_lo), (hi, w_hi)):
        f = vals - w
        sig.append(int(np.count_nonzero(
            np.signbit(f[:-1]) != np.signbit(f[1:]))))
    # also whether overlap is ever zero inside
    ov = np.minimum(hi, w_hi) - np.maximum(lo, w_lo)
    sig.append(int(np.count_nonzero(
        np.signbit(ov[:-1]) != np.signbit(ov[1:]))))
    return tuple(sig)


def outer_pieces(a_lo, a_hi, b_lo_fn, w_lo, w_hi, nscan=801):
    """Split [a_lo, a_hi] at points where the breakpoint pattern changes."""
    grid = np.linspace(a_lo, a_hi, nscan)
    sigs = [pattern_signature(aa, b_lo_fn, w_lo, w_hi) for aa in grid]
    cuts = [a_lo]
    for i in range(len(grid) - 1):
        if sigs[i] != sigs[i + 1]:
            x0, x1 = grid[i], grid[i + 1]
            s0 = sigs[i]
            for _ in range(60):
                xm = 0.5 * (x0 + x1)
                if pattern_signature(xm, b_lo_fn, w_lo, w_hi) == s0:
                    x0 = xm
                else:
                    x1 = xm
            cuts.append(0.5 * (x0 + x1))
    cuts.append(a_hi)
    return cuts


def gauss_piece(fn, x0, x1, nodes):
    xs, ws = np.polynomial.legendre.leggauss(nodes)
    mid = mp.mpf(x0 + x1) / 2
    half = mp.mpf(x1 - x0) / 2
    total = mp.mpf(0)
    for xi, wi in zip(xs, ws):
        total += mp.mpf(wi) * fn(mid + half * mp.mpf(xi))
    return total * half


def outer_integral(a_lo, a_hi, b_lo_fn, w_lo, w_hi, nodes=48):
    cuts = outer_pieces(a_lo, a_hi, b_lo_fn, w_lo, w_hi)
    fn = lambda aa: inner_integral(float(aa), b_lo_fn(float(aa)),
                                   float(aa) ** 2 / 3.0, w_lo, w_hi)
    total = mp.mpf(0)
    for x0, x1 in zip(cuts[:-1], cuts[1:]):
        if x1 - x0 < 1e-13:
            continue
        total += gauss_piece(fn, x0, x1, nodes)
    return total, cuts


# ---------------------------------------------------------------- cases
def main():
    results = {}
    t0 = time.time()

    # --- validation: depressed cubic anchor through the same code path
    val = inner_integral(0.0, -1.0, 0.0, -1.0, 1.0) / 4
    exact = 2 * mp.sqrt(3) / 45
    err = abs(val - exact)
    print(f"validation (depressed): {mp.nstr(val, 25)}")
    print(f"exact 2 sqrt(3)/45    : {mp.nstr(exact, 25)}")
    print(f"|err| = {mp.nstr(err, 3)}")
    results["validation_depressed"] = {
        "computed": mp.nstr(val, 25),
        "exact": mp.nstr(exact, 25),
        "abs_err": mp.nstr(err, 3),
    }

    # --- P_sym : (a,b,c) iid U[-1,1]; a-symmetry => integrate a in [0,1], x2
    # Vol = 2 * Int_0^1 Int_{-1}^{a^2/3} overlap db da ;  P = Vol / 8
    for nodes in (48, 64):
        I, cuts = outer_integral(0.0, 1.0, lambda aa: -1.0, -1.0, 1.0,
                                 nodes=nodes)
        P_sym = 2 * I / 8
        results[f"P_sym_nodes{nodes}"] = mp.nstr(P_sym, 25)
        print(f"P_sym  (nodes={nodes}): {mp.nstr(P_sym, 25)}   "
              f"pieces at {['%.6f' % c for c in cuts]}")
    P_sym = mp.mpf(results["P_sym_nodes64"])
    conv = abs(mp.mpf(results["P_sym_nodes48"]) - P_sym)
    results["P_sym"] = mp.nstr(P_sym, 25)
    results["P_sym_node_doubling_diff"] = mp.nstr(conv, 3)
    print(f"node-doubling agreement: {mp.nstr(conv, 3)}")

    # --- P_unit : (a,b,c) iid U[0,1]; b in [0, a^2/3], c-window [0,1]
    for nodes in (48, 64):
        I, cuts = outer_integral(0.0, 1.0, lambda aa: 0.0, 0.0, 1.0,
                                 nodes=nodes)
        P_unit = I  # cube volume 1
        results[f"P_unit_nodes{nodes}"] = mp.nstr(P_unit, 25)
        print(f"P_unit (nodes={nodes}): {mp.nstr(P_unit, 25)}")
    P_unit = mp.mpf(results["P_unit_nodes64"])
    results["P_unit"] = mp.nstr(P_unit, 25)
    results["P_unit_node_doubling_diff"] = mp.nstr(
        abs(mp.mpf(results["P_unit_nodes48"]) - P_unit), 3)

    # ------------------------------------------------ identification
    ident = {}
    consts = ["sqrt(3)", "pi", "log(2)", "log(3)", "sqrt(2)", "sqrt(5)",
              "sqrt(7)"]
    for label, valx in (("P_sym", P_sym), ("P_unit", P_unit)):
        found = {}
        try:
            r = mp.identify(valx, consts)
            found["identify_default"] = str(r)
        except Exception as e:  # noqa
            found["identify_default"] = f"error: {e}"
        # PSLQ against a curated basis
        basis_syms = ["1", "sqrt(3)", "pi", "log(2)", "log(3)",
                      "sqrt(3)*pi", "pi**2", "log(2)**2", "asinh(...)"]
        basis = [mp.mpf(1), mp.sqrt(3), mp.pi, mp.log(2), mp.log(3),
                 mp.sqrt(3) * mp.pi, mp.pi ** 2, mp.log(2) ** 2,
                 mp.asinh(1 / mp.sqrt(3))]
        try:
            rel = mp.pslq([valx] + basis, maxcoeff=10**6, maxsteps=10**5)
            found["pslq_relation"] = (None if rel is None
                                      else dict(zip(["target"] + basis_syms,
                                                    [int(z) for z in rel])))
        except Exception as e:  # noqa
            found["pslq_relation"] = f"error: {e}"
        ident[label] = found
        print(f"identify {label}: {found}")
    results["identification"] = ident

    results["elapsed_seconds"] = round(time.time() - t0, 1)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(results, fh, indent=2)
    print(f"written: {os.path.abspath(OUT)}  "
          f"({results['elapsed_seconds']}s)")


if __name__ == "__main__":
    main()
