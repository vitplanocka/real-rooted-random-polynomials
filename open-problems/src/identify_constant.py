"""Broad closed-form search for a decimal constant: mpmath.identify + PSLQ.

Usage:  python src/identify_constant.py <decimal-string> [label]

Deliberately reports the *search basis actually tried*, not just a verdict, so
that "nothing found" is a documented negative rather than a shrug.

Discipline (inherited from the previous campaign's post-mortem):
  * PSLQ on N digits will always find *some* relation if you allow large
    coefficients.  A hit is only interesting if the coefficients are small
    relative to the number of digits supplied, and if it survives being re-run
    against more digits.
  * So every hit is printed together with its coefficient size and the number of
    digits it was found from, and nothing is called a discovery here.
"""
import json
import os
import sys
from mpmath import mp, mpf, pi, log, sqrt, catalan, gamma, euler, exp, identify, pslq

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "..", "results")


def constant_pool():
    """Named constants plausibly arising from Gaussian/erf-flavoured integrals."""
    return {
        "pi": pi,
        "1/pi": 1 / pi,
        "pi^2": pi ** 2,
        "1/pi^2": 1 / pi ** 2,
        "log2": log(2),
        "log3": log(3),
        "log5": log(5),
        "sqrt2": sqrt(2),
        "sqrt3": sqrt(3),
        "sqrt5": sqrt(5),
        "sqrt2/pi": sqrt(2) / pi,
        "sqrt3/pi": sqrt(3) / pi,
        "log2/pi": log(2) / pi,
        "log3/pi": log(3) / pi,
        "catalan": catalan,
        "catalan/pi": catalan / pi,
        "gamma(1/4)": gamma(mpf(1) / 4),
        "gamma(1/4)^2": gamma(mpf(1) / 4) ** 2,
        "gamma(1/3)": gamma(mpf(1) / 3),
        "euler": euler,
        # arctan / arcsin values that show up in Gaussian orthant probabilities
        "atan(sqrt2)": mp.atan(sqrt(2)),
        "atan(sqrt2)/pi": mp.atan(sqrt(2)) / pi,
        "atan(1/sqrt2)/pi": mp.atan(1 / sqrt(2)) / pi,
        "asin(1/3)/pi": mp.asin(mpf(1) / 3) / pi,
        "asin(1/4)/pi": mp.asin(mpf(1) / 4) / pi,
        "asin(1/sqrt3)/pi": mp.asin(1 / sqrt(3)) / pi,
        "atan(1/sqrt3)/pi": mp.atan(1 / sqrt(3)) / pi,
        "acos(1/3)/pi": mp.acos(mpf(1) / 3) / pi,
        "acos(-1/3)/pi": mp.acos(-mpf(1) / 3) / pi,
        # erf-adjacent
        "erf(1)": mp.erf(1),
        "exp(-1/2)": exp(mpf(-1) / 2),
        "sqrt(pi)": sqrt(pi),
    }


def run(xstr: str, label: str) -> dict:
    x = mpf(xstr)
    ndig = len(xstr.split(".")[-1])
    out = {"label": label, "value": xstr, "digits_supplied": ndig, "hits": []}

    print(f"=== {label} ===")
    print(f"value    : {xstr}")
    print(f"digits   : {ndig}\n")

    # 1. mpmath.identify with a few explicit bases
    bases = [
        [],
        ["pi"],
        ["pi", "log(2)"],
        ["pi", "log(2)", "log(3)"],
        ["pi", "sqrt(2)", "sqrt(3)"],
        ["pi", "log(2)", "log(3)", "sqrt(2)", "sqrt(3)"],
        ["catalan", "pi"],
        ["gamma(0.25)", "pi"],
    ]
    print("-- mpmath.identify --")
    for b in bases:
        for tol_exp in (ndig - 4, ndig - 8):
            if tol_exp < 8:
                continue
            r = identify(x, b, tol=mpf(10) ** (-tol_exp))
            if r:
                print(f"  basis={b or '[rationals]'} tol=1e-{tol_exp} -> {r}")
                out["hits"].append({"kind": "identify", "basis": b,
                                    "tol": f"1e-{tol_exp}", "result": str(r)})
    if not out["hits"]:
        print("  (no hit)")

    # 2. PSLQ: is x a rational combination of x and one named constant?
    print("\n-- PSLQ, x vs each named constant (2-term) --")
    pool = constant_pool()
    maxcoeff = 10 ** 6
    n2 = 0
    for name, c in pool.items():
        rel = pslq([x, c, mpf(1)], maxcoeff=maxcoeff, maxsteps=10 ** 5)
        if rel and rel[0] != 0:
            size = max(abs(v) for v in rel)
            print(f"  {name:18s} rel={rel}  maxcoeff={size}")
            out["hits"].append({"kind": "pslq2", "constant": name,
                                "relation": [int(v) for v in rel],
                                "maxcoeff": int(size)})
            n2 += 1
    if n2 == 0:
        print("  (no relation with coefficients below 1e6)")

    out["basis_tried"] = {"identify_bases": [b or ["rationals"] for b in bases],
                          "pslq_pool": sorted(pool.keys()),
                          "pslq_maxcoeff": maxcoeff}
    return out


def main() -> None:
    if len(sys.argv) < 2:
        print(__doc__)
        return
    xstr = sys.argv[1]
    label = sys.argv[2] if len(sys.argv) > 2 else "constant"
    mp.dps = max(40, len(xstr) + 10)
    out = run(xstr, label)
    path = os.path.join(RESULTS, f"identify_{label}.json")
    json.dump(out, open(path, "w"), indent=2)
    print(f"\nwrote {path}")
    print(f"\nHITS: {len(out['hits'])} "
          f"(treat as tentative until re-checked against more digits)")


if __name__ == "__main__":
    main()
