"""Merge every quadrature run into one verdict and rewrite the results JSON."""
import json
import os
import pickle

from mpmath import mp, mpf

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES = os.path.join(ROOT, "results")
mp.dps = 160


def agree(x, y):
    if x == y:
        return mp.dps
    return int(mp.floor(-mp.log10(abs(x - y) / abs(x))))


def main():
    with open(os.path.join(RES, "gaussian_cubic_quad.json")) as fh:
        base = json.load(fh)
    Chi_s, Rhi_s = pickle.load(open(os.path.join(RES, "_hires.pkl"), "rb"))
    Chi, Rhi = mpf(Chi_s), mpf(Rhi_s)

    C110 = mpf(base["method_C_final"])
    R110 = mpf(base["method_R_final"])
    Cv110 = mpf(base["method_C_variant"])
    Rv110 = mpf(base["method_R_variant"])

    ts = None
    p_ts = os.path.join(RES, "gaussian_cubic_quad_ts.json")
    if os.path.exists(p_ts):
        with open(p_ts) as fh:
            ts = json.load(fh)

    pairs = {
        "C(dps150,n150) vs R(dps150,n132)  [independent reductions]": (Chi, Rhi),
        "C(dps150,n150) vs C(dps110,n104, variant mesh)": (Chi, Cv110),
        "C(dps150,n150) vs C(dps110,n110)": (Chi, C110),
        "R(dps150,n132) vs R(dps110,n96)": (Rhi, R110),
        "R(dps110,n96) vs R(dps110,n92, variant mesh)": (R110, Rv110),
        "C(dps110,n110) vs R(dps110,n96)": (C110, R110),
    }
    print("=== FINAL AGREEMENT TABLE ===")
    tbl = {}
    for k, (x, y) in pairs.items():
        tbl[k] = agree(x, y)
        print(f"  {tbl[k]:4d} digits   {k}")

    if ts:
        Tv = mpf(ts["runs"][-1]["value"])
        d = agree(Chi, Tv)
        print(f"  {d:4d} digits   T(mpmath-native tanh-sinh + GL) vs C(dps150,n150)"
              f"   [limited by the {len(ts['runs'][-1]['value'])-2}-digit print width of T]")
        tbl["T(mpmath-native) vs C(dps150,n150)"] = d

    # verdict: C is the better-converged method (mesh-independent to ~79 digits);
    # R is the independent confirmation and caps the *defensible* count.
    n_ind = agree(Chi, Rhi)
    print(f"\nIndependent-reduction agreement (C vs R): {n_ind} significant digits")
    print(f"Claimed (deliberately conservative): {n_ind - 5} digits\n")

    claim = n_ind - 5
    print("P_A =")
    print("  " + mp.nstr(Chi, claim))
    print("\nfull method-C value (best available, ~79 digits believed correct):")
    print("  " + mp.nstr(Chi, 80))

    base["hires_method_C_dps150_n150"] = Chi_s
    base["hires_method_R_dps150_n132"] = Rhi_s
    base["final_agreement_digits"] = tbl
    base["independent_reduction_agreement_digits"] = n_ind
    base["claimed_digits"] = claim
    base["P_A"] = mp.nstr(Chi, claim)
    base["P_A_best_available_80_digits"] = mp.nstr(Chi, 80)
    if ts:
        base["method_T_mpmath_native"] = ts
    with open(os.path.join(RES, "gaussian_cubic_quad.json"), "w") as fh:
        json.dump(base, fh, indent=2)
    print("\nrewrote results/gaussian_cubic_quad.json")


if __name__ == "__main__":
    main()
