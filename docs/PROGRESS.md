# PROGRESS — settling the non-monic cubic discrepancy

Server session started 2026-08-17. Log entries are `date '+%F %T'`.

## 2026-08-17 19:30:32 — start
Read TASK.md, THEOREMS.md, src/reduce_monic.py. Env OK
(.venv: numpy 2.5.2, sympy 1.14.0, mpmath 1.3.0, scipy 1.18.0; 28 cores, 33 GB free).

## 2026-08-17 19:32 — analytic groundwork (before any numerics)
Two things derived by hand first, both to be checked in code:

**(a) Exact band endpoints in factored form.** For `f = a x^3 + b x^2 + c x + d`
with `a > 0` and `sigma = sqrt(b^2 - 3 a c) > 0`, the 3-real-root condition is
`d in [d_lo, d_hi]` with

    d_hi = (b - sigma)^2 (b + 2 sigma) / (27 a^2)
    d_lo = (b + sigma)^2 (b - 2 sigma) / (27 a^2)

(width `4 sigma^3/(27a^2)`, matching THEOREMS.md S1). Substituting
`c = (b^2 - sigma^2)/(3a)` (so `dc = -(2 sigma/(3a)) d sigma`) makes the whole
integrand *piecewise polynomial in sigma*, and every clipping breakpoint is a
root of an explicit cubic. This kills the "find kinks by dense scan + bisection"
step of src/reduce_monic.py and should buy many digits.

**(b) A 4D -> 3D face decomposition (new route).** The real-rooted set
`R = {Delta > 0}` is a cone (Delta is homogeneous of degree 4), so by the
divergence theorem with `F = x/4` (and `x . n = 0` on the lateral boundary since
Euler gives `x . grad Delta = 4 Delta = 0` there),

    vol_4(R n [-1,1]^4) = (1/4) * sum over the 8 faces of area(R n face)
                        = (1/2) (S_a + S_b + S_c + S_d)

where `S_a = vol_3{(b,c,d) in [-1,1]^3 : x^3 + b x^2 + c x + d has 3 real roots}`
and `S_b = vol_3{(a,c,d) : a x^3 + x^2 + c x + d ...}` etc. Reversal
`x -> 1/x`, i.e. `(a,b,c,d) -> (d,c,b,a)`, preserves both R and the box, so
`S_a = S_d` and `S_b = S_c`. Hence

    P = vol/16 = (V(1) + S_b)/16,   V(1) = S_a = 766/1215 + ln(3)/6 (Theorem 1).

This turns the 4D problem into ONE new 3D volume with no `t -> infinity` tail
and no `a -> 0` endpoint blow-up. Numeric target next.

## 2026-08-17 19:36 — first scout number (double precision, scipy quad)
`src/scout_face.py`:

    V(1) computed = 0.8135547230084710   vs exact 766/1215+ln3/6 = 0.8135547230084710
                    (anchor reproduced through the NEW code path, diff 0.0e+00)
    S_b           = 2.6746132840042920   (quad err est 1.2e-12)
    P             = 0.2180105004382977

    dxdy  641/2430 - ln3/24 = 0.2180104962026148   diff +4.2e-09
    sweep 0.217993225       = 0.2179932250000000   diff +1.7e-05

So already at double precision the dxdy candidate is favoured by ~4000x and the
literature-sweep value is refuted by 1.7e-5 (its claimed error bar was 5e-8).
The residual 4.2e-9 is consistent with double-precision quadrature across the
clipping kinks. Next: exact-breakpoint mpmath version for >= 15 digits, the
independent V(t) route, MC, and the symbolic evaluation.

## 2026-08-17 19:45 — EXACT closed form via the face route  (src/face_exact.py)
Swapping the (a,s) integration order makes the whole face integral elementary.
Two lemmas do the work (both algebraic, both re-checked numerically later):

* **L1 (top never clips on the b=1 face)**: `d_hi <= 1` throughout, because
  `alpha_p = sqrt(K_p/27) < a0 = |s^2-1|/3` reduces to `2s+1 < 3(s+1)^2`, true
  for all s. (Analogue of the never-clipped lemma of Theorem 1.)
* **L2 (bottom clips exactly for s in (2/3,2))**: `alpha_m > a0` reduces to
  `(3s-2)(s-2) < 0`; and `alpha_m < 1` reduces to `(s+1)^2(2s-1) < 27`, i.e.
  `s < 2`, with equality exactly at the endpoint s = 2.

Then `F(s) = int_{a0}^1 L/a da` is elementary (the awkward
`-K_p/(2K_m) + 2s^3/K_m` collapses to the constant 1/2 via `K_p+K_m = 4s^3`),
continuous at s = 2/3 (both sides 11264/18225 — sympy PASS), and

    S_b = (4/3) int_0^2 s F(s) ds = 1454/405 - 5 ln(3)/6 = 2.674613216233365...

    P = (V(1) + S_b)/16 = (766/1215 + ln3/6 + 1454/405 - 5 ln3/6)/16
      = 641/2430 - ln(3)/24                      <-- EXACT, sympy: P - cand = 0
      = 0.218010496202614771088984123359...

**This is the dxdy.ru candidate exactly.** The sweep value 0.217993225 is off by
+1.727e-05. Next: the fully independent V(t) route (no divergence theorem) to
confirm to >= 15 digits, plus the MC.

## 2026-08-17 19:45 — Monte Carlo, 4e10 samples (src/nonmonic_mc.py, 800 s, 10 nice'd workers)
40x the 1e9 the brief asked for. Two estimators:

| estimator | p | s.e. | z vs dxdy | z vs sweep |
|---|---|---|---|---|
| RAW sign(Delta), no theory used | 0.218008985275 | 2.06e-06 | **-0.73** | **+7.63** |
| conditional (d integrated out) | 0.218009106962 | 1.20e-06 | **-1.16** | **+13.2** |

The raw estimator uses only `Delta = 18abcd-4b^3d+b^2c^2-4ac^3-27a^2d^2 > 0`, so it
is independent of every reduction in this repo. It excludes the sweep value at
7.6 sigma and is consistent with 641/2430 - ln3/24.

## 2026-08-17 19:48 — verification of the face route (src/face_verify.py)
1. **Cone/divergence identity tested exactly on the quadratic analogue**
   (`q^2 > 4pr` on `[-1,1]^3`, a cone since the discriminant is homogeneous):
   faces give `S_p=S_r=13/6`, `S_q=5/2+ln2`, and `(1/3)*2*(S_p+S_q+S_r) =
   41/9 + (2/3)ln2`, which is EXACTLY `8*(1/2+5/72+ln2/12)`, the known volume.
   Symbolic match, so the decomposition step itself is not an approximation.
2. **F(s) closed form** vs brute-force `int_{a0}^1 L/a da`: agrees to 1e-16 at
   13 values of s spanning all three regimes (only the s=1.99 edge point is
   worse, 1e-10, and that is scipy's problem, not the formula's).
3. **Lemmas by 2e6-point scan**: L1 holds everywhere; the clipping window comes
   out numerically as s in [0.6666677, 2.0000000] vs the claimed (2/3, 2);
   max alpha_m = 0.999999999 <= 1 as claimed.
4. **S_b three ways**: sympy exact `1454/405 - 5ln3/6`, mpmath quadrature of the
   closed-form F(s) = same to **3.9e-31**, brute 2D (a,s) scipy = same to 6.8e-8.
5. **S_c (the c=1 face) computed independently** = 2.674613006 vs S_b =
   2.674613216 (diff 2.1e-7, at the tolerance of that crude quadrature) —
   confirms the reversal symmetry S_b = S_c used in the decomposition.
6. **PSLQ, blind**: from the 22-digit numeric S_b, PSLQ returns
   `-810*S_b + 2908 - 675*ln3 = 0`, i.e. `S_b = 1454/405 - (5/6) ln 3`.
   Independent recovery of the closed form from the numerics alone.

## 2026-08-17 20:04 — route 1 (V(t)) hardened and relaunched
Route 1 is the fully independent confirmation: it never uses the face
decomposition. Structure: sigma-substitution => the innermost integral is exact
(piecewise polynomial, breakpoints = roots of explicit cubics); then quadrature
in b, then in a.

Anchors through this code path (dps 40):

    V(1)      = 0.813554723008470956796326881051  vs 766/1215+ln3/6, |err| 1.1e-41
    depressed = 0.0769800358919501019345531707336 vs 2 sqrt(3)/45,   |err| 0
    p(1)      = 0.101694340376058869599540860131  vs 383/4860+ln3/48,|err| 1.4e-42
    V(t) direct vs V(t) = 8 p(1/t)/a^3 : agree to 1e-41 for t = 1, 1.5, 2, 3
        (t = 5, 10: the DIRECT V(t) code loses to ~1e-11 because its A-scan
         misses kinks at large t; the p-route values are the reliable ones.)

Three numerical-conditioning traps found and fixed (each one silently costs
digits — plausibly how the literature sweep landed 1.7e-5 off):

1. **a -> 0 is a sqrt(a) endpoint, not a smooth one.** Measured:
   `p(a) = p(0) - (2/3) sqrt(a) + ...` with p(0) = 1/2 + 5/72 + ln2/12 =
   0.6272067094911065536 (the random-quadratic limit, since the third root runs
   off to -b/a). The measured coefficient converges to 0.66666678 at a = 1e-5.
   Plain Gauss nodes on such an endpoint lose ~7 digits (verified directly:
   GL degree 6 on int_0^1 sqrt(x)e^x is off by 1.1e-7 while tanh-sinh is exact).
   Handled by tanh-sinh + the substitution a = v^2 on [0,1e-4].
2. **The cubic P_p = U has a near-double root at sigma = b.** Its two branches
   are ~sqrt(U/3b) apart, which float64 destroys once U << b^3, i.e. for small
   leading coefficient. Solving in the shifted variable z = sigma - b
   (`2z^3+3b z^2-U`) removes the cancellation; before the fix the kink scan
   reported 105 phantom breakpoints at a = 1e-9, after it reports 4.
3. **The b-structure migrates to b ~ sqrt(3a).** A linear 400-point scan in b
   walks straight past it; at a = 1e-6 it missed three real kinks and cost
   ~1e-9 relative accuracy in p(a). Fixed with a linear+logarithmic scan grid.
   After the fix p(a) is converged (inner degree 8 vs 10) to 1e-15 at a = 1e-6
   and to 0 at a >= 1e-4. Working precision is also raised as
   dps ~ 40 + 2.2 log10(1/a) to cover the cancellation in the exact
   antiderivatives.

## 2026-08-17 20:12 — V(t) table (src/vt_table.py) and a convergence caveat
V(t) computed two ways: the direct A-order (monic variables, the literal V(t) of
the brief) and the b-order via the scaling identity V(t) = 8 t^3 p(1/t).

    V(1)    = 0.8135547230084709567963269   = 766/1215 + ln3/6 to 1.1e-41
    V(1.25) = 1.896072321154865367226615    (agree 1.1e-41)
    V(1.5)  = 3.779704487957479836999049    (agree 2.4e-41)
    V(2)    = 11.08836062582113115207304    (agree 5.7e-42)
    V(3)    = 49.18994594136796017449959    (agree 1.9e-41)
    V(5)    = 311.2172038042818798493448    (b-order; A-order 2.7e-12 off)
    V(10)   = 3283.333305772980494564387    (b-order; A-order 1.7e-12 off)
    depressed-cubic anchor 2 sqrt(3)/45 reproduced exactly (|err| 0).

For t >= 4 the A-order loses ~1e-12 relative; refining its scan and degree walks
it back toward the b-order value (t=5: 311.2172038051 -> ...42532 -> ...42884
vs b-order ...42819), so the b-order values are the accurate ones and are what
feed P. Recorded rather than papered over.

## 2026-08-17 20:13 — post-mortem: my reconstruction does NOT reproduce the sweep value
Running plain nested `scipy.quad` (no kink splitting, no endpoint treatment) on
the same interval-length reduction at eps=1e-8 gives **P = 0.218010497101**,
only 9.0e-10 from the exact value — i.e. a naive scipy pipeline of this shape
already gets the right answer to 9 digits and does NOT land on 0.217993225.
So the three genuine hazards documented above (sqrt(a) endpoint, migrating
kinks, float breakpoint loss) are real, but they do not by themselves explain
the sweep's 1.7e-5 error; something more specific in that setup did, and the
recorded metadata is not enough to reconstruct it. VERDICT.md will say exactly
this rather than assert a mechanism.

## 2026-08-17 20:20 — route 1 restructured (src/route1_closed_a.py)
The nested version (src/nonmonic_vt.py) reproduces every anchor to 1e-41 and is
kept for that (log: results/vt_nested_anchors.log), but its outer a-quadrature
is the weak link: p(a) has genuine kinks in a whose locations cannot be pinned
down reliably by a float structure scan (the fingerprint itself fluctuates), and
each p(a) at a ~ 1e-11 costs ~40 s, so panels cannot simply be refined.

Fix: **do the a-integral in closed form instead of numerically.** In

    P = (1/6) int_0^1 (da/a) int_0^1 db int sigma L dsigma

the leading coefficient enters ONLY through u = 27a^2, so swapping the order and
integrating a first is elementary — the same move that made the face route
exact. That leaves

    P = (1/6) int_0^1 db int_0^{sqrt(b^2+3)} sigma G(b,sigma) dsigma

with G in closed form (sqrt and log only; no root finding, no nested quadrature,
no small-a cancellation). G verified against direct numerical
`int_{a0}^1 L/a da` at 8 points spanning every regime: agreement 0 to 2e-16.
G's only singularity is an integrable log on the curve sigma = b, which is put
at a panel endpoint. Now running with tanh-sinh and Gauss-Legendre at several
degrees for the method-comparison evidence.

## 2026-08-17 20:21 — ROUTE 1 CONFIRMS THE EXACT VALUE
`src/route1_closed_a.py`, Gauss-Legendre degree 5 over the b-panels (70 s):

    route 1 (leading-coefficient route)  P = 0.218010496202614695372980026366
    exact  641/2430 - ln(3)/24             = 0.218010496202614771088984123359
    difference                             = -7.6e-17

**16 significant digits, from a route that uses none of the face
decomposition** — no divergence theorem, no reversal symmetry, no Theorem 1.
Higher degrees and the tanh-sinh comparison are still running.

## 2026-08-17 20:32 — a real bug found in route 1b, and fixed
First run of route 1b converged beautifully (GL degrees 5/6/7 agreeing to 3e-19)
but sat a systematic **7.4e-17** below the exact value — 300x its own apparent
convergence. Chased it down rather than accepting it:

* G(b,sigma) itself is right: re-validated against direct mp quadrature of
  `int_{a0}^1 L/a da` at 16 points including sigma -> b, sigma -> b/2,
  sigma -> 0 and random points — max relative difference **1.6e-35**.
* the sigma-integration is stable: refining the sigma scan 15x changes I(b) by
  exactly 0 at 30 digits.
* the culprit was in the b-panel list. The kink scan returns a spurious cut at
  **b = 0.9999999999999998 = 1 - one ulp**, and the panel loop's
  `if x1 - x0 < 1e-13: continue` guard then dropped that sliver from the
  integral altogether. Deficit = I(1) * 2.22e-16 / 6 = 7.4e-17 — the observed
  bias to the digit.

Fixed by dropping the offending *cut point* instead of the *interval*
(`clean_panels`), and by pinning the sigma = b panel endpoint (where G has its
log singularity) to full mp precision rather than its float64 rounding.

After the fix:

    GL degree 5: 0.218010496202614769578850684779   (exact - this = +1.5e-18)
    GL degree 6: 0.218010496202614771186280767570   (exact - this = -9.7e-20)
    exact       0.218010496202614771088984123359

**~19 significant digits, from the route that uses none of the face
decomposition.** tanh-sinh comparison still running.

## 2026-08-17 20:50 — second numerical trap in route 1b (tanh-sinh -> +inf)
The Gauss-Legendre passes were fine but both tanh-sinh passes returned +inf.
Cause: tanh-sinh clusters nodes double-exponentially at panel endpoints, and one
endpoint is sigma = b, exactly where G has its log singularity. Two compounding
issues:

* `a0 = |sigma^2 - b^2|/3` rounds to exactly 0 as soon as sigma is within a
  working-precision epsilon of b (the expanded form loses the difference).
  Rewriting it factored, `a0 = |sigma-b|(sigma+b)/3`, pushes the failure out to
  the point where sigma itself rounds onto b.
* Raising the working precision makes this WORSE, not better: mpmath places
  tanh-sinh nodes closer to the endpoints at higher precision, so degree 7 GL
  also fell over when dps was bumped. Precision is not the lever here.

Correct fix: floor a0 at 2^(-2 prec) when it underflows. G diverges only
logarithmically there and the quadrature weight at such a node is ~2^-prec, so
the substitution is harmless — while a single inf poisons the entire sum.
Re-running all five method/degree passes.

## 2026-08-17 20:58 — ROUTE 1 FINAL, all five passes
`src/route1_closed_a.py`, 56 b-panels, dps 40:

    gauss-legendre deg 5  0.218010496202614769578850684778839182   -1.5e-18
    gauss-legendre deg 6  0.218010496202614771186280767569990715   +9.7e-20
    gauss-legendre deg 7  0.218010496202614770896727194507463389   -1.9e-19
    tanh-sinh      deg 5  0.218010496202614770731237427650885106   -3.6e-19
    tanh-sinh      deg 6  0.218010496202614771018504937142472413   -7.0e-20
    exact 641/2430-ln3/24 0.218010496202614771088984123358680771

Method spread 1.6e-18; best pass agrees with the exact closed form to **7.0e-20**
(19 significant digits). Route 1 uses no part of the face decomposition, so this
is an independent confirmation of the exact result, not a consistency check.

## 2026-08-17 20:58 — deliverables written
* `results/nonmonic_quadrature.json` — deliverable 1 (anchors + V(t) table +
  route-1 P with method/degree evidence + cross-links).
* `VERDICT.md` — deliverable 4, with the decisive digits side by side.
* Stretch goal: the exact closed form was obtained (route 2), but by radial
  rather than level-set integration. Recorded there as a negative result:
  V(t) itself is very likely NOT elementary — PSLQ on 40-digit p(1/2) and
  p(1/3) against {1, ln2, ln3, ln5, sqrt2, sqrt3, pi} with maxcoeff 1e10 returns
  only junk relations, and mpmath.identify finds nothing. V(1) is elementary
  because t = 1 is exactly where Theorem 1's corner-touching geometry applies.

## Summary of the verdict
**P = 641/2430 - ln(3)/24 = 0.21801049620261477108898412335868...**
The dxdy.ru candidate is CONFIRMED (symbolically identical). The
literature-sweep value 0.217993225 +- 5e-8 is REFUTED, wrong by +1.7271e-05.
No third value appeared anywhere in this campaign.

## Note for the operator: one typo in TASK.md
TASK.md's verification section says *"V(1) must give 766/1215 + ln(3)/6 =
1.813556..."*. The value of `766/1215 + ln(3)/6` is **0.8135547230084709568**,
not 1.813556 — a stray leading 1. Everything else in the brief is consistent
with 0.81355 (e.g. "at a=1 the integrand is V(1)/8 = 0.101694340376" is exactly
0.8135547/8), so this is a typo, not a different convention. All work here uses
V(1) = 0.8135547230084709568 = 8 x Theorem 1.
