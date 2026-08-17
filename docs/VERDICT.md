# VERDICT — the non-monic cubic

**Question.** `P( a x^3 + b x^2 + c x + d has 3 real roots )`, `(a,b,c,d)` iid `U[-1,1]`.

**Answer.** The dxdy.ru candidate is **correct**, and it is now *proved*, not just
matched numerically:

> **P = 641/2430 − ln(3)/24 = 0.2180104962026147710889841233594…**

The literature-sweep quadrature value **0.217993225 ± 5e-8 is wrong**, by
**+1.7271e-05** — about 345 times its own claimed error bar.

## The decisive digits, side by side

| | value | P − this |
|---|---|---|
| **This campaign, exact** (`641/2430 − ln3/24`) | `0.21801049620261477109` | — |
| dxdy.ru candidate (June 2026) | `0.21801049620261477109` | `0` (symbolically identical) |
| Literature-sweep quadrature | `0.21799322500000000000` | `+1.7271e-05` |

The two computations that matter most are the exact symbolic evaluation and the
numerical route that shares no step with it. Digit by digit:

```
exact  (641/2430 - ln3/24)   0.218010496202614771088984123358680771
route 1, tanh-sinh degree 6  0.218010496202614771018504937142472413   diff -7.0e-20
route 1, Gauss-Legendre  6   0.218010496202614771186280767569990715   diff +9.7e-20
route 1, Gauss-Legendre  7   0.218010496202614770896727194507463389   diff -1.9e-19
route 1, tanh-sinh degree 5  0.218010496202614770731237427650885106   diff -3.6e-19
route 1, Gauss-Legendre  5   0.218010496202614769578850684778839182   diff -1.5e-18
literature sweep             0.2179932250000000000000000000000000     diff +1.7e-05
```

Nineteen significant digits of agreement, across two quadrature families and
three degrees each (spread `1.6e-18`). The sweep's value disagrees in the
**fifth** digit.

## What supports it

Two of these are genuinely independent of each other — route 1 and route 2 share
no step. The rest are internal checks of route 2 and of the reduction itself.

| method | result | agreement |
|---|---|---|
| **route 2 — exact symbolic** (face decomposition, sympy) | `641/2430 − ln3/24` | `P − candidate = 0`, symbolically |
| **route 1 — the leading-coefficient / V(t) route**, sharing no step with route 2 | `0.21801049620261477102` | `7.0e-20` (19 digits) |
| Monte Carlo, 4×10^10 samples, raw `sign(Δ)` — uses no theory from this repo | `0.218008985 ± 2.1e-6` | `−0.73 σ`  (sweep: `+7.6 σ`) |
| — same run, `d` integrated out analytically | `0.218009107 ± 1.2e-6` | `−1.16 σ` (sweep: `+13.2 σ`) |
| *(internal)* mpmath quadrature of route 2's closed form `F(s)` | `S_b` to 30 digits | `3.9e-31` |
| *(internal)* **blind PSLQ** on the 22-digit numeric `S_b` | returns `1454/405 − (5/6)ln3` | recovers the closed form unprompted |
| *(internal)* the cone identity itself, tested on the quadratic analogue | exact match | see below |
| *(internal)* double-precision brute force (`scipy`, raw variables) | `0.2180105004` | `4.2e-9`, that method's kink limit |

The cone identity is the one genuinely new structural step, so it was tested
where the answer is known independently: for `q² > 4pr` on `[-1,1]³` (also a
cone, the discriminant being homogeneous) the three faces give `S_p = S_r = 13/6`
and `S_q = 5/2 + ln 2`, so `(1/3)·2·(S_p+S_q+S_r) = 41/9 + (2/3)ln2` — which
*is* `8·(1/2 + 5/72 + ln2/12)`, the known volume. Symbolic match, so the step is
an identity and not an approximation.

Anchors, reproduced through the new code paths before any new number was
believed: `V(1) = 766/1215 + ln3/6` to `1.1e-41`, the depressed-cubic anchor
`2√3/45` exactly, `p(1) = 383/4860 + ln3/48` to `1.4e-42`.

## How the closed form is obtained

The key is that the real-rooted set `R = {Δ > 0}` is a **cone**: the discriminant

    Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²

is homogeneous of degree 4, so `Δ(λx) = λ⁴ Δ(x)` and `R` is invariant under
`x → λx`. Apply the divergence theorem to `F = x/4` (`div F = 1`) on `R ∩ [-1,1]⁴`.
Euler's identity gives `x·∇Δ = 4Δ = 0` on the lateral boundary `{Δ = 0}`, so that
part of the surface integral vanishes and only the eight faces of the cube
survive. Central symmetry `(a,b,c,d) → (−a,−b,−c,−d)` pairs them up, and the
reversal `x → 1/x`, i.e. `(a,b,c,d) → (d,c,b,a)`, gives `S_a = S_d`, `S_b = S_c`:

    vol₄(R ∩ [-1,1]⁴) = ½ (S_a + S_b + S_c + S_d) = V(1) + S_b,
    P = vol₄/16 = ( V(1) + S_b ) / 16

with `S_a = V(1) = 766/1215 + ln3/6` already proved (Theorem 1) and

    S_b = vol₃{ (a,c,d) ∈ [-1,1]³ : a x³ + x² + c x + d has 3 real roots }.

So a 4-dimensional problem becomes **one** 3-dimensional one — and with no
`t → ∞` tail and no `a → 0` endpoint blow-up, which is where the sweep's
quadrature died.

`S_b` is then elementary. Writing `s = √(1−3ac)` (so `c = (1−s²)/(3a)`), the band
of admissible `d` is `[−K₋/u, K₊/u]` with

    K₊ = (s−1)²(2s+1),   K₋ = (s+1)²(2s−1),   u = 27a²,   K₊ + K₋ = 4s³,

the domain is `{ s ∈ (0,2), a ∈ [|s²−1|/3, 1] }`, and — this is the move —
integrating over **`a` first, at fixed `s`**, makes everything elementary,
because `a` enters only through `u = 27a²`. Two lemmas:

* **L1 (the band never clips above).** `d_hi ≤ 1` throughout, since
  `α₊ = √(K₊/27) < a₀ = |s²−1|/3` reduces to `2s+1 < 3(s+1)²`, true for all `s`.
  This is the exact analogue of the never-clipped lemma behind Theorem 1.
* **L2 (it clips below exactly for `s ∈ (2/3, 2)`).** `α₋ = √(K₋/27) > a₀`
  reduces to `(3s−2)(s−2) < 0`; and `α₋ < 1` reduces to `(s+1)²(2s−1) < 27`,
  i.e. `s < 2`, with equality precisely at the endpoint `s = 2`.

Then `F(s) = ∫_{a₀}^1 L/a da` is elementary — the awkward `−K₊/(2K₋) + 2s³/K₋`
collapses to the constant `1/2` via `K₊ + K₋ = 4s³` — and

    F(s) = (2s³/27)(1/a₀² − 1)                                    for s ≤ 2/3
    F(s) = K₊/(54a₀²) + 1/2 + ln(α₋/a₀) − 2s³/27                  for 2/3 < s < 2

(continuous at `s = 2/3`; both sides `11264/18225`). Finally

    S_b = (4/3) ∫₀² s F(s) ds = 1454/405 − (5/6) ln 3 = 2.674613216233365…
    P   = ( 766/1215 + ln3/6 + 1454/405 − 5ln3/6 ) / 16 = **641/2430 − ln(3)/24**.

sympy confirms `P − (641/2430 − ln3/24) = 0` exactly.

## Why the sweep's number was wrong

Honest answer first: **I could not reproduce the failure.** The sweep's recorded
method is *"scipy 1e-12 dblquad / tplquad on the exact interval-length
reduction"*. Running exactly that shape — plain nested `scipy.quad`, no kink
splitting, no endpoint treatment, `eps = 1e-8` — gives

    P = 0.218010497101      (9.0e-10 from the exact value)

So a naive scipy pipeline on this reduction already gets 9 correct digits and
does *not* land anywhere near `0.217993225`. Whatever went wrong in the sweep
was specific to its own setup, and the recorded metadata does not pin it down.
What can be said is that its error bar was an internal `scipy` estimate — a
quantity that in this problem is demonstrably not trustworthy — and that its own
Monte Carlo runs were pointing at the right answer and were overruled.

That said, this integrand *does* carry three real hazards, all concentrated at
small leading coefficient `a`, all invisible to a Gauss–Kronrod error estimate,
and all of which had to be fixed to reach 15+ digits here:

1. **The `a → 0` endpoint is a square-root singularity, not a smooth point.**
   The conditional probability given the leading coefficient satisfies
   `p(a) = p(0) − (2/3)√a + …`, with `p(0) = 1/2 + 5/72 + ln2/12 = 0.6272067…`
   (as `a → 0` the third root escapes to `−b/a` and the event degenerates to
   `c² > 4bd`, the random-quadratic problem). Measured coefficient: 0.66666778
   at `a = 1e-5`. A Gauss rule on a `√a` endpoint loses roughly seven digits and
   reports none of it — verified directly: on `∫₀¹ √x e^x dx`, Gauss–Legendre at
   degree 6 is off by `1.1e-7` while tanh–sinh is exact to working precision.
2. **The kink structure migrates to `b ~ √(3a)` as `a → 0`.** Any fixed scan or
   panel layout in `b` walks straight past it; at `a = 1e-6` a 400-point linear
   scan misses three real kinks and costs `~1e-9` relative accuracy in `p(a)`.
3. **Float64 loses the clipping breakpoints entirely for small `a`.** The
   breakpoint cubic `P₊ = U` has a near-double root at `σ = b` whose branches sit
   only `√(U/3b)` apart; once `U = 27a² ≪ b³` that separation is below float
   resolution. Before fixing this (by solving in the shifted variable
   `z = σ − b`), our own structure scan reported **105 phantom breakpoints** at
   `a = 1e-9`; afterwards it reports 4.

The sweep's own notes already recorded the symptom — *"the scipy/dblquad error
estimates were optimistic by ~4e-11 near C¹ kinks"* — and that its three Monte
Carlo runs pooled to `0.218017 ± 0.000022`, about 1σ **above** its quadrature
value. Both were correct warnings: the MC was right and the quadrature was not.

And they are not a hypothetical worry: chasing 15+ digits here turned up two
further traps of exactly this kind *in this campaign's own code*, both caught
only because a route was cross-checked against an exact value rather than
against its own convergence estimate:

* a spurious kink at `b = 1 − 2.2e-16` (one ulp) whose sliver a
  `if panel_width < tol: continue` guard silently dropped — a bias of `7.4e-17`,
  three digits, while the method's internal degree-doubling claimed `3e-19`;
* `|σ² − b²|` rounding to exactly zero at the tanh-sinh nodes clustered on the
  log singularity `σ = b`, turning the whole integral into `+inf` (and getting
  *worse*, not better, when the working precision was raised).

The lesson the sweep's number teaches is not about `scipy` specifically. It is
that on this integrand a quadrature routine's own error estimate is not
evidence, and only agreement between structurally different computations is.

## Status of each candidate

* **`641/2430 − ln(3)/24` — CONFIRMED**, and now proved: a complete derivation
  exists (above), verified symbolically in sympy, reproduced to 19 significant digits by an
  independent numerical route that shares no step with it, recovered blind by
  PSLQ, and consistent with 4×10^10 Monte Carlo samples.
* **`0.217993225 ± 5e-8` — REFUTED.** It is `1.7271e-05` too small, roughly 345
  times its own error bar. That error bar was a `scipy` internal estimate, which
  on this integrand is not a measurement of anything: even a correctly written
  naive pipeline saturates near `1e-9` while reporting `2e-11`. The specific
  mechanism that took the sweep all the way to `1.7e-05` could not be
  reconstructed from what it recorded.
* **No third value.** Every route here lands on `641/2430 − ln(3)/24`.

## The stretch goal, and a negative result worth recording

The brief's stretch goal was to get `V(t)` in closed form piecewise in `t` and
then evaluate `P = ∫₀¹ (a³/8) V(1/a) da` exactly. The exact evaluation was
achieved — but by a different order of integration, and there is a reason the
suggested path is the hard one.

The closed form exists **because of the cone structure**, and the cone structure
is only visible when the *scale* is the innermost variable. Integrating `a`
first (radially) at fixed shape leaves elementary integrands; the reverse order
leaves integrals of algebraic functions of the roots of a cubic whose
coefficients move with the outer variable, which is not elementary in general.
`V(t)` at a fixed `t ≠ 1` looks like exactly that. Evidence:

* `p(1/2) = 0.173255634778455174251141172449419764456…`
* `p(1/3) = 0.227731231210036852659720324839651789782…`

(where `p(a) = a³V(1/a)/8` is the conditional probability given the leading
coefficient; both to 40 digits). PSLQ against `{1, ln2, ln3, ln5, √2, √3, π}`
with `maxcoeff = 10^10` returns only junk relations with 5-digit coefficients,
and `mpmath.identify` finds nothing. That is not a proof, but it is a clear
signal that `V(t)` is not elementary in the naive constants even though
`∫₁^∞ V(t) t⁻⁵ dt` is. `V(1)` is elementary because `t = 1` is exactly the
value at which the never-clipped lemma of Theorem 1 applies — the corner-touching
geometry — not because `V` is nice in general.

So the closed form was obtained by cutting the 4D cone with its own faces
(`P = (V(1)+S_b)/16`) rather than by slicing it into `V(t)` levels. A table of
`V(t)` to 25 digits for `t = 1 … 50` is in `results/vt_table.json` regardless,
computed two ways, with `V(1)` reproducing `766/1215 + ln3/6` to `1.1e-41`.

## What this means for the dxdy.ru thread

The thread's `V(1) = 766/1215 + ln3/6` agrees with Theorem 1 (proved in this
repo), and its final `641/2430 − ln(3)/24` is now confirmed exactly. Its
remaining steps therefore reach the right answer, though nothing here validates
the route it took to get there — this is an independent derivation, not a
verification of theirs.

## Where everything is

| file | what |
|---|---|
| `results/nonmonic_quadrature.json` | deliverable 1: anchors, `V(t)` table, route-1 P with method/degree evidence, cross-links to routes 2 and MC |
| `results/route1_closed_a.json` | route 1 raw output (5 method/degree passes, 56 b-panels) |
| `results/face_exact.json` | the exact symbolic evaluation (`S_b`, `P`, and `P − dxdy = 0`) |
| `results/face_verify.json` | cone identity on the quadratic analogue, `F(s)` checks, lemma scans, `S_c` cross-check, blind PSLQ |
| `results/nonmonic_mc.json` | 4×10^10-sample Monte Carlo, both estimators |
| `results/vt_table.json` | `V(t)`, `t = 1 … 50`, both integration orders |
| `results/weighted_cone_check.json` | the fixed-`a` weighted-cone identity, checked against raw-discriminant grid areas |
| `results/sweep_postmortem.json` | naive-scipy reconstruction attempts |
| `src/route1_closed_a.py` | route 1 |
| `src/face_exact.py`, `src/face_verify.py` | route 2, exact and verified |
| `src/nonmonic_vt.py`, `src/vt_table.py` | `V(t)` and `p(a)` by nested quadrature (anchors, the `V(t)` table) |
| `src/nonmonic_mc.py` | Monte Carlo |
| `PROGRESS.md` | the running log, including every trap found and every discrepancy |

## Suggested amendment to THEOREMS.md

The last paragraph of THEOREMS.md ("Bonus lead … settling that discrepancy with
this project's machinery is next on the target list") is now answered, and the
result is a third theorem in the same family:

> **Theorem 3.** Let `(a,b,c,d)` be i.i.d. uniform on `[−1,1]`. Then
> `P( a x³ + b x² + c x + d has three real roots ) = 641/2430 − ln(3)/24`
> `= 0.21801049620261477108898412335868…`

with `V(1) = 766/1215 + ln3/6` (Theorem 1) and the new
`S_b = 1454/405 − (5/6) ln 3` as its two ingredients. Unlike Theorems 1 and 2,
this one is **not** new as a *value* — it is the dxdy.ru thread's June 2026
candidate. What is new here is a derivation of it, and the retraction of the
`0.217993225` figure.
