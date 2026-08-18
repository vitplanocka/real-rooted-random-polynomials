# VERDICT — two open problems in random-polynomial real-rootedness

Campaign of 2026-08-18 (`TASK2.md` Phase 2), follow-on to the non-monic cubic
campaign. Evidence standard deliberately matched to that campaign's
`VERDICT.md`: **nothing is called exact without at least two structurally
independent confirmations**, and a quadrature routine's own error estimate is
never treated as evidence. Where only one route exists, it is labelled
*provisional* rather than promoted.

Full working log: `PROGRESS.md`.

---

## Problem A — monic cubic, Gaussian coefficients

> `P( x³ + ax² + bx + c has 3 distinct real roots )`, `(a,b,c)` i.i.d. `N(0,1)`.

### Status: **best numeric, no closed form found** (TASK2.md's "acceptable case")

    P_A = 0.16992938262347950265644315713176190213405726145463153…

**~54 digits.** Prior best was Monte Carlo `0.169962 ± 4.2e-5` — five significant
digits. That is an improvement of order **10⁵⁰** in precision.

### Evidence

| route | agreement |
|---|---|
| coefficient space, method C (main + variant mesh) | 79 digits between meshes |
| root space, method R (main + variant mesh) | 54 digits vs C |
| mpmath-native tanh–sinh, method T (shares no numerical code) | 52 digits vs C |
| **spread over all four C/R runs** | **4.95e-56 → 54 digits common** |
| root-space *gap* reparametrisation (independent, main thread) | 12 digits (its float64 ceiling) |
| Monte Carlo | −0.78σ |

Truncation of the Gaussian tails is rigorously bounded (`5.5e-89` for C,
`5.1e-80` for R), so the tails are not the limiting factor; the 54 digits are a
quadrature-agreement statement.

### The closed-form search, and why its negative is trustworthy

The search pipeline was **calibrated first** on constants whose closed form is
known, each presented at exactly 50 digits like `P_A`:

* `383/4860 + log3/48` (the previous campaign's Theorem 1) — recovered, margin 43.9 digits
* `+ Catalan/17` (2 constants) — recovered, margin 35.9 digits
* `1/7 + log2/5 + G/3 + √3/11` (3 constants) — recovered, margin 41.8 digits

The first coefficient bound tried **failed** the second calibration (whose true
relation needs `maxcoeff 330480`); bounds were widened before the real run. A
negative from an uncalibrated pipeline would have been worthless.

Then: **55 named constants** × **21 transformations** of the value ×
`mpmath.identify` at 3 tolerances × PSLQ at 1, 2 and 3 terms with coefficient
bounds `1e10/1e8/1e6` (plus an over-permissive `1e16` sweep) —
**583 330 PSLQ subset calls**. Rationality tested to `maxcoeff 1e24`;
algebraicity for degrees 2,3,4,5,6,8.

**Zero relations and zero `identify` hits.** Nothing even reached the
over-determination test. A structureless control shows PSLQ only starts
manufacturing junk at `maxcoeff 1e25`, where relations "spend" 65.6 digits
against 54 available (margin −11.6); the same probe on `P_A` gives margins
−10.9 to −14.8. That is what junk looks like here, and nothing came close.

**Honest scope**: this excludes the *standard repertoire at credible coefficient
sizes*. A closed form could still involve a constant outside the 55-element pool
(e.g. a period specific to the discriminant surface), more than three basis
elements, or larger coefficients.

### Novelty

No prior art found: OEIS returns nothing for eight distinct truncations, and
contains no all-roots-real probability for *any* ensemble (searching
`"random polynomial" "real roots"` returns exactly two sequences in the whole
database, both about expected *counts*). Web and StackExchange searches are
clean. Edelman–Kostlan (arXiv:math/9501224) was downloaded and grepped: it
contains no all-roots-real result. **Caveat**: Li (1988) is unread (see below).

---

## Problem B — monic quartic, uniform coefficients

> `P( x⁴ + bx³ + cx² + dx + e has 4 distinct real roots )`, `(b,c,d,e)` i.i.d. `U[-1,1]`.

### Status: **structure solved; 99.27 % of the answer is in closed form; the remainder is a single explicit correction, numerically evaluated**

    P_B = 0.005464330340589985545194403283287741146329
                    (~41 digits; ~14 confirmed by an independent route — see Evidence)

### What is proved exactly

These are derived symbolically **and** verified numerically; I regard them as
established.

1. **Normal form.** Every monic quartic is a perfect square plus a *linear*
   function:

       x⁴+bx³+cx²+dx+e = (x²+px+q)² + δx + ε,
       p = b/2,  q = c/2 − b²/8,  δ = d − (bc/2 − b³/8),  ε = e − q².

   The map `(b,c,d,e) ↦ (p,q,δ,ε)` is lower-triangular with Jacobian exactly `1/4`.
   (sympy: residual exactly `0`.)

2. **The band length factorises.** With `m = 3b²/16 − c/2` and `τ = δ/m^{3/2}`,

       L(b,c,d) = m² · Λ(τ),

   and `f` has three real critical points iff `m > 0` and `|τ| < τ_c = 8/(3√3)`
   (0 mismatches in 4000 tests; `L` verified to median 4.4e-16).

3. **`Λ` in closed form — the exact analogue of the cubic's `(4/27)s³`.**
   Parametrising by `S ∈ [1, 2/√3]` via `τ = 4S(S²−1)`,

       **Λ = S (4 − 3S²)^{3/2}**

   (max deviation 7.8e-16). Same `3/2` power as the cubic band width.

4. **A rational universal constant.**

       **K = ∫_{−τ_c}^{τ_c} Λ(τ) dτ = 128/105**   (exactly)

   via `u = 4 − 3S²`: `K = (4/3)∫₀¹ (3−u)u^{3/2} du = (4/3)(6/5 − 2/7)`.
   sympy confirms; `scipy.quad` gives `1.21904761904762`.

5. **The unclipped integral is closed-form.** `db dc dd = 2m^{3/2} db dm dτ`, and
   the constraint `|c| ≤ 1` is *exactly* `0 < m ≤ M(b) := (3b²+8)/16`. Dropping
   only `|d| ≤ 1`, the integral factorises completely:

       16 P_B(unclipped) = (4K/9)·2^{−18} ∫_{−1}^{1} (3b²+8)^{9/2} db
                         = **√3·asinh(√6/4)/90 + 7013√11/302400**
                         = 0.0880669596606268607…

   (`asinh(√6/4) = log((√6+√22)/4)`.) Same shape as Theorem 1's
   `3064/1215 + (8/3)asinh(1/√3)`.

   **`U` rests on four independent legs**: symbolic derivation (main thread);
   independent sympy re-derivation (Agent B2); a 200-dps quadrature of the
   reduction agreeing to **192 digits**; and — sharing *no algebra at all* with
   the `(m,τ,Λ)` derivation — a raw `(b,c,d)` quadrature over the *unclipped*
   `d`-band using only `crit_points` and `g`, agreeing to **6.2e-14**. By this
   campaign's standard, `U` is established.

6. **The clipping onset is a cubic irrational.** The `d`-band first leaves
   `[-1,1]` where `8(b³+4b+8)/(3b²+8)^{3/2} = 8/(3√3)`, i.e. where

       **27b³ − 9b² + 108b + 76 = 0**,   b* = −0.6143021014162960827521478…

   (irreducible; single real root). This *derives* the constant `0.6143021014162962`
   that an earlier attempt had fitted numerically by hand. (Agent B2 found the
   same constant independently as the root of `27b³+9b²+108b−76` — the same number
   under the opposite sign convention; verified, the two roots sum to 0.)

### What remains

    16 P_B = [ √3·asinh(√6/4)/90 + 7013√11/302400 ] − C_clip,
    C_clip = 0.000637674211187091936250935532440028016216419
             (the same integral restricted to |d| > 1)

**The clipping correction is only 0.724 % of the total.** No closed form for
`C_clip` has been found, by two searches of very different depth. The deeper one
(Agent B2) ran PSLQ at **190 digits**: no algebraic relation of degree ≤ 10 with
coefficients ≤ 1e14, and no hit against a 17-constant pool. The first (main
thread) ran at 41 digits on both `C_clip` and `16 P_B`
over a **structure-informed** 25-constant basis — the constants the derivation
actually produces (`√2,√3,√6,√11,√22,√33, π, log2, log3, asinh(√6/4),
√3·asinh(√6/4)`, the cubic irrational `b*` and `b*²`, and
`u₀=√(3b*²+8)` with `u₀^{3,5,7,9}`, `b*u₀^{3,5,7,9}`, `A₀=asinh(b*√3/(2√2))`,
`√3·A₀`) at k = 1,2,3 terms and `maxcoeff` 1e8/1e6, with an over-determination
filter of "digits spent < 25" against 41 available. **Nothing survived.**
The 190-digit search also covered a **purpose-built** basis `{b*^i·g}` with
`g ∈ {1, √(3b*²+8), asinh(√6·b*/4), √11, √3·asinh(√6/4), …}` — i.e. the field the
derivation actually generates — and returned only the trivial identity
`R² = 3b*² + 8` (with coefficient 0 on `C_clip`). As a control, the same code
recovers `U`'s closed form immediately.

**Structural reason for pessimism** (Agent B2): the clipped region's boundary is
`τm^{3/2} − bm + b³/16 = ±1`, an algebraic surface, integrated against 3/2- and
5/2-power weights, so the `b`-integral runs over a **high-genus curve**. An
elementary closed form should not be expected. So **Problem B is not solved**:
`16 P_B = U − C_clip` with `U` exact and `C_clip` transcendental-looking.

### Evidence, and an explicit caveat about it

* Two **differently arranged** evaluations of the same reduction agree to
  **17 digits** (impose `|d|≤1` as `τ`-limits directly, versus
  unclipped-minus-correction), and the value is stable to 41 digits at dps 50.
* **Independently reproduced**: a separate implementation (Agent B2) gives
  `P_B = 0.0054643303405899855451944032832877411463288609119348`, agreeing with
  the main-thread value to **~40 digits**. That agent also verified the closed
  form `U` against its own 200-dps quadrature to **192 digits**
  (`U_quad_diff = 9.9e-192`) and re-derived it symbolically in sympy.
* **A genuinely independent high-precision route exists**: a raw `(b,c,d)`
  mpmath quadrature that uses only the *definition* of `L` (critical points of
  `f′`, no `(m,τ)` reduction, no `Λ`) gives `16 P_B = 0.0874292854494383849`,
  differing from the reduction route by `1.4e-15` absolute on a value `0.0874`,
  i.e. `1.6e-14` relative — **~14 significant digits confirmed across
  structurally different methods.** (Agent B2 quotes "15 digits", counting
  decimal places; on significant figures it is ~14. I use the conservative
  reading.) A third route
  (`quartic_quad.py`, a `(b,u,s)` reduction that had never been run to completion
  before) agrees to 15 digits.
* *Caveat, and it is the agent's own*: **~14 significant digits are defended**;
  the remaining ~27 of the 41 rest on the `(b,m,τ)` reduction plus the
  sympy-verified `U`, and are "internally converged" rather than doubly confirmed.
* The independent confirmations are Monte Carlo:
  * **5.6×10⁸ samples** (Agent B2) gives `0.00546386200566855 ± 8.3e-7`, i.e.
    **+0.57σ** against the deterministic value;
  * **2×10⁸ samples** (main thread) in raw `(b,c,d)` with `L` from the critical points —
    independent of the `(m,τ)` reduction, of the `Λ` closed form and of the
    quadrature — gives `0.0054657434 ± 0.0000013861`, i.e. **+1.02σ**;
  * root-space Vandermonde MC (shares no code or algebra with any critical-point
    route) gives `0.00546099 ± 0.00000396`, i.e. **+0.84σ**;
  * three further coefficient-space MCs give 0.005457 / 0.005462 / 0.00548, and
    the earlier campaign gave `0.0054749 ± 9.0e-6`.
* So the reduction and its domain are confirmed to about **six** significant
  digits, and a structural error is excluded. **Digits beyond the sixth remain
  provisional** pending a second independent *high-precision* route.
* A nested-`scipy.quad` computation from an earlier session gave `0.003138` and
  is **definitively wrong** (43 % low), excluded by four independent Monte Carlos.
  Recorded rather than quietly dropped.

### The `e`-window: exact bounds, not just sampled ones

The "never clips" claim is now exact rather than statistical (Agent B2):

    max e_hi = **25/64**, attained at (b,c,d) = (1, −1, −5/8)
    min e_lo = −(3y²−24y+1)/64 where 8y³+3y²+1 = 0  (y ≈ −0.66104)
             = −0.2840024343025303296803789391661167152427…

(I verified `max e_hi = 25/64` independently: at that point the critical points
are `x₂ = −1/4` exactly.) The reason is clean: there `δ = 0`, so
`f = (x²+x/2−5/8)² + ε` and both minima of `g` equal `−q²` with `q = c/2−b²/8`,
and `|q| ≤ 5/8` on the cube. Margins to the window walls are **0.609** and
**0.716** — the `e`-window is not merely unclipped, it is nowhere near clipping.
In a 5.6×10⁸-sample run, `n_samples_with_e_clipping = 0`.

**Honest caveat on the proof status** (the agent's own): `25/64` rests on a KKT /
envelope-theorem classification (`∇_{b,c,d} g(x_i) = (x_i³,x_i²,x_i)` vanishes only
at `x_i = 0`, so extrema cannot be interior, nor in the relative interior of a
face or edge) **plus** a global search — not on a one-line inequality. In
particular `−q²` is *not* a universal lower bound for `max(g(x₁),g(x₃))`; samples
violate it by up to `9.3e-4`. Both extrema were also found by a 320³ grid with
SLSQP refinement and are consistent with the MC extrema. So: true, well
corroborated, and a good candidate for symbolic proof — but not yet proved.

Contrast Theorem 1 of the previous campaign, where the band touched the cube
corner exactly. Here it does not come close, which is why the `e`-integration
contributes no correction term at all.

### The cone trick does *not* apply — confirmed and sharpened

`paper.tex` (per `TASK2.md`) suggested the divergence-theorem/cone trick that
solved the non-monic cubic applies here. It does not. The quartic discriminant is
homogeneous of degree 6 in **all five** coefficients, so `{Δ>0} ⊆ ℝ⁵` *is* a
cone — but the monic problem is the slice `a = 1`, and a slice of a cone is not a
cone. Running the (Lean-verified) cone identity on the *non-monic* quartic gives
`vol₅ = (1/5)Σ_{10 faces}`, confirming `TASK2.md`'s correction of the paper's
"2×4 = 8 faces" to **10**; and by central symmetry (degree 6 is even) plus
coefficient reversal, `vol₅ = (2/5)(2S_a + 2S_b + S_c)` with **`S_a = 16 P_B`**.
So that route *consumes* Problem B as an input and cannot produce it.

### Novelty

No prior art found. The digit search was re-run against the 16-digit value and is
now decisive: eight OEIS queries and a web search for every digit string returned
nothing, as did OEIS queries for the new constants `0.0880669596606269`
(unclipped), `0.00063767421118709` (`C_clip`) and `0.5794051802149734`
(`asinh(√6/4)`). arXiv metadata searches for `arcsinh`+`random polynomial` and
`sqrt{11}`+`real roots` return 0.

**Novelty is still not claimed**, for one reason only: Li (1988) explicitly
claims exact results for the quartic and remains unread (below). The correct
phrasing is *"not found in any searchable source; Li (1988) unverified"*.

(Note: `K = 128/105 = 2⁷/105` is a Wallis-type rational, not a fingerprint —
searching it as prior art would be meaningless, and was treated as such.)

---

## The single largest residual risk, for both problems

**Li (1988)**, *Comm. Statist. Theory Methods* 17(2):395–409
(DOI 10.1080/03610928808829630), explicitly claims exact results for the
**quartic**. It is paywalled, Unpaywall confirms `oa_status: closed` with no
repository copy, and it could not be read. Four things were established about it:

* what zbMATH carries as its "review" is **Li's own abstract**, recovered
  word-for-word via OpenAlex — so it is not independent testimony and does not
  enumerate the special cases. The independent MR review (G. Samal) is inaccessible.
* its **complete 9-item bibliography** (via Crossref) is classical
  theory-of-equations plus elementary statistics — Dickson, Uspensky, Kac 1949,
  Ibragimov 1971, Lapin, Stevens, Yu — with **zero** Gaussian-ensemble or
  measure-theoretic sources. *Weak inferential* support that his special cases are
  bounded/uniform-type; it says nothing about his quartic cases.
* the previous campaign established that its *cubic* family `x³+3ax²+3bx+2c` with
  symmetric uniform coefficients specialises to that campaign's Theorem 1.
* **its single citing work is identified**: Jiří Anděl, *Mathematics of Chance*
  (Wiley 2001), likely Ch. 11 pp. 195–210 — a popular chapter, exactly where the
  special cases would be restated in the open. The IA scan is lending-restricted.

**Its quartic cases remain unknown to us.** Obtaining Li (ILL), or Anděl Ch. 11,
is the single highest-value next action for the novelty question.

Explicitly **not searched** (so no negative is inferred): Google Books full text,
which indexes *Mathematical Reviews* and would likely settle it — it returned
HTTP 429 "Quota exceeded". Worth retrying after the quota resets.

Other things that could **not** be searched, so no negative is claimed from them:
DuckDuckGo (bot-blocked, control included), MathSciNet, Google Scholar,
Taylor & Francis full text, MR 89j full text, Bharucha-Reid–Sambandham (1986),
arXiv full text.

---

## Lean formalization

Not started, and correctly so: `TASK2.md` makes it a stretch goal for *after* a
closed form is proved, and neither problem has one. The nearest candidate is
Problem B's exact sub-results (items 1–6 above), which *are* proved and would
formalize in the style of the Mission-1 Lean development — in particular
`Λ = S(4−3S²)^{3/2}` and `K = 128/105` are exactly the kind of statement that
development already handles. Recorded here so it is easy to pick up.
