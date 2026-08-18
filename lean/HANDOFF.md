# HANDOFF

Written 2026-08-18 at the end of the session that (i) finished the Lean
formalization of the non-monic cubic and (ii) worked the two open problems in
`~/math/open-problems/`.

Full detail: `~/math/open-problems/VERDICT.md` (paper draft) and `PROGRESS.md`
(chronological log). This file is the short version.

---

## Phase 1 — non-monic cubic, Lean: COMPLETE

`P(a x³+b x²+c x+d has three distinct real roots) = 641/2430 − ln3/24`,
`(a,b,c,d)` i.i.d. `U[-1,1]`, machine-checked end to end.

* `lake build` clean; **zero `sorry`**; `#print axioms` on every headline theorem
  gives exactly `[propext, Classical.choice, Quot.sound]`.
* All three theorems also exist in **root-count form** with no discriminant in
  the statement (`theorem1_root_count`, `theorem2_root_count`,
  `theorem3_root_count`), so the English sentence is what is proved.
* Includes the classical `sign Δ ↔ three distinct real roots` bridge, which
  Mathlib did not have.

Nothing outstanding.

---

## Phase 2, Problem A — monic **Gaussian** cubic: **RESOLVED**

    p_A = (1/π) ∫₀^∞ exp( −x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1)) )
                     · 2(x⁴+6x²+3)/( √(x⁴+4x²+1)·(x⁴+4x²+9) ) dx
        = 0.1699293826234795026564431571317619021340572614546315…   (100 digits)

A single 1-D integral of elementary functions. Formula **contributed by an
external agent**; independently re-verified in this session — every algebraic
step symbolic residual **exactly 0**, and the integral agrees with this
campaign's unrelated quadrature to **79 significant digits** (that quadrature's
own precision ceiling). One step (eq. 8) was *strengthened* here from
numerical-at-points to exact.

### The two explicit non-claims — do not let either erase the other

1. **The "no elementary antiderivative" (Risch) claim is UNVERIFIED.** Neither the
   operator's session nor this one re-derived it. It is harder than it looks: the
   integrand is `e^g·f` with `g` rational but `f` **algebraic** (contains
   `√(x⁴+4x²+1)`), so the textbook Liouville criterion for `∫ f e^g` with `f,g`
   rational does **not** apply — it needs Risch over `ℚ(x, √(x⁴+4x²+1))`.
   sympy timing out is not evidence. **Unverified, not refuted.**
2. **The PSLQ negative still stands, separately.** `p_A` is *not* a
   small-coefficient combination of 55 standard constants — calibrated pipeline
   (recovered three known constants first, one of which exposed a too-small
   coefficient bound), 583 330 PSLQ subset calls, rationality to `maxcoeff 1e24`,
   algebraicity to degree 8. **Zero hits.**
   So the closed form is a **definite integral**, not a named-constant
   expression. These are independent claims about different questions.

**Novelty**: claim the Owen's-*T* cancellation and the closed form it yields.
Do **not** claim "Kac–Rice applied to the monic Gaussian cubic" — Edelman–Kostlan
explicitly invite that computation in BAMS 1995 — nor "Owen's T in a Rice-formula
context". Because E–K signpost it, an unindexed exercise doing it would be
invisible to every search channel tried.

### Formalized so far

`NonmonicCubic/GaussianCubic.lean` machine-checks the **algebraic skeleton** of
the derivation — every identity that verification had only CAS-checked, now
proved in Lean with zero `sorry`:

* `normSq_w`, `dot_w_dw` — `‖w‖² = q` and `w·w′ = q′/2`, i.e. what forces
  `u·u′ = 0` and hence **`Z ⟂ Z′`**;
* `key_v2`, `v_sq_eq` — `‖u′‖² = (x⁴+4x²+1)/q²`;
* `key_eq7` — equation (7), the exponent;
* `key_eq8` + `eq8_sides_pos` — equation (8) reduced to a polynomial identity by
  clearing **both** nested radicals (the step sympy could not close symbolically);
* `hasDerivAt_hA` — `h′ = x²(x⁴+2x²+3)/q^{3/2}`, the one genuine calculus step;
* `eq9_eq_Δ₃`, `eq9_consistent` — the external derivation's discriminant form is
  *literally* this project's `Δ₃`, tying it to `disc_completeSquare`.

`NonmonicCubic/KacRice.lean` machine-checks the algebra of the **inner Gaussian
integral** — the quadratic form `M`, `L`, `K`; `det M = q`; the residual exponent
`= h²`; `m = h′√q`; `s² = v²q`; and that the ratio `m/s = h′/v = z` is
normalisation-independent.

`NonmonicCubic/NormalCDF.lean` supplies `φ` and `Φ` — which **Mathlib does not
have in any form** — with `∫φ = 1`, `HasDerivAt Φ (φ x) x`, `Φ(x)+Φ(−x)=1`, and
the limits `Φ → 1` at `+∞`, `Φ → 0` at `−∞`.

`NonmonicCubic/Assembly.lean` **assembles the Kac–Rice integrand**
(`inner_iterated_kacRice`): the sheared iterated integral
`∫∫ φ(a)φ(β−2ax−3x²)|β|φ(x³+ax²+(β−2ax−3x²)x) da dβ` equals
`φ(h)·[2vφ(z) + h′(2Φ(z)−1)]` — the Kac–Rice formula for this problem, from the
definition of the Gaussian measure, with no Rice's formula anywhere. Checked
numerically to 20 digits at three values of `x`.

`NonmonicCubic/AffineChange.lean` does the **affine change of variables**:
`integral_exp_quadratic` (the Gaussian integral with a linear term — Mathlib has
only the centred one), `exponent_completeSquare` (the shear plus completion of
the square, whose residual is independent of `a`), `integral_a_exp` (the two
composed) and `integral_abs_gaussian_shift` (the `β`-side, reducing to
`FoldedNormal.integral_abs_scaled`). The composed chain reproduces the Kac–Rice
integrand `φ(h)[2vφ(z) + h′(2Φ(z)−1)]` to 25 digits at four values of `x`.

`NonmonicCubic/KacRiceIntegral.lean` does the **Tonelli swap**
(`lintegral_kacRice_swap`) and evaluates the fibre: at fixed `(a,b)`,
`∫⁻ x, kacRice a b x = φ(a)φ(b)·(1 + 2∫⁻_{Icc B A} φ)`, the bracket being
`E[N | a,b]`. Composing the two gives the Kac–Rice identity
`∫⁻ x ∫⁻ (a,b), kacRice = E[N]`.

`NonmonicCubic/FoldedNormal.lean` proves the **folded-normal mean**
`∫|m+σs|φ(s)ds = 2σφ(m/σ) + m(2Φ(m/σ)−1)` (`integral_abs_scaled`) — Mathlib has
no Gaussian moments beyond mean and variance. Note `2φ(t) = √(2/π)e^{−t²/2}`, so
this is the textbook form with `√(2/π)` never appearing.

`NonmonicCubic/DiscriminantNull.lean` proves `{Δ₃ = 0}` is Lebesgue-null in `ℝ³`
and hence `ae_dichotomy`: **almost every** monic cubic has exactly one real root
or three distinct real roots.

`NonmonicCubic/AreaFormula.lean` proves the **area formula for a real cubic in
full** (`lintegral_cub`): for every `(a,b)` there are levels `B ≤ A` with
`∫⁻ x, |cub′ x|·u(cub x) = ∫⁻ y, u y + 2∫⁻_{Icc B A} u`. With `u = φ` that is
`E[#roots | a,b] = 1 + 2·P(three roots | a,b)`.

So the algebra is machine-checked, step 1 of the analysis is machine-checked, and
the rest of the analysis is not — see the go/no-go table below.

### The root-count bridge is now complete (added 2026-08-18)

`NonmonicCubic/OneRealRoot.lean` supplies the **negative half** of the
sign↔root-count dictionary, which `DiscriminantRootCount.lean` was missing:

* `Δ₄_neg_iff_hasExactlyOneRealRoot` — for `a ≠ 0` and `Δ₄ ≠ 0`,
  `Δ₄ < 0 ↔ the cubic has exactly one real root` (`∃!`). The `Δ₄ ≠ 0`
  hypothesis is **necessary**, not laziness: `x³` has exactly one real root and
  `Δ₄ 1 0 0 0 = 0`. It is free in the intended application, where `{Δ = 0}` is null.
* `exactlyOne_or_threeDistinct` + `not_both_exactlyOne_and_three` — the
  dichotomy `N ∈ {1,3}` off `{Δ₄ = 0}`, which is exactly the content of
  `p = (E[N] − 1)/2`. Monic forms: `Δ₃_neg_iff_hasExactlyOneRealRoot`,
  `monic_exactlyOne_or_threeDistinct`.
* The engine is one identity, `Δ₄_eq_at_root`: at any root `r`,
  `Δ₄ = f′(r)² · ((b+ar)² − 4a(c+br+ar²))` — derivative squared times the
  discriminant of the complementary quadratic. A `linear_combination`, no case
  split. `f′(r)` vanishes iff `r` is repeated; the second factor is negative iff
  the other two roots are non-real. That is the whole theorem.
* The one analytic ingredient is "a real cubic has a real root"
  (`exists_real_root_cubic`): Mathlib has **no** odd-degree version (checked
  2026-08-18), so it is proved here by IVT between the explicit far-out points of
  `exists_le_cubic_neg`/`exists_ge_cubic_pos` (de-privatised for this purpose).

Zero `sorry`; `lake build` clean with **zero warnings**; `#print axioms` on all
seven headline theorems gives exactly `[propext, Classical.choice, Quot.sound]`.

What remains out of reach on the A side is unchanged and genuinely
probabilistic: Rice's formula itself. Do not re-investigate.

### The Kac–Rice step does NOT need Rice's formula (established 2026-08-18)

The earlier assessment — "the probabilistic content is out of reach" — was
**wrong**, and the reason is worth stating precisely so it is not rediscovered.

`Z(x) = (a,b,c)·u(x)` is not a general stochastic process. It is a linear
functional of **one fixed 3-dimensional Gaussian vector**, so "expected number of
crossings" is not a path property at all. Integrating `c` out *first* turns the
whole thing into deterministic calculus: for fixed `(a,b)` the real roots of
`f` are the solutions of `cub a b x = −c` with `cub a b x = x³+ax²+bx`, and

    E[N] = ∫_x [ ∫∫_{a,b} φ(a) φ(b) φ(x³+ax²+bx) · |3x²+2ax+b| da db ] dx

by the 1-D area formula plus Tonelli. **Verified symbolically**: the inner
integral equals `φ(h)·[v√(2/π)e^{−z²/2} + h′(2Φ(z)−1)]`, i.e. exactly the
classical Kac–Rice integrand — see `KacRice.lean`, whose header carries the
derivation.

### Go/no-go: GO on the route, NO on finishing it in one session

There is **no missing theory**. Every remaining step is a concrete lemma of known
shape. But the total is low-thousands of lines of Lean. Status of each step:

| step | status | note |
|---|---|---|
| 1. area formula for the cubic | **DONE** — `AreaFormula.lean` | this was the step that looked like it needed a coarea formula |
| 2. Tonelli swap | **DONE** — `KacRiceIntegral.lean` | nonnegative integrand ⇒ `lintegral_lintegral_swap` needs only `AEMeasurable`; fibre also evaluated |
| 3a. inner integral, algebra | **DONE** — `KacRice.lean` | `det M = q`, residual `= h²`, `m = h′√q`, `s² = v²q` |
| 3b. the normal CDF `Φ` | **DONE** — `NormalCDF.lean` | **Mathlib has no `Φ` and no `erf` at all.** Defined here with `deriv Φ = φ`, `Φ(x)+Φ(−x)=1`, `∫φ=1`, and the limits at `±∞` |
| 3c. folded-normal mean | **DONE** — `FoldedNormal.lean` | `∫|m+σs|φ(s)ds = 2σφ(m/σ) + m(2Φ(m/σ)−1)`; Mathlib has no Gaussian moments beyond mean/variance |
| 3d. affine change of variables in `ℝ²` | **DONE** — `AffineChange.lean` | no 2×2 Jacobian needed: `(a,b) ↦ (a,B)` is a shear, so it is a translation plus a 1-D Gaussian-with-linear-term integral |
| 4. Owen's-`T` theory | **DONE** — `OwenT.lean` | both partials: `∂T/∂a` (FTC) and `∂T/∂k = −φ(k)(2Φ(ak)−1)/2` (differentiation under the integral); `T(0,a)=arctan a/(2π)`; uniform bound and limits at `k → ±∞` |
| 7a. the jump at `x=0` | **DONE** — `OwenT.lean` | `T(0,·) → ±1/4` at `±∞` |
| 7b. chain-rule algebra | **DONE** — `OwenT.lean` | `owen_chain_rule_algebra` |
| 7c. chain rule for `x ↦ T(k x, a x)` | **DONE** — `OwenChain.lean` | joint differentiability turned out **not** to be needed; joint *continuity* suffices |
| 7d. `Ψ′` | **DONE** — `OwenChain.lean` | `hasDerivAt_owenPsi` |
| 7e. boundary values of `Ψ` | **DONE** — `OwenChain.lean` | `∓1/2` at `0^±`, `0` at `±∞`; the crude bound `|T(k,a)−T(0,a)| ≤ (k²/2)|a|/(2π)` suffices |
| 7f. **`∫_ℝ Ψ′ = 1`** | **DONE** — `OwenCancellation.lean` | the Owen's-`T` cancellation, abstract in `(h,z)` |
| 8. instantiate + final assembly | not done — **all that is left** | see below |
| 5a. final assembly algebra | **DONE** — `GaussianCubic.lean`, `KacRice.lean` | eq (7), eq (8) (now rational, see below) |
| 5b. inner integral assembled | **DONE** — `Assembly.lean` | `inner_iterated_kacRice`: the sheared iterated integral **is** `φ(h)[2vφ(z)+h′(2Φ(z)−1)]` |
| 5c. shear + Fubini to `∫⁻` over `ℝ²` | **DONE** — `Assembly.lean` | `inner_lintegral_eq`: the Kac–Rice identity in the original `(a,b)` variables |
| 6. `{Δ₃ = 0}` null in `ℝ³` | **DONE** — `DiscriminantNull.lean` | sections in `c` are finite (quadratic, leading coeff `−27`); gives `ae_dichotomy` |

**Step 1 was the one that looked fatal and is not.** Mathlib has no coarea
formula, no Banach indicatrix, no level-crossing theory (all confirmed absent by
exhaustive search, Mathlib v4.33.0). It does not need them: `JacobianOneDim.lean`
has `lintegral_image_eq_lintegral_deriv_mul_of_{monotoneOn,antitoneOn}` — change
of variables with **no injectivity hypothesis** on an arbitrary measurable set —
and `cub′` has at most two zeros, so `ℝ` has at most three monotone pieces and
the multiplicity function is a sum of three indicators *by construction*.

**Step 4, the Owen's-`T` cancellation, is not abstract theory either** — it is an
explicit antiderivative, and this was worked out here:

    Ψ(x) := −2 T( h(x), z(x)/h(x) ),   T Owen's T,
    Ψ′ = φ(h) h′ (2Φ(z) − 1) − (1/π) e^{−(h²+z²)/2} θ′,   θ = arctan(z/h)

(the 1-form is closed — cross-derivatives verified equal by hand). The `+1` in
`E[N] = 1 + 2p` is **the jump of `Ψ` at `x = 0`**: `h(0) = 0`, so `z/h → ±∞` and
`T(0,±∞) = ±1/4`, so `−2T` jumps by `∓1`; the limits at `x → ±∞` both vanish
since `T(k,a) → 0` as `|k| → ∞`.

**All of this was checked numerically, twice independently** (2026-08-18): the
identity for `Ψ′` holds to **32 digits**; `Ψ(0∓) = ±1/2` so the jump is exactly
`−1`; `Ψ(±60) ≈ 2e−784`; and the assembled constant
`J = ∫_ℝ φ(h)h′(2Φ(z)−1) dx − (1/π)∫_ℝ e^{−(h²+z²)/2} θ′ dx` comes out to
**`1` to 30 digits**. The whole route was also confirmed end to end: direct 2-D
quadrature of the inner integral matches `φ(h)[v√(2/π)e^{−z²/2} + h′(2Φ(z)−1)]`
to ~25 digits at nine values of `x` (and `I(0) = 1/π` exactly), the resulting
`p` reproduces **all 52 known digits**, a fully-direct route using no closed form
anywhere agrees to `7.6e-16`, and Monte Carlo at `4×10⁷` sits at `0.70 σ`.

*Quadrature warning for anyone re-running this:* naive nested quadrature of the
inner integral in the raw `(a,b)` variables **silently fails** for `|x| ≳ 3`
(30 % low at `x = 3`; off by 36 orders of magnitude at `x = 5`). The mass sits on
a ridge of width `~1/x²` around `a ≈ −x` that tanh–sinh over `ℝ²` misses. Fix:
substitute `a → u = x³+ax²+bx` (Jacobian `1/x²`) with a breakpoint at the `|·|`
kink `u₀ = x(b−x²)/2`, and use `(a,b)` only for `|x| ≤ 1.5`.

**`θ′` has a closed form, and it makes equation (8) rational.** Independently
confirmed to 30 digits and symbolically:

    θ′ = (x⁸ + 6x⁶ − 6x⁴ − 22x² − 3) / ( q · √(x⁴+4x²+1) · (x⁴+4x²+9) )

(the degree-12 denominator the raw quotient produces factors as
`q·(x⁴+4x²+1)·(x⁴+4x²+9)`). Two consequences, both now in `KacRice.lean`:

* **No singularity at the origin** in this form — `θ′(0) = −3/9 = −1/3` directly.
* **Equation (8) is not a nested-radical identity.** Over the common denominator
  it reduces to the single polynomial identity
  `(x⁴+4x²+1)(x⁴+4x²+9) + (x⁸+6x⁶−6x⁴−22x²−3) = 2(x⁴+6x²+3)·q`, a one-line
  `ring` (`eq8_numerator`). This supersedes `GaussianCubic.key_eq8`, which
  cleared *both* nested radicals — the step the original verification could only
  check numerically. Given the closed form, nothing needs clearing.

**Formalization gotcha, recorded so it is not hit cold:** `θ′` is written
`(h z′ − z h′)/(h² + z²)`, and `h² + z² → 0` as `x → 0` — it is a genuine `0/0`.
It is removable: near `0`, `h ≈ x³` and `z ≈ 3x²`, so `θ′ → −1/3` (confirmed
numerically from both sides).  So `θ′` extends continuously through `x = 0` but
the quotient form does **not** work there, and `eq (8)`'s `v + θ′` must be given
its extended value at the origin. To formalize: define `T` by its integral and
prove `∂T/∂k = −φ(k)(2Φ(ak)−1)/2`, `∂T/∂a = (1/2π)e^{−k²(1+a²)/2}/(1+a²)`
(differentiation under the integral sign — Mathlib has
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), plus the two limits and
`T(0,a) = arctan(a)/(2π)`. Estimate 400–800 lines; the hardest analysis in the
project. Owen's `T` is absent from Mathlib, as are bivariate-normal orthant
probabilities.

### Next step for A

## **Problem A is CLOSED.**

`FinalAssembly.rootProb_eq`:

    rootProb = ENNReal.ofReal (∫ x in Ioi 0, targetIntegrand x)

where `rootProb` is the Gaussian measure of the three-distinct-real-roots region
for `x³+ax²+bx+c`, `(a,b,c)` i.i.d. `N(0,1)`, and

    targetIntegrand x
      = (1/π)·e^{−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1))}·2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9))

— exactly the boxed formula. Zero `sorry`, zero warnings, axioms exactly
`[propext, Classical.choice, Quot.sound]`. The formalized integrand integrates
numerically to `0.169929382623479502656443157132`, matching the campaign's
independently established value to all 30 digits computed.

**How `rootProb` is phrased — read before quoting the result.** It is defined
directly as the iterated `lintegral` of the Gaussian density over the
three-real-roots region:

    rootProb = ∫⁻ (a,b), ofReal (φ a · φ b) · ∫⁻ y in {y | three distinct real
                 roots of x³+ax²+bx+(−y)}, ofReal (φ y)

That *is* the probability, written measure-theoretically, and it is what the
whole chain computes. But it does **not** go through Mathlib's
`ProbabilityTheory` API — no `gaussianReal`, no `Measure.pi`, no `IsProbabilityMeasure`.
If the statement is ever wanted in the form `μ {p | HasThreeDistinctRealRoots …}`
for a named Gaussian measure `μ` on `ℝ³`, that is a further translation step and
is **not done**. Mathlib has the pieces for it (`gaussianReal`,
`Measure.volume_eq_prod`, `map_pi_eq_stdGaussian`), so it is bookkeeping, not
mathematics — but it is not to be claimed as already proved.

**None of Rice's formula, the coarea formula, a theory of stochastic processes,
or a C¹ criterion was needed** — Mathlib has none of them. The derivation runs on:
the 1-D area formula for a cubic (three monotone pieces, `AreaFormula`), Tonelli
in `ℝ≥0∞`, a shear plus a Gaussian integral with a linear term (`AffineChange`),
the folded-normal mean (`FoldedNormal`), and Owen's `T` built from scratch
(`OwenT`, `OwenChain`, `OwenCancellation`).

### Five expectations that turned out wrong, recorded so they are not re-feared

1. **Joint differentiability of `T` is not needed.** The chain rule for the
   one-variable composite `x ↦ T(k x, a x)` follows from the two partials plus
   joint *continuity* of the integrand, so Mathlib's missing C¹ criterion is
   irrelevant (`OwenChain.hasDerivAt_owenT_comp`).
2. **The limit `T(h,z/h) → 1/4` at `0⁺` needs no uniform-in-`a` estimate.** The
   crude `|T(k,a) − T(0,a)| ≤ (1/2π)(k²/2)|a|` suffices, because `k²a = hz → 0`.
3. **`θ′` is not a nested-radical mess.** It equals `N₂/(q√w(x⁴+4x²+9))` off two
   *polynomial* identities, and is regular at the origin (`θ′(0) = −1/3`). This
   also makes equation (8) rational and supersedes `GaussianCubic.key_eq8`.
4. **Integrability is easy once (3) is known** — `Ψ′` agrees a.e. with a
   continuous function dominated by `10 e^{−x²/6}`.
5. **The band-to-roots link needs no Rolle's theorem** — `f(x₁)f(x₂) = −Δ₃/27`
   and `f(x₁) − f(x₂) = (x₂−x₁)³/2`, both `ring` (`BandRoots`).

### Lean gotchas worth keeping

* `HasDerivAt.neg` yields `Pi.neg`, breaking `convert` on an `AddCommGroup`
  diamond; and `convert h using 1` on `HasDerivAt` descends into a `Module`
  instance equality. Rewrite the derivative with an explicit `have` + `exact`.
* Keep `√` **linear** through every cross-multiplication (state `(√G)′` with `√G`
  in the numerator), and `set` the `√` terms opaque before touching `field_simp`;
  `field_simp` also normalises polynomials *inside* `Real.sqrt` arguments, which
  silently breaks atom matching.
* `rw [show (1:ℝ) = Real.exp 0 ...]` rewrites the `1` inside `1 + t²` too.

### Still open for Problem A (not part of the formula)

Settle the Risch question over `ℚ(x, √(x⁴+4x²+1))`, or drop the
"no elementary antiderivative" claim. Unrelated to the formalization.

The elementary theory, for reference:The elementary theory, for reference:The elementary theory, for reference:
`OwenT.lean` has the definition, `T(k,0)=0`, `T(0,a) = arctan a/(2π)` (this is
what makes `T(0,±∞) = ±1/4` and hence the jump), evenness in `k`, `∂T/∂a` by plain
FTC, the uniform bound `|T(k,a)| ≤ e^{−k²/2}/4` (integrand `≤ e^{−k²/2}/(1+t²)`,
`∫₀^∞ dt/(1+t²) = π/2`), and the limits `T(k, a(k)) → 0` as `k → ±∞` for an
*arbitrary* moving second argument — which is the form the application needs,
since `z/h → 0` as `x → ±∞`.

**What is left is one lemma: `∂T/∂k = −φ(k)(2Φ(ak) − 1)/2`**, i.e.
differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). After that, `Ψ = −2T(h, z/h)`
and the chain rule give `Ψ′`, and the jump analysis at `x = 0` closes Problem A.
Note `owenT_neg_right` (oddness in `a`) is *not* proved — `intervalIntegral.integral_comp_neg`
hits an instance diamond there — and is not needed; the bound handles both signs
of `a` directly.

Everything else is proved, and
`Assembly.inner_lintegral_eq` now states the Kac–Rice identity directly in the
original `(a,b)` variables:

    ∫⁻ a ∫⁻ b  φ(a)φ(b)·|3x²+2ax+b|·φ(x³+ax²+bx)
      = φ(h)·[2vφ(z) + h′(2Φ(z) − 1)].

So the chain `E[N] = ∫ φ(h)[2vφ(z) + h′(2Φ(z)−1)] dx` is complete except for
combining it with `AreaFormula` and `KacRiceIntegral` (a rewrite), and the
remaining mathematical content of Problem A is exactly the Owen's-`T` step.

The nearest piece of (5) is *stitching*, not new mathematics: all four factors of
`I(x) = φ(h)[2vφ(z) + h′(2Φ(z)−1)]` now exist as separate theorems
(`integral_a_exp`, `integral_abs_gaussian_shift`, and the `KacRice.lean`
identities `mB_eq`/`varB_eq`/`resid_eq_hA_sq`/`mB_eq_hA'_mul_sqrt`/
`varB_eq_v_sq_mul`), and the composed chain was checked numerically to 25 digits.
What is needed is a Tonelli step to write the `(a,b)` integral as
`∫_β |β| ∫_a …` — the same `lintegral`-in-`ℝ≥0∞` pattern as
`KacRiceIntegral.lean` — and then the arithmetic
`(2π)^{-3/2}√(2π/W)·s√(2π) = φ(h)/√q · …`.

**(4) Owen's `T` is the only genuinely hard item left.**
`Tendsto Φ atTop (𝓝 1)` / `atBot (𝓝 0)` are also still missing and will be
wanted eventually (they need `Φ x = ∫_{Iic x} φ`, deliberately not proved yet). Also still open and independent of all
this: the Risch question over `ℚ(x, √(x⁴+4x²+1))` (or drop the claim).

---

## Phase 2, Problem B — monic **uniform** quartic: 99.28 % solved

    16 p_B = U − C_clip
    U      = √3·asinh(√6/4)/90 + 7013√11/302400      (exact, four independent legs)
    C_clip = 0.000637674211187091936250935532440…    (0.724 % of the total)
    p_B    = 0.0054643303405899855451944032832877411463…  (~41 digits, ~14 defended)

Proved exactly along the way: the normal form
`x⁴+bx³+cx²+dx+e = (x²+px+q)² + δx + ε` (Jacobian 1/4); the band factorisation
`L = m²Λ(τ)`; the band closed form **`Λ = S(4−3S²)^{3/2}`** (the analogue of the
cubic's `(4/27)s³`); and **`∫Λ dτ = 128/105`**. The `e`-window never clips
(`max e_hi = 25/64`, margins 0.61/0.72 — established, not yet proved). The
clipping onset is the real root of `27b³ − 9b² + 108b + 76`.

**The remaining gap is `C_clip` alone** — the same integral over `|d| > 1`.
No closed form: 190-digit PSLQ found no algebraic relation of degree ≤ 10 with
coefficients ≤ 1e14, and none against a purpose-built basis in the field the
derivation generates. Structural reason for pessimism: the clipped region's
boundary is an algebraic surface integrated against 3/2- and 5/2-power weights, so
the `b`-integral runs over a **high-genus curve**.

### `C_clip` reduced to 1-D, and partly proved non-elementary (2026-08-18)

An **external agent** submitted a reduction; it was verified here from scratch
(record: `~/math/open-problems/problem_B_verification_2026-08-18.md`, summary in
`VERDICT.md` §3.7). Substantially correct. Three transcription errors found and
corrected: the `A₁` `artanh` coefficient is `35√3/12288` (not `/4096`); the
Möbius map is `t_S(z) = B(z−α)/(A(z−β))` (the submission had it inverted, which
makes the answer complex); and the claimed minimum `54 − (11/108)√22` should be
`54 − (108/11)√22 ≈ 7.949`. With the first two fixed, the 1-D formula reproduces
`C_clip` to **all 75 quoted digits**.

**The submission's "factor of 2" does NOT affect anything in this campaign.** It
is arithmetically right — the correct integrand is `2 m^{7/2}Λ`, the 2 being the
Jacobian `|∂(b,c,d)/∂(b,m,τ)| = 2m^{3/2}` — but Prop B5 already carries it inside
`4K/9`, and the omission was in an ad-hoc `c_clip_problem_statement.md` written
for the external agent that **is not in the repo** and is referenced nowhere in
the campaign record. `U`, `C_clip`, `16p_B = U − C_clip` all unchanged and
self-consistent to 53 decimals; independently reconfirmed by a from-scratch raw
`(b,c,d)` Monte Carlo (N = 3×10⁸, `z = +0.97`).

Also **corrected**: the `b`-integral does *not* run over a high-genus curve. The
relevant curve is `y³ = t(1−t)`, **genus 1**, `j = 0` — confirmed three ways.

Note for writing up: the non-elementarity of `∫t^{−1/3}(1−t)^{−1/3}dt` follows
from **Chebyshev's 1853 criterion** on binomial differentials in one line. Do not
present the genus/Rosenlicht machinery as the proof of *that*; the genuinely new
step is the Hermite reduction of the **trinomial**
`(1−ρt)⁸t^{−10/3}(1−t)^{−10/3}`, with `γ(ρ)` shown (by Sturm) to have no real
root at all.

### Next step for B

The residual is now the **outer** `S`-integral: an incomplete elliptic period
against `W(S)` over algebraic endpoints, the right one on the plane cubic
`S³−S = 17z³−z`. Prove *that* non-elementary (Rosenlicht one level up, or
Picard–Fuchs), or find its closed form. Secondary:
write out the `e`-window proof (KKT/envelope outline is complete; note the
tempting shortcut `−q²` is **false**, violated by 9.3e-4).

---

## Cross-cutting

* **Do not use the cone/divergence trick on the monic quartic.** `{Δ>0} ⊆ ℝ⁵` is
  a cone but the monic problem is the slice `a=1`, and a slice of a cone is not a
  cone. Applied correctly to the non-monic quartic it needs **10** faces (not 8)
  and *consumes* `p_B` as an input.
* **`2^{−n(n−1)/4}` is Edelman 1997 for real Ginibre matrices**, not
  Edelman–Kostlan and not the Kostlan polynomial ensemble.
* **Single highest-value non-computational action, both problems**: obtain
  **Li (1988)**, *Comm. Statist. Theory Methods* 17(2):395–409, which claims exact
  **quartic** results and is unread. Its only citing work is Anděl,
  *Mathematics of Chance* (Wiley 2001), likely Ch. 11. Until then, phrase both
  results as *"not found in any searchable source; Li (1988) unverified"* — not
  "novel".

## Repository layout

* This repo — the Lean development (Phase 1) plus this file.
* `~/math/open-problems/` — Phase 2. Committed as its own git repo this session.
* `~/math/real-rooted-random-polynomials/` — sibling reference project, **not**
  under version control; only `README.md` and `LITERATURE.md` were edited, as
  `TASK2.md` permits.
