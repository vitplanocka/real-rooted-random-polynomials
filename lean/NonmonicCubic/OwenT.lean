/-
# Owen's T function

Step 4, the last mathematical content of Problem A.  Mathlib has no Owen's `T`
and no bivariate-normal orthant probabilities (checked 2026-08-18), so it is
built here.

    T(k, a) = (1/2π) ∫₀^a exp(−k²(1+t²)/2) / (1+t²) dt

**Why it is needed.**  The Kac–Rice integrand proved in `Assembly.lean` is
`φ(h)·[2vφ(z) + h′(2Φ(z)−1)]`, and the `Φ` term is what stands between that and
the one-dimensional closed form.  It is removed by an *explicit antiderivative*:
with `θ = arctan(z/h)`,

    Ψ(x) := −2 T(h(x), z(x)/h(x))
    Ψ′(x) = φ(h) h′ (2Φ(z) − 1) − (1/π) e^{−(h²+z²)/2} θ′

(verified numerically to 32 digits, see `HANDOFF.md`).  So integrating the `Φ`
term over `ℝ` reduces to the boundary values of `Ψ`, and those are: `0` at
`x = ±∞` (because `T(k,a) → 0` as `|k| → ∞`) and a **jump of `−1` at `x = 0`**,
where `h(0) = 0` sends `z/h → ±∞` and `T(0,±∞) = ±1/4`.  That jump is exactly
the `1` in `E[N] = 1 + 2p`.

This file establishes the elementary theory: the two symmetries, `T(0,a)`, the
`a`-derivative (plain FTC), and the uniform bound `|T(k,a)| ≤ e^{−k²/2}/4` which
gives the limits at `k → ±∞`.  The `k`-derivative
`∂T/∂k = −φ(k)(2Φ(ak) − 1)/2` — differentiation under the integral sign — is the
remaining piece.
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import NonmonicCubic.NormalCDF

namespace NonmonicCubic.Gaussian

open MeasureTheory Real intervalIntegral

/-- **Owen's T function.** -/
noncomputable def owenT (k a : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ t in (0 : ℝ)..a, Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)

theorem one_add_sq_pos (t : ℝ) : (0 : ℝ) < 1 + t ^ 2 := by positivity

theorem continuous_owenIntegrand (k : ℝ) :
    Continuous fun t : ℝ => Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
  Continuous.div (by fun_prop) (by fun_prop) fun t => (one_add_sq_pos t).ne'

theorem owenIntegrand_pos (k t : ℝ) :
    0 < Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
  div_pos (Real.exp_pos _) (one_add_sq_pos t)

/-! ## Elementary values and symmetries -/

@[simp] theorem owenT_zero_right (k : ℝ) : owenT k 0 = 0 := by simp [owenT]

/-- `T(0, a) = arctan a / (2π)`.  In particular `T(0, ±∞) = ±1/4`, which is the
source of the jump that produces the `1` in `E[N] = 1 + 2p`. -/
theorem owenT_zero_left (a : ℝ) : owenT 0 a = Real.arctan a / (2 * π) := by
  unfold owenT
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_mul,
    zero_div, Real.exp_zero]
  rw [integral_one_div_one_add_sq]
  simp [Real.arctan_zero]
  ring

/-- `T` is even in its first argument. -/
theorem owenT_neg_left (k a : ℝ) : owenT (-k) a = owenT k a := by
  unfold owenT; rw [neg_sq]

/-! ## The `a`-derivative: plain FTC -/

/-- `∂T/∂a = (1/2π)·e^{−k²(1+a²)/2}/(1+a²)`. -/
theorem hasDerivAt_owenT_right (k a : ℝ) :
    HasDerivAt (owenT k)
      (1 / (2 * π) * (Real.exp (-k ^ 2 * (1 + a ^ 2) / 2) / (1 + a ^ 2))) a := by
  unfold owenT
  exact (((continuous_owenIntegrand k).integral_hasStrictDerivAt 0 a).hasDerivAt).const_mul _

/-! ## The uniform bound, and the limits at `k → ±∞` -/

/-- `|T(k,a)| ≤ e^{−k²/2}/4`, uniformly in `a`.  The integrand is at most
`e^{−k²/2}/(1+t²)` and `∫₀^∞ dt/(1+t²) = π/2`. -/
theorem abs_owenT_le (k a : ℝ) : |owenT k a| ≤ Real.exp (-k ^ 2 / 2) / 4 := by
  have hexp : (0 : ℝ) < Real.exp (-k ^ 2 / 2) := Real.exp_pos _
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have core : ∀ u v : ℝ, u ≤ v →
      (∫ t in u..v, Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
        ≤ Real.exp (-k ^ 2 / 2) * (Real.arctan v - Real.arctan u) := by
    intro u v huv
    have hint := (continuous_owenIntegrand k).intervalIntegrable (μ := volume) u v
    have hbd : IntervalIntegrable
        (fun t : ℝ => Real.exp (-k ^ 2 / 2) * (1 / (1 + t ^ 2))) volume u v := by
      apply Continuous.intervalIntegrable
      exact Continuous.mul continuous_const
        (Continuous.div continuous_const (by fun_prop) fun t => (one_add_sq_pos t).ne')
    have hle : ∀ t ∈ Set.Icc u v,
        Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2)
          ≤ Real.exp (-k ^ 2 / 2) * (1 / (1 + t ^ 2)) := by
      intro t _
      rw [mul_one_div, div_le_div_iff_of_pos_right (one_add_sq_pos t)]
      have hkt : 0 ≤ k ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg k) (sq_nonneg t)
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg k, sq_nonneg t, hkt]
    have h := intervalIntegral.integral_mono_on huv hint hbd hle
    rwa [intervalIntegral.integral_const_mul, integral_one_div_one_add_sq] at h
  have corenn : ∀ u v : ℝ, u ≤ v →
      0 ≤ ∫ t in u..v, Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
    fun u v huv => intervalIntegral.integral_nonneg huv fun t _ => (owenIntegrand_pos k t).le
  have hkey : ∀ A : ℝ, A ≤ π / 2 →
      1 / (2 * π) * (Real.exp (-k ^ 2 / 2) * A) ≤ Real.exp (-k ^ 2 / 2) / 4 := by
    intro A hA
    have h1 : Real.exp (-k ^ 2 / 2) * A ≤ Real.exp (-k ^ 2 / 2) * (π / 2) :=
      mul_le_mul_of_nonneg_left hA hexp.le
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    have heq : 1 / (2 * π) * (Real.exp (-k ^ 2 / 2) * (π / 2)) = Real.exp (-k ^ 2 / 2) / 4 := by
      have hp : π ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    linarith
  rcases le_or_gt 0 a with ha | ha
  · rw [owenT, abs_of_nonneg (mul_nonneg (by positivity) (corenn 0 a ha))]
    have h1 := core 0 a ha
    rw [Real.arctan_zero, sub_zero] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    have h3 := hkey (Real.arctan a) (Real.arctan_lt_pi_div_two a).le
    linarith
  · have hsym : (∫ t in (0 : ℝ)..a, Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
        = -∫ t in a..(0 : ℝ), Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) :=
      intervalIntegral.integral_symm a 0
    rw [owenT, hsym, mul_neg, abs_neg,
      abs_of_nonneg (mul_nonneg (by positivity) (corenn a 0 ha.le))]
    have h1 := core a 0 ha.le
    rw [Real.arctan_zero, zero_sub] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    have h3 := hkey (-Real.arctan a) (by linarith [Real.neg_pi_div_two_lt_arctan a])
    linarith

/-- `e^{−k²/2} → 0` at `+∞`. -/
theorem tendsto_exp_neg_sq_half : Filter.Tendsto (fun k : ℝ => Real.exp (-k ^ 2 / 2))
    Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun k : ℝ => -k ^ 2 / 2) Filter.atTop Filter.atBot := by
    have h : Filter.Tendsto (fun k : ℝ => k ^ 2 / 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    simpa [neg_div] using h
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1

/-- **`T(k, a) → 0` as `k → +∞`, uniformly in `a`.**  Stated for an arbitrary
`a = f k` because in the application the second argument moves with `k`. -/
theorem tendsto_owenT_atTop (f : ℝ → ℝ) :
    Filter.Tendsto (fun k : ℝ => owenT k (f k)) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun k : ℝ => Real.exp (-k ^ 2 / 2) / 4) Filter.atTop (nhds 0) := by
    simpa using tendsto_exp_neg_sq_half.div_const 4
  refine squeeze_zero_norm (fun k => ?_) hb
  simpa [Real.norm_eq_abs] using abs_owenT_le k (f k)

/-- **`T(k, a) → 0` as `k → −∞`**, by evenness in `k`. -/
theorem tendsto_owenT_atBot (f : ℝ → ℝ) :
    Filter.Tendsto (fun k : ℝ => owenT k (f k)) Filter.atBot (nhds 0) := by
  have hb : Filter.Tendsto (fun k : ℝ => Real.exp (-k ^ 2 / 2) / 4) Filter.atBot (nhds 0) := by
    have h := tendsto_exp_neg_sq_half.comp Filter.tendsto_neg_atBot_atTop
    have e : ∀ k : ℝ, Real.exp (-(-k) ^ 2 / 2) = Real.exp (-k ^ 2 / 2) := by
      intro k; rw [neg_sq]
    simpa [Function.comp_def, e] using h.div_const 4
  refine squeeze_zero_norm (fun k => ?_) hb
  simpa [Real.norm_eq_abs] using abs_owenT_le k (f k)


/-! ## The `k`-derivative: differentiation under the integral sign

`∂/∂k` of the integrand is `−k·e^{−k²(1+t²)/2}`, which is bounded by `|k|+1`
uniformly for `k` in a unit ball and for all `t` (the exponential is `≤ 1`).  On a
compact interval a constant bound is integrable, so Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies
directly — no manual splitting into `Ioc` pieces. -/

/-- `∂/∂k [ e^{−k²(1+t²)/2}/(1+t²) ] = −k e^{−k²(1+t²)/2}`. -/
theorem hasDerivAt_owenIntegrand_left (t k : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
      (-(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2))) k := by
  have h1 : (1 : ℝ) + t ^ 2 ≠ 0 := (one_add_sq_pos t).ne'
  -- normalise the exponent so that no `Pi.neg` appears (which would break `convert`)
  have hsq : ∀ x : ℝ, -x ^ 2 * (1 + t ^ 2) / 2 = -(1 + t ^ 2) / 2 * x ^ 2 := fun x => by ring
  simp only [hsq]
  have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * k) k := by simpa using hasDerivAt_pow 2 k
  have h := ((h0.const_mul (-(1 + t ^ 2) / 2)).exp).div_const (1 + t ^ 2)
  have hd : -(k * Real.exp (-(1 + t ^ 2) / 2 * k ^ 2))
      = Real.exp (-(1 + t ^ 2) / 2 * k ^ 2) * (-(1 + t ^ 2) / 2 * (2 * k)) / (1 + t ^ 2) := by
    field_simp
  rw [hd]
  exact h

/-- The uniform bound on `∂/∂k` of the integrand: `‖−x e^{−x²(1+t²)/2}‖ ≤ |k|+1`
for `x` within distance `1` of `k`, for every `t`. -/
theorem owen_deriv_bound (k : ℝ) {x : ℝ} (hx : x ∈ Metric.ball k 1) (t : ℝ) :
    ‖-(x * Real.exp (-x ^ 2 * (1 + t ^ 2) / 2))‖ ≤ |k| + 1 := by
  have hx' : |x - k| < 1 := by simpa [Real.dist_eq] using hx
  have hxle : |x| ≤ |k| + 1 := by
    have := abs_sub_abs_le_abs_sub x k
    linarith
  have hexp : Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) ≤ 1 := by
    have hnp : -x ^ 2 * (1 + t ^ 2) / 2 ≤ 0 := by
      nlinarith [sq_nonneg x, sq_nonneg t, mul_nonneg (sq_nonneg x) (sq_nonneg t)]
    calc Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) ≤ Real.exp 0 := Real.exp_le_exp.2 hnp
      _ = 1 := Real.exp_zero
  rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |x| * Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg x)
    _ = |x| := mul_one _
    _ ≤ |k| + 1 := hxle

/-- **Differentiation under the integral sign** for Owen's `T`. -/
theorem hasDerivAt_owenT_integral (a k : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..a, Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
      (∫ t in (0 : ℝ)..a, -(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2))) k := by
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => Real.exp (-x ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2))
    (F' := fun x t : ℝ => -(x * Real.exp (-x ^ 2 * (1 + t ^ 2) / 2)))
    (bound := fun _ : ℝ => |k| + 1)
    (Metric.ball_mem_nhds k one_pos)
    (Filter.Eventually.of_forall fun x => (continuous_owenIntegrand x).aestronglyMeasurable)
    ((continuous_owenIntegrand k).intervalIntegrable (μ := volume) 0 a)
    ((by fun_prop : Continuous fun t : ℝ =>
      -(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t _ x hx => owen_deriv_bound k hx t)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_owenIntegrand_left t x)).2

/-- `∂T/∂k` as an integral, before evaluation. -/
theorem hasDerivAt_owenT_left_integral (a k : ℝ) :
    HasDerivAt (fun x : ℝ => owenT x a)
      (1 / (2 * π) * ∫ t in (0 : ℝ)..a, -(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2))) k :=
  (hasDerivAt_owenT_integral a k).const_mul _


/-! ## Evaluating the `k`-derivative -/

/-- `∫₀^x e^{−u²/2} du = √(2π)(Φ(x) − 1/2)`, i.e. `Φ` up to normalisation. -/
theorem integral_exp_neg_sq_half (x : ℝ) :
    ∫ u in (0 : ℝ)..x, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * π) * (Φ x - 1 / 2) := by
  have hP : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h : ∀ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * π) * φ u := by
    intro u; unfold φ; field_simp
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul]
  unfold Φ
  ring

/-- The `k`-derivative integral, evaluated: the substitution `u = k t` turns it
into `∫₀^{ka} e^{−u²/2} du`, i.e. into `Φ`. -/
theorem integral_owen_deriv (a k : ℝ) :
    (∫ t in (0 : ℝ)..a, -(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2)))
      = -π * φ k * (2 * Φ (a * k) - 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [Φ_zero]
  · have hfac : ∀ t : ℝ, -(k * Real.exp (-k ^ 2 * (1 + t ^ 2) / 2))
        = -(k * Real.exp (-k ^ 2 / 2)) * Real.exp (-(k * t) ^ 2 / 2) := by
      intro t
      have hh : Real.exp (-k ^ 2 * (1 + t ^ 2) / 2)
          = Real.exp (-k ^ 2 / 2) * Real.exp (-(k * t) ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hh]; ring
    simp_rw [hfac]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => Real.exp (-u ^ 2 / 2)) hk,
      mul_zero, integral_exp_neg_sq_half, smul_eq_mul, mul_comm a k]
    have hP : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    unfold φ
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- **`∂T/∂k = −φ(k)(2Φ(ak) − 1)/2`.**

This is the last piece of Owen's-`T` theory.  Together with
`hasDerivAt_owenT_right` it gives both partials, so the chain rule applies to
`Ψ(x) = −2 T(h(x), z(x)/h(x))`, and the `Φ` term of the Kac–Rice integrand
becomes a boundary term. -/
theorem hasDerivAt_owenT_left (a k : ℝ) :
    HasDerivAt (fun x : ℝ => owenT x a) (-(φ k * (2 * Φ (a * k) - 1)) / 2) k := by
  have h := hasDerivAt_owenT_left_integral a k
  rw [integral_owen_deriv] at h
  have heq : 1 / (2 * π) * (-π * φ k * (2 * Φ (a * k) - 1))
      = -(φ k * (2 * Φ (a * k) - 1)) / 2 := by
    have hp : π ≠ 0 := Real.pi_ne_zero
    field_simp
  rwa [heq] at h


/-! ## The jump at `x = 0`

`T(0,a) = arctan a/(2π)`, so `T(0, ±∞) = ±1/4`.  In the application `h(0) = 0`
while `z/h → ±∞` as `x → 0^±`, so `Ψ = −2T(h, z/h)` jumps by `−1` across the
origin — and that jump is the `1` in `E[N] = 1 + 2p`. -/

theorem tendsto_owenT_zero_atTop :
    Filter.Tendsto (owenT 0) Filter.atTop (nhds (1 / 4)) := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  have h : Filter.Tendsto Real.arctan Filter.atTop (nhds (π / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have h2 := h.div_const (2 * π)
  have heq : π / 2 / (2 * π) = 1 / 4 := by field_simp; ring
  rw [heq] at h2
  have hfun : owenT 0 = fun a => Real.arctan a / (2 * π) := funext owenT_zero_left
  rw [hfun]
  exact h2

theorem tendsto_owenT_zero_atBot :
    Filter.Tendsto (owenT 0) Filter.atBot (nhds (-(1 / 4))) := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  have h : Filter.Tendsto Real.arctan Filter.atBot (nhds (-(π / 2))) :=
    Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
  have h2 := h.div_const (2 * π)
  have heq : -(π / 2) / (2 * π) = -(1 / 4) := by field_simp; ring
  rw [heq] at h2
  have hfun : owenT 0 = fun a => Real.arctan a / (2 * π) := funext owenT_zero_left
  rw [hfun]
  exact h2

/-- **The jump of `Ψ = −2T(0, ·)` across `±∞` is `−1`.**  `−2·(1/4) − (−2·(−1/4)) = −1`. -/
theorem owenT_zero_jump : -2 * (1 / 4 : ℝ) - -2 * -(1 / 4 : ℝ) = -1 := by norm_num

/-! ## The chain rule, algebraically

The two partials are proved (`hasDerivAt_owenT_left`, `hasDerivAt_owenT_right`).
What the chain rule for `Ψ(x) = −2 T(h(x), z(x)/h(x))` would produce, *once the
joint differentiability of `T` is available*, is the contraction of those two
partials against `h′` and `(z/h)′`.  `owen_chain_rule_algebra` verifies that this
contraction is **exactly** the Owen's-`T` cancellation — so the only thing
separating `Ψ′` from the target is the analytic fact that `T` is differentiable
as a function of two variables, not the algebra.

See `HANDOFF.md`: Mathlib has no C¹ criterion (continuous partials ⇒
differentiable), so that fact needs its own construction. -/

/-- **The chain-rule terms assemble to the Owen's-`T` cancellation.**

With `∂T/∂k = −φ(k)(2Φ(ak)−1)/2` at `(k,a) = (h, z/h)` contracted against `h′`,
and `∂T/∂a = (1/2π)e^{−k²(1+a²)/2}/(1+a²)` contracted against
`(z/h)′ = (z′h − zh′)/h²`, the total `−2·(…)` is

    φ(h) h′ (2Φ(z) − 1) − (1/π) e^{−(h²+z²)/2} · (h z′ − z h′)/(h² + z²)

which is `φ(h)h′(2Φ(z)−1) − (1/π)e^{−(h²+z²)/2} θ′` with `θ = arctan(z/h)`. -/
theorem owen_chain_rule_algebra (h z h' z' : ℝ) (hh : h ≠ 0) :
    -2 * ((-(φ h * (2 * Φ (z / h * h) - 1)) / 2) * h'
        + 1 / (2 * π) * (Real.exp (-h ^ 2 * (1 + (z / h) ^ 2) / 2) / (1 + (z / h) ^ 2))
          * ((z' * h - z * h') / h ^ 2))
      = φ h * h' * (2 * Φ z - 1)
        - 1 / π * Real.exp (-(h ^ 2 + z ^ 2) / 2) * ((h * z' - z * h') / (h ^ 2 + z ^ 2)) := by
  have hp : π ≠ 0 := Real.pi_ne_zero
  have hh2 : (0 : ℝ) < h ^ 2 := by
    rcases lt_or_gt_of_ne hh with hlt | hlt <;> nlinarith
  have hq : (0 : ℝ) < h ^ 2 + z ^ 2 := by nlinarith [sq_nonneg z]
  have e1 : z / h * h = z := div_mul_cancel₀ z hh
  have e2 : (1 : ℝ) + (z / h) ^ 2 = (h ^ 2 + z ^ 2) / h ^ 2 := by
    field_simp
  have e3 : -h ^ 2 * (1 + (z / h) ^ 2) / 2 = -(h ^ 2 + z ^ 2) / 2 := by
    rw [e2]; field_simp
  rw [e1, e3, e2]
  field_simp
  ring

end NonmonicCubic.Gaussian
