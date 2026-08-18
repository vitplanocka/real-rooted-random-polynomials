/-
# The standard normal density and CDF

Mathlib has `gaussianPDFReal` and `gaussianReal`, but — checked 2026-08-18,
Mathlib v4.33.0 — it has **no standard normal CDF and no `erf`/`erfc` at all**.
`Probability/CDF.lean` defines only the generic `ProbabilityTheory.cdf` as a
`StieltjesFunction`, with no derivative and no closed form; the Gaussian
directory contains no `cdf` lemma and not even
`gaussianReal μ v (Iic x) = …` in unevaluated form.  (Exponential, Gamma and
Pareto all *do* have `cdf_*_eq` lemmas, so the omission is conspicuous.)

Problem A's Kac–Rice integrand contains `2Φ(z) − 1`, so `Φ` has to exist before
any of the analysis can be stated.  This file supplies it, with the minimum
useful API.

`Φ` is *defined* as `1/2 + ∫₀ˣ φ` rather than as `∫_{Iic x} φ`, because that makes
the fundamental theorem of calculus apply directly
(`Continuous.integral_hasStrictDerivAt`), which is the property actually used.
Identifying it with `∫_{Iic x} φ` is not done here and is not needed for the
Kac–Rice integrand.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace NonmonicCubic.Gaussian

open MeasureTheory Real intervalIntegral

/-- The standard normal density `φ t = e^{−t²/2} / √(2π)`. -/
noncomputable def φ (t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2) / Real.sqrt (2 * π)

theorem φ_eq (t : ℝ) : φ t = Real.exp (-(1 / 2) * t ^ 2) / Real.sqrt (2 * π) := by
  unfold φ; congr 2; ring

theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)

theorem φ_pos (t : ℝ) : 0 < φ t := by
  unfold φ; positivity

@[fun_prop]
theorem continuous_φ : Continuous φ := by
  unfold φ; fun_prop

/-- `φ` is even. -/
theorem φ_neg (t : ℝ) : φ (-t) = φ t := by
  unfold φ; congr 2; ring

theorem integrable_φ : Integrable φ := by
  have h : Integrable fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2) :=
    integrable_exp_neg_mul_sq (by norm_num)
  simpa only [← φ_eq] using h.div_const (Real.sqrt (2 * π))

/-- **`∫ φ = 1`.**  The normalisation, from Mathlib's `integral_gaussian`. -/
theorem integral_φ : ∫ t, φ t = 1 := by
  simp only [φ_eq]
  rw [MeasureTheory.integral_div, integral_gaussian, show π / (1 / 2) = 2 * π by ring]
  exact div_self sqrt_two_pi_pos.ne'

/-- The standard normal CDF. -/
noncomputable def Φ (x : ℝ) : ℝ := 1 / 2 + ∫ t in (0 : ℝ)..x, φ t

theorem Φ_zero : Φ 0 = 1 / 2 := by simp [Φ]

/-- **`Φ′ = φ`.**  Immediate from the fundamental theorem of calculus, which is
why `Φ` is defined by an interval integral. -/
theorem hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  unfold Φ
  exact ((continuous_φ.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add (1 / 2 : ℝ)

theorem deriv_Φ (x : ℝ) : deriv Φ x = φ x := (hasDerivAt_Φ x).deriv

theorem differentiable_Φ : Differentiable ℝ Φ := fun x => (hasDerivAt_Φ x).differentiableAt

@[fun_prop]
theorem continuous_Φ : Continuous Φ := differentiable_Φ.continuous

/-- **`Φ(x) + Φ(−x) = 1`**, i.e. the symmetry of the normal law. -/
theorem Φ_add_Φ_neg (x : ℝ) : Φ x + Φ (-x) = 1 := by
  have h : ∫ t in (0 : ℝ)..(-x), φ t = -∫ t in (0 : ℝ)..x, φ t := by
    have hc : (∫ t in (0 : ℝ)..x, φ (-t)) = ∫ t in (-x)..(-0 : ℝ), φ t := by
      rw [intervalIntegral.integral_comp_neg]
    simp only [φ_neg, neg_zero] at hc
    rw [intervalIntegral.integral_symm 0 (-x)] at hc
    linarith
  unfold Φ
  rw [h]; ring


/-! ## Limits at `±∞`

These are what the folded-normal mean needs: the antiderivative
`−φ + cΦ` must have known limits at both ends for the improper fundamental
theorem of calculus to apply. -/

theorem tendsto_φ_atTop : Filter.Tendsto φ Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => -t ^ 2 / 2) Filter.atTop Filter.atBot := by
    have h : Filter.Tendsto (fun t : ℝ => t ^ 2 / 2) Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    simpa [neg_div] using h
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 := h2.div_const (Real.sqrt (2 * π))
  rw [zero_div] at h3
  exact h3

theorem tendsto_φ_atBot : Filter.Tendsto φ Filter.atBot (nhds 0) := by
  have h := tendsto_φ_atTop.comp Filter.tendsto_neg_atBot_atTop
  simpa [Function.comp_def, φ_neg] using h

theorem integral_Ioi_φ : ∫ t in Set.Ioi (0 : ℝ), φ t = 1 / 2 := by
  have hIic : IntegrableOn φ (Set.Iic 0) := integrable_φ.integrableOn
  have hIoi : IntegrableOn φ (Set.Ioi 0) := integrable_φ.integrableOn
  have hsplit : (∫ t in Set.Iic (0 : ℝ), φ t) + ∫ t in Set.Ioi (0 : ℝ), φ t = 1 := by
    rw [integral_Iic_add_Ioi hIic hIoi]; exact integral_φ
  have hsym : (∫ t in Set.Iic (0 : ℝ), φ t) = ∫ t in Set.Ioi (0 : ℝ), φ t := by
    simpa [φ_neg] using integral_comp_neg_Iic (0 : ℝ) φ
  linarith

theorem integral_Iic_φ : ∫ t in Set.Iic (0 : ℝ), φ t = 1 / 2 := by
  have hsym : (∫ t in Set.Iic (0 : ℝ), φ t) = ∫ t in Set.Ioi (0 : ℝ), φ t := by
    simpa [φ_neg] using integral_comp_neg_Iic (0 : ℝ) φ
  rw [hsym, integral_Ioi_φ]

theorem tendsto_Φ_atTop : Filter.Tendsto Φ Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun y : ℝ => ∫ t in (0 : ℝ)..y, φ t) Filter.atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ), φ t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 integrable_φ.integrableOn Filter.tendsto_id
  rw [integral_Ioi_φ] at h
  have h2 := h.const_add (1 / 2 : ℝ)
  rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num] at h2
  exact h2

theorem tendsto_Φ_atBot : Filter.Tendsto Φ Filter.atBot (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => ∫ t in y..(0 : ℝ), φ t) Filter.atBot
      (nhds (∫ t in Set.Iic (0 : ℝ), φ t)) :=
    intervalIntegral_tendsto_integral_Iic 0 integrable_φ.integrableOn Filter.tendsto_id
  rw [integral_Iic_φ] at h
  have hfun : (fun y : ℝ => ∫ t in y..(0 : ℝ), φ t) = fun y => -∫ t in (0 : ℝ)..y, φ t := by
    funext y; exact intervalIntegral.integral_symm 0 y
  rw [hfun] at h
  have h2 : Filter.Tendsto (fun y : ℝ => ∫ t in (0 : ℝ)..y, φ t) Filter.atBot
      (nhds (-(1 / 2 : ℝ))) := by simpa using h.neg
  have h3 := h2.const_add (1 / 2 : ℝ)
  rw [show (1 : ℝ) / 2 + -(1 / 2) = 0 by norm_num] at h3
  exact h3


/-! ## `Φ` takes values in `[0,1]` -/

theorem strictMono_Φ : StrictMono Φ :=
  strictMono_of_deriv_pos fun x => by rw [deriv_Φ]; exact φ_pos x

theorem Φ_le_one (x : ℝ) : Φ x ≤ 1 :=
  strictMono_Φ.monotone.ge_of_tendsto tendsto_Φ_atTop x

theorem Φ_nonneg (x : ℝ) : 0 ≤ Φ x :=
  strictMono_Φ.monotone.le_of_tendsto tendsto_Φ_atBot x

/-- `|2Φ(x) − 1| ≤ 1`, the bound the Kac–Rice integrand needs. -/
theorem abs_two_Φ_sub_one_le (x : ℝ) : |2 * Φ x - 1| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [Φ_nonneg x, Φ_le_one x]

end NonmonicCubic.Gaussian
