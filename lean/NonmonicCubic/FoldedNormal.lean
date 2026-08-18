/-
# The folded-normal mean

Step 3c of the Rice-formula-free route to Problem A (`KacRice.lean`).  The inner
`(a,b)`-integral, after the affine change of variables that diagonalises it, is
the mean of `|W|` for `W ~ N(m, σ²)`.  Mathlib has no Gaussian moments beyond
the mean and the variance — no `E|X|`, no `E[X^{2k}]`, nothing (checked
2026-08-18) — so this is built here.

The standardised statement is

    ∫ |s + c| φ(s) ds = 2 φ(c) + c (2 Φ(c) − 1)                (`integral_abs_add_mul_φ`)

and the scaled one, which is what the Kac–Rice integrand uses,

    ∫ |m + σ s| φ(s) ds = 2 σ φ(m/σ) + m (2 Φ(m/σ) − 1)        (`integral_abs_scaled`)

for `σ > 0`.  Note `2 φ(c) = √(2/π) e^{−c²/2}`, so the second is the textbook
`E|W| = σ√(2/π) e^{−m²/(2σ²)} + m (2Φ(m/σ) − 1)`; the `2φ` form is used here
because it avoids `√(2/π)` entirely.

The proof is the obvious one, and it is worth recording that it *is* obvious
once `Φ` exists: `cΦ − φ` is an explicit antiderivative of `(s + c) φ(s)`,
because `φ′(s) = −s φ(s)` and `Φ′ = φ`.  Splitting `ℝ` at `s = −c`, where the
absolute value changes sign, and applying the improper fundamental theorem of
calculus on each half-line gives the result; the limits of `cΦ − φ` at `±∞`
are `c` and `0`, which is what `NormalCDF.lean`'s `tendsto_Φ_atTop`/`atBot`
supply.
-/
import NonmonicCubic.NormalCDF

namespace NonmonicCubic.Gaussian

open MeasureTheory Real Set Filter intervalIntegral

/-! ## The antiderivative -/

/-- `φ′(s) = −s φ(s)`. -/
theorem hasDerivAt_φ (s : ℝ) : HasDerivAt φ (-(s * φ s)) s := by
  have hin : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-((2 : ℕ) * s ^ 1) / 2) s :=
    ((hasDerivAt_pow 2 s).neg).div_const 2
  have h := hin.exp.div_const (Real.sqrt (2 * π))
  have heq : -(s * φ s)
      = Real.exp (-s ^ 2 / 2) * (-((2 : ℕ) * s ^ 1) / 2) / Real.sqrt (2 * π) := by
    unfold φ; push_cast; ring
  rw [heq]
  exact h

/-- **The antiderivative.**  `(cΦ − φ)′ = (s + c) φ(s)`. -/
theorem hasDerivAt_foldAnti (c s : ℝ) :
    HasDerivAt (fun t => c * Φ t - φ t) ((s + c) * φ s) s := by
  have h := ((hasDerivAt_Φ s).const_mul c).sub (hasDerivAt_φ s)
  have heq : (s + c) * φ s = c * φ s - -(s * φ s) := by ring
  rw [heq]
  exact h

theorem continuous_foldAnti (c : ℝ) : Continuous (fun t => c * Φ t - φ t) :=
  (continuous_Φ.const_mul c).sub continuous_φ

theorem tendsto_foldAnti_atTop (c : ℝ) :
    Tendsto (fun t => c * Φ t - φ t) atTop (nhds c) := by
  simpa using (tendsto_Φ_atTop.const_mul c).sub tendsto_φ_atTop

theorem tendsto_foldAnti_atBot (c : ℝ) :
    Tendsto (fun t => c * Φ t - φ t) atBot (nhds 0) := by
  simpa using (tendsto_Φ_atBot.const_mul c).sub tendsto_φ_atBot

/-! ## Integrability -/

theorem integrable_id_mul_φ : Integrable (fun s : ℝ => s * φ s) := by
  have h : Integrable (fun s : ℝ => s * Real.exp (-(1 / 2 : ℝ) * s ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  refine (h.div_const (Real.sqrt (2 * π))).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [φ_eq]; ring

theorem integrable_lin_mul_φ (c : ℝ) : Integrable (fun s : ℝ => (s + c) * φ s) := by
  refine (integrable_id_mul_φ.add (integrable_φ.const_mul c)).congr
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]; ring

theorem integrable_abs_lin_mul_φ (c : ℝ) : Integrable (fun s : ℝ => |s + c| * φ s) := by
  refine ((integrable_lin_mul_φ c).abs).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [abs_mul]
  rw [abs_of_pos (φ_pos s)]

/-! ## The two half-lines -/

theorem integral_Ioi_lin_mul_φ (c : ℝ) :
    ∫ s in Ioi (-c), (s + c) * φ s = c - (c * Φ (-c) - φ c) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t => c * Φ t - φ t) (f' := fun s => (s + c) * φ s) (a := -c) (m := c)
    (continuous_foldAnti c).continuousWithinAt (fun x _ => hasDerivAt_foldAnti c x)
    (integrable_lin_mul_φ c).integrableOn (tendsto_foldAnti_atTop c)
  rw [h, φ_neg]

theorem integral_Iic_lin_mul_φ (c : ℝ) :
    ∫ s in Iic (-c), (s + c) * φ s = c * Φ (-c) - φ c := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto
    (f := fun t => c * Φ t - φ t) (f' := fun s => (s + c) * φ s) (a := -c) (m := 0)
    (continuous_foldAnti c).continuousWithinAt (fun x _ => hasDerivAt_foldAnti c x)
    (integrable_lin_mul_φ c).integrableOn (tendsto_foldAnti_atBot c)
  rw [h, φ_neg, sub_zero]

/-! ## The folded-normal mean -/

/-- **The folded-normal mean, standardised.**

    ∫ |s + c| φ(s) ds = 2 φ(c) + c (2 Φ(c) − 1).

Absent from Mathlib, which has no Gaussian moments beyond mean and variance. -/
theorem integral_abs_add_mul_φ (c : ℝ) :
    ∫ s : ℝ, |s + c| * φ s = 2 * φ c + c * (2 * Φ c - 1) := by
  have hI := integrable_abs_lin_mul_φ c
  have hsplit : (∫ s in Iic (-c), |s + c| * φ s) + ∫ s in Ioi (-c), |s + c| * φ s
      = ∫ s : ℝ, |s + c| * φ s := integral_Iic_add_Ioi hI.integrableOn hI.integrableOn
  have hIic : ∫ s in Iic (-c), |s + c| * φ s = -∫ s in Iic (-c), (s + c) * φ s := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
    have hs' : s + c ≤ 0 := by have : s ≤ -c := hs; linarith
    rw [abs_of_nonpos hs']; ring
  have hIoi : ∫ s in Ioi (-c), |s + c| * φ s = ∫ s in Ioi (-c), (s + c) * φ s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : (0 : ℝ) ≤ s + c := by have : -c < s := hs; linarith
    rw [abs_of_nonneg hs']
  have hsym : Φ (-c) = 1 - Φ c := by have := Φ_add_Φ_neg c; linarith
  rw [← hsplit, hIic, hIoi, integral_Ioi_lin_mul_φ, integral_Iic_lin_mul_φ, hsym]
  ring

/-- **The folded-normal mean.**  For `σ > 0` and `W = m + σ s` with `s` standard
normal, `E|W| = 2σ φ(m/σ) + m (2 Φ(m/σ) − 1)`.

Since `2φ(t) = √(2/π) e^{−t²/2}`, this is the textbook
`E|W| = σ√(2/π) e^{−m²/(2σ²)} + m (2Φ(m/σ) − 1)`.  In the Kac–Rice integrand
`m = h′` and `σ = v`, giving `φ(h)·[2 v φ(z) + h′ (2Φ(z) − 1)]` with `z = h′/v`
— the two `√q` factors having already cancelled (`KacRice.ratio_sq_eq`). -/
theorem integral_abs_scaled (m σ : ℝ) (hσ : 0 < σ) :
    ∫ s : ℝ, |m + σ * s| * φ s = 2 * σ * φ (m / σ) + m * (2 * Φ (m / σ) - 1) := by
  have hσ' : σ ≠ 0 := hσ.ne'
  have hc : ∀ s : ℝ, |m + σ * s| * φ s = σ * (|s + m / σ| * φ s) := by
    intro s
    have h : m + σ * s = σ * (s + m / σ) := by field_simp; ring
    rw [h, abs_mul, abs_of_pos hσ]; ring
  simp_rw [hc]
  rw [MeasureTheory.integral_const_mul, integral_abs_add_mul_φ]
  field_simp

end NonmonicCubic.Gaussian
