/-
The two explicit one-dimensional integrals behind Theorem 1.

* `integral_band_width` : `∫_{-1}^{a²/3} (4/27)(a²-3b)^{3/2} db = (8/405)(a²+3)^{5/2}`
* `integral_p52_shift`  : `∫_{-1}^{1} (8/405)(a²+3)^{5/2} da = 766/1215 + log 3 / 6`

Both are done by exhibiting an explicit antiderivative and applying the
fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`).
The antiderivative for the second is

    F(x) = x (r⁵/6 + 5r³/8 + 45r/16) + (135/16) log (x + r),   r = √(x²+3),

which was checked against `reference/THEOREMS.md`'s value `3064/1215 + (8/3) asinh(1/√3)`
(note `asinh(1/√3) = log 3 / 2`, so that is `766/1215·4 = ...`; numerically both give
`P = 0.10169434037605886…`, matching the reference to 16 digits).
-/
import NonmonicCubic.Basic

namespace NonmonicCubic

open Real Set MeasureTheory intervalIntegral

/-! ## `x ↦ x^{5/2}` -/

/-- `x ↦ x^{5/2}`, extended by `0` below `0`. -/
noncomputable def p52 (x : ℝ) : ℝ := x ^ 2 * Real.sqrt x

theorem continuous_p52 : Continuous p52 := (continuous_pow 2).mul Real.continuous_sqrt

theorem continuous_p32 : Continuous p32 := continuous_id.mul Real.continuous_sqrt

@[simp] theorem p52_zero : p52 0 = 0 := by simp [p52]

theorem p52_eq_sq_mul {s : ℝ} (hs : 0 ≤ s) : p52 (s ^ 2) = s ^ 5 := by
  unfold p52; rw [Real.sqrt_sq hs]; ring

/-- `(x^{5/2})' = (5/2) x^{3/2}` for `x > 0`. -/
theorem hasDerivAt_p52 {x : ℝ} (hx : 0 < x) : HasDerivAt p52 (5 / 2 * p32 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).fun_pow 2
  have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have h := h1.mul h2
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  refine h.congr_deriv ?_
  unfold p32
  field_simp
  linear_combination -hsq

/-! ## The inner integral (over `b`) -/

theorem continuous_shift (a : ℝ) : Continuous fun b : ℝ => a ^ 2 - 3 * b :=
  continuous_const.sub (continuous_const.mul continuous_id)

theorem hasDerivAt_shift (a b : ℝ) : HasDerivAt (fun y : ℝ => a ^ 2 - 3 * y) (-3) b := by
  simpa using ((hasDerivAt_id b).const_mul (3 : ℝ)).const_sub (a ^ 2)

/-- **The band-width integral**, general limits.  Valid as long as the whole
interval lies at or below the parabola `b = a²/3`, so the integrand is the
honest `(a²-3b)^{3/2}` throughout. -/
theorem integral_band_width_gen {a l u : ℝ} (hlu : l ≤ u) (hu : u ≤ a ^ 2 / 3) :
    ∫ b in l..u, 4 / 27 * p32 (a ^ 2 - 3 * b)
      = 8 / 405 * p52 (a ^ 2 - 3 * l) - 8 / 405 * p52 (a ^ 2 - 3 * u) := by
  set H : ℝ → ℝ := fun b => -(8 / 405) * p52 (a ^ 2 - 3 * b) with hHdef
  have hHcont : Continuous H := continuous_const.mul (continuous_p52.comp (continuous_shift a))
  have hderiv : ∀ b ∈ Ioo l u, HasDerivAt H (4 / 27 * p32 (a ^ 2 - 3 * b)) b := by
    intro b hb
    have hpos : 0 < a ^ 2 - 3 * b := by have := hb.2; linarith
    refine (((hasDerivAt_p52 hpos).comp b (hasDerivAt_shift a b)).const_mul
      (-(8 / 405) : ℝ)).congr_deriv ?_
    ring
  rw [integral_eq_sub_of_hasDerivAt_of_le hlu hHcont.continuousOn hderiv
    (((continuous_const.mul (continuous_p32.comp (continuous_shift a)))).intervalIntegrable _ _)]
  simp only [hHdef]
  ring

/-- **The `b`-integral of Theorem 1.**  For every `a`, integrating the band width
`(4/27)(a²-3b)^{3/2}` over `b ∈ [-1, a²/3]` gives `(8/405)(a²+3)^{5/2}`. -/
theorem integral_band_width (a : ℝ) :
    ∫ b in (-1 : ℝ)..(a ^ 2 / 3), 4 / 27 * p32 (a ^ 2 - 3 * b) = 8 / 405 * p52 (a ^ 2 + 3) := by
  have hle : (-1 : ℝ) ≤ a ^ 2 / 3 := by nlinarith [sq_nonneg a]
  rw [integral_band_width_gen hle le_rfl, show a ^ 2 - 3 * (a ^ 2 / 3) = 0 by ring]
  norm_num

/-- `cLo a` is continuous in `b`. -/
theorem continuous_cLo (a : ℝ) : Continuous (cLo a) := by
  unfold cLo
  exact (((continuous_const.mul continuous_id).sub continuous_const).sub
    (continuous_const.mul (continuous_p32.comp (continuous_shift a)))).div_const _

/-- `cHi a` is continuous in `b`. -/
theorem continuous_cHi (a : ℝ) : Continuous (cHi a) := by
  unfold cHi
  exact (((continuous_const.mul continuous_id).sub continuous_const).add
    (continuous_const.mul (continuous_p32.comp (continuous_shift a)))).div_const _

/-- The `b`-integral of the **upper band edge** `cHi` alone (needed for Theorem 2,
where the band is clipped from below by `c = 0`). -/
theorem integral_cHi_gen {a l u : ℝ} (hlu : l ≤ u) (hu : u ≤ a ^ 2 / 3) :
    ∫ b in l..u, cHi a b
      = (a * u ^ 2 / 6 - 2 * a ^ 3 * u / 27 - 4 / 405 * p52 (a ^ 2 - 3 * u))
        - (a * l ^ 2 / 6 - 2 * a ^ 3 * l / 27 - 4 / 405 * p52 (a ^ 2 - 3 * l)) := by
  set K : ℝ → ℝ :=
    fun b => a * b ^ 2 / 6 - 2 * a ^ 3 * b / 27 - 4 / 405 * p52 (a ^ 2 - 3 * b) with hKdef
  have hKcont : Continuous K :=
    (((continuous_const.mul (continuous_pow 2)).div_const 6).sub
      ((continuous_const.mul continuous_id).div_const 27)).sub
      (continuous_const.mul (continuous_p52.comp (continuous_shift a)))
  have hderiv : ∀ b ∈ Ioo l u, HasDerivAt K (cHi a b) b := by
    intro b hb
    have hpos : 0 < a ^ 2 - 3 * b := by have := hb.2; linarith
    have h1 : HasDerivAt (fun y : ℝ => a * y ^ 2 / 6) (a * (2 * b) / 6) b := by
      simpa using (((hasDerivAt_id b).fun_pow 2).const_mul a).div_const 6
    have h2 : HasDerivAt (fun y : ℝ => 2 * a ^ 3 * y / 27) (2 * a ^ 3 / 27) b := by
      simpa using ((hasDerivAt_id b).const_mul (2 * a ^ 3)).div_const 27
    have h3 := ((hasDerivAt_p52 hpos).comp b (hasDerivAt_shift a b)).const_mul (4 / 405 : ℝ)
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    unfold cHi
    ring
  rw [integral_eq_sub_of_hasDerivAt_of_le hlu hKcont.continuousOn hderiv
    ((continuous_cHi a).intervalIntegrable _ _)]

/-! ## The outer integral (over `a`) -/

/-- `r(x) = √(x²+3)`. -/
noncomputable def rr (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 3)

theorem rr_pos (x : ℝ) : 0 < rr x := Real.sqrt_pos.2 (by positivity)

theorem rr_sq (x : ℝ) : rr x ^ 2 = x ^ 2 + 3 := Real.sq_sqrt (by positivity)

/-- `√(x²+3) > |x|`, so `x + r(x) > 0`; needed for the `log` term. -/
theorem add_rr_pos (x : ℝ) : 0 < x + rr x := by
  have h := rr_sq x
  have hp := rr_pos x
  nlinarith

theorem hasDerivAt_rr (x : ℝ) : HasDerivAt rr (x / rr x) x := by
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 3) (2 * x) x := by
    simpa using ((hasDerivAt_id x).fun_pow 2).add_const (3 : ℝ)
  have hne : (fun y : ℝ => y ^ 2 + 3) x ≠ 0 := by positivity
  have h := hinner.sqrt hne
  refine h.congr_deriv ?_
  have := (rr_pos x).ne'
  unfold rr
  field_simp

/-- The antiderivative of `(x²+3)^{5/2}`. -/
noncomputable def Fanti (x : ℝ) : ℝ :=
  x * (rr x ^ 5 / 6 + 5 * rr x ^ 3 / 8 + 45 * rr x / 16) + 135 / 16 * Real.log (x + rr x)

theorem hasDerivAt_Fanti (x : ℝ) : HasDerivAt Fanti (p52 (x ^ 2 + 3)) x := by
  have hr := hasDerivAt_rr x
  have hrpos := rr_pos x
  have hr0 : rr x ≠ 0 := hrpos.ne'
  have hxr : 0 < x + rr x := add_rr_pos x
  have hx2 : x ^ 2 = rr x ^ 2 - 3 := by have := rr_sq x; linarith
  -- derivative of the polynomial-in-`r` factor
  have h5 : HasDerivAt (fun y => rr y ^ 5) (5 * rr x ^ 4 * (x / rr x)) x := by
    simpa using hr.fun_pow 5
  have h3 : HasDerivAt (fun y => rr y ^ 3) (3 * rr x ^ 2 * (x / rr x)) x := by
    simpa using hr.fun_pow 3
  have hP : HasDerivAt (fun y => rr y ^ 5 / 6 + 5 * rr y ^ 3 / 8 + 45 * rr y / 16)
      (5 * rr x ^ 4 * (x / rr x) / 6 + 5 * (3 * rr x ^ 2 * (x / rr x)) / 8
        + 45 * (x / rr x) / 16) x := by
    exact ((h5.div_const 6).add ((h3.const_mul (5 : ℝ)).div_const 8)).add
      ((hr.const_mul (45 : ℝ)).div_const 16)
  have hterm1 := (hasDerivAt_id x).mul hP
  have hlog : HasDerivAt (fun y => Real.log (y + rr y)) (1 / rr x) x := by
    have h := ((hasDerivAt_id x).add hr).log (show x + rr x ≠ 0 from hxr.ne')
    simp only [Pi.add_apply, id_eq] at h
    refine h.congr_deriv ?_
    field_simp
    ring
  have htotal := hterm1.add (hlog.const_mul (135 / 16 : ℝ))
  refine htotal.congr_deriv ?_
  have hp52 : p52 (x ^ 2 + 3) = rr x ^ 5 := by
    have : x ^ 2 + 3 = rr x ^ 2 := (rr_sq x).symm
    rw [this, p52_eq_sq_mul hrpos.le]
  rw [hp52]
  simp only [id_eq]
  field_simp
  linear_combination (640 * rr x ^ 4 + 1440 * rr x ^ 2 + 2160) * hx2

/-- **The `a`-integral.**  `∫_{-1}^{1} (8/405)(a²+3)^{5/2} da = 766/1215 + log 3 / 6`. -/
theorem integral_p52_shift :
    ∫ a in (-1 : ℝ)..1, 8 / 405 * p52 (a ^ 2 + 3) = 766 / 1215 + Real.log 3 / 6 := by
  have hderiv : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => 8 / 405 * Fanti y) (8 / 405 * p52 (x ^ 2 + 3)) x :=
    fun x _ => (hasDerivAt_Fanti x).const_mul _
  have hint : IntervalIntegrable (fun x : ℝ => 8 / 405 * p52 (x ^ 2 + 3)) volume (-1) 1 :=
    (continuous_const.mul
      (continuous_p52.comp ((continuous_pow 2).add continuous_const))).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hr1 : rr 1 = 2 := by unfold rr; norm_num
  have hrm1 : rr (-1) = 2 := by unfold rr; norm_num
  unfold Fanti
  rw [hr1, hrm1]
  norm_num
  ring

end NonmonicCubic
