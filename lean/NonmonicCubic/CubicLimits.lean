/-
# The specific `h`, `z` of the monic Gaussian cubic, and their boundary behaviour

`OwenCancellation.integral_owenPsiDeriv_eq_one` is stated for an abstract pair
`(h, z)`.  This file supplies the pair — `h = hA`, `z = zB` — in closed form and
verifies the boundary hypotheses:

    h  = x³/√q,        z = x²(x⁴+2x²+3)/(√q·√(x⁴+4x²+1))
    z/h = (x⁴+2x²+3)/(x·√(x⁴+4x²+1))   → ±∞  as x → 0^±
    h·z = x⁵(x⁴+2x²+3)/(q·√(x⁴+4x²+1)) → 0   as x → 0
    h²  = x⁶/q ≥ x²/3 for |x| ≥ 1,  so exp(−h²/2) → 0 at ±∞
-/
import NonmonicCubic.Assembly
import NonmonicCubic.OwenCancellation

namespace NonmonicCubic.Gaussian

open MeasureTheory Real Filter Set
open NonmonicCubic.GaussianCubic

theorem wA_pos (x : ℝ) : (0 : ℝ) < x ^ 4 + 4 * x ^ 2 + 1 := by positivity

theorem sqrt_qA_pos (x : ℝ) : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 (qA_pos x)

theorem sqrt_wA_pos (x : ℝ) : (0 : ℝ) < Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) :=
  Real.sqrt_pos.2 (wA_pos x)

/-- `s = √(x⁴+4x²+1)/√q`. -/
theorem sB_eq (x : ℝ) : sB x = Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / Real.sqrt (qA x) := by
  rw [eq_div_iff (sqrt_qA_pos x).ne']
  exact sB_mul_sqrt_qA x

/-- `z` in closed form. -/
theorem zB_eq (x : ℝ) :
    zB x = x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3)
      / (Real.sqrt (qA x) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
  unfold zB mB
  rw [sB_eq]
  set S := Real.sqrt (qA x) with hSdef
  set W := Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) with hWdef
  have hS : S ≠ 0 := by rw [hSdef]; exact (sqrt_qA_pos x).ne'
  have hW : W ≠ 0 := by rw [hWdef]; exact (sqrt_wA_pos x).ne'
  have hSq : S ^ 2 = qA x := by rw [hSdef]; exact Real.sq_sqrt (qA_pos x).le
  rw [← hSq]
  field_simp

theorem hA_ne_zero {x : ℝ} (hx : x ≠ 0) : hA x ≠ 0 := by
  unfold hA
  exact div_ne_zero (pow_ne_zero 3 hx) (sqrt_qA_pos x).ne'

/-- `h·z` in closed form: continuous, and `0` at the origin. -/
theorem hA_mul_zB (x : ℝ) :
    hA x * zB x = x ^ 5 * (x ^ 4 + 2 * x ^ 2 + 3)
      / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
  unfold hA
  rw [zB_eq]
  set S := Real.sqrt (qA x) with hSdef
  set W := Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) with hWdef
  have hS : S ≠ 0 := by rw [hSdef]; exact (sqrt_qA_pos x).ne'
  have hW : W ≠ 0 := by rw [hWdef]; exact (sqrt_wA_pos x).ne'
  have hSq : S ^ 2 = qA x := by rw [hSdef]; exact Real.sq_sqrt (qA_pos x).le
  rw [← hSq]
  field_simp

/-- `z/h` in closed form. -/
theorem zB_div_hA {x : ℝ} (hx : x ≠ 0) :
    zB x / hA x = (x ^ 4 + 2 * x ^ 2 + 3) / (x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
  have hS : Real.sqrt (qA x) ≠ 0 := (sqrt_qA_pos x).ne'
  have hW : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (sqrt_wA_pos x).ne'
  unfold hA
  rw [zB_eq]
  field_simp

/-! ## `h²` grows: `exp(−h²/2) → 0` at `±∞` -/

theorem hA_sq_ge {x : ℝ} (hx : 1 ≤ |x|) : x ^ 2 / 3 ≤ hA x ^ 2 := by
  have hq := qA_pos x
  have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [hA_sq, div_le_div_iff₀ (by norm_num) hq]
  unfold qA
  nlinarith [hx2, sq_nonneg x, sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2)]

theorem tendsto_hA_sq_atTop : Tendsto (fun x => hA x ^ 2) atTop atTop := by
  have hb : Tendsto (fun x : ℝ => x ^ 2 / 3) atTop atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact hA_sq_ge (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]; linarith)

theorem tendsto_hA_sq_atBot : Tendsto (fun x => hA x ^ 2) atBot atTop := by
  have hb : Tendsto (fun x : ℝ => x ^ 2 / 3) atBot atTop := by
    have := (Filter.tendsto_pow_atTop (n := 2) two_ne_zero).atTop_div_const
      (by norm_num : (0:ℝ) < 3)
    have hcomp := this.comp Filter.tendsto_neg_atBot_atTop
    simpa [Function.comp_def] using hcomp
  refine tendsto_atTop_mono' atBot ?_ hb
  filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
  exact hA_sq_ge (by rw [abs_of_nonpos (by linarith : x ≤ (0:ℝ))]; linarith)

theorem tendsto_exp_hA_atTop :
    Tendsto (fun x => Real.exp (-(hA x) ^ 2 / 2)) atTop (nhds 0) := by
  have h1 : Tendsto (fun x => -(hA x) ^ 2 / 2) atTop atBot := by
    have h := tendsto_hA_sq_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2)
    simpa [neg_div] using h
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1

theorem tendsto_exp_hA_atBot :
    Tendsto (fun x => Real.exp (-(hA x) ^ 2 / 2)) atBot (nhds 0) := by
  have h1 : Tendsto (fun x => -(hA x) ^ 2 / 2) atBot atBot := by
    have h := tendsto_hA_sq_atBot.atTop_div_const (by norm_num : (0:ℝ) < 2)
    simpa [neg_div] using h
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp h1


/-! ## The limits at `0^±` -/

theorem tendsto_hA_mul_zB : Tendsto (fun x => hA x * zB x) (nhds 0) (nhds 0) := by
  have hcont : Continuous fun x : ℝ =>
      x ^ 5 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) :=
    Continuous.div (by fun_prop) (by unfold qA; fun_prop)
      fun x => (mul_pos (qA_pos x) (sqrt_wA_pos x)).ne'
  have h := hcont.tendsto 0
  have hval : (0 : ℝ) ^ 5 * ((0 : ℝ) ^ 4 + 2 * (0 : ℝ) ^ 2 + 3)
      / (qA 0 * Real.sqrt ((0 : ℝ) ^ 4 + 4 * (0 : ℝ) ^ 2 + 1)) = 0 := by norm_num [qA]
  rw [hval] at h
  simpa only [hA_mul_zB] using h

theorem tendsto_zB_div_hA_atTop :
    Tendsto (fun x => zB x / hA x) (nhdsWithin 0 (Ioi 0)) atTop := by
  have hEq : (fun x => zB x / hA x) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      fun x => (x ^ 4 + 2 * x ^ 2 + 3) * (x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1))⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [zB_div_hA (ne_of_gt (show (0 : ℝ) < x from hx)), div_eq_mul_inv]
  refine Filter.Tendsto.congr' hEq.symm ?_
  have hnum : Tendsto (fun x : ℝ => x ^ 4 + 2 * x ^ 2 + 3) (nhdsWithin 0 (Ioi 0)) (nhds 3) := by
    have hc := (by fun_prop : Continuous fun x : ℝ => x ^ 4 + 2 * x ^ 2 + 3).tendsto (0 : ℝ)
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun x : ℝ => x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc := (by fun_prop :
        Continuous fun x : ℝ => x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)).tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos (show (0 : ℝ) < x from hx) (sqrt_wA_pos x)
  exact Filter.Tendsto.pos_mul_atTop (by norm_num) hnum (tendsto_inv_nhdsGT_zero.comp hden)

theorem tendsto_zB_div_hA_atBot :
    Tendsto (fun x => zB x / hA x) (nhdsWithin 0 (Iio 0)) atBot := by
  have hEq : (fun x => zB x / hA x) =ᶠ[nhdsWithin (0 : ℝ) (Iio 0)]
      fun x => (x ^ 4 + 2 * x ^ 2 + 3) * (x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1))⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [zB_div_hA (ne_of_lt (show x < (0 : ℝ) from hx)), div_eq_mul_inv]
  refine Filter.Tendsto.congr' hEq.symm ?_
  have hnum : Tendsto (fun x : ℝ => x ^ 4 + 2 * x ^ 2 + 3) (nhdsWithin 0 (Iio 0)) (nhds 3) := by
    have hc := (by fun_prop : Continuous fun x : ℝ => x ^ 4 + 2 * x ^ 2 + 3).tendsto (0 : ℝ)
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun x : ℝ => x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1))
      (nhdsWithin 0 (Iio 0)) (nhdsWithin 0 (Iio 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc := (by fun_prop :
        Continuous fun x : ℝ => x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)).tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_neg_of_neg_of_pos (show x < (0 : ℝ) from hx) (sqrt_wA_pos x)
  exact Filter.Tendsto.pos_mul_atBot (by norm_num) hnum (tendsto_inv_nhdsLT_zero.comp hden)

/-- `T(h, z/h) → 1/4` as `x → 0⁺`. -/
theorem tendsto_owenT_cubic_pos :
    Tendsto (fun x => owenT (hA x) (zB x / hA x)) (nhdsWithin 0 (Ioi 0)) (nhds (1 / 4)) := by
  refine tendsto_owenT_quarter ?_ tendsto_zB_div_hA_atTop
  have hEq : ∀ᶠ x in nhdsWithin (0 : ℝ) (Ioi 0), hA x * zB x = hA x ^ 2 * (zB x / hA x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne := hA_ne_zero (ne_of_gt (show (0 : ℝ) < x from hx))
    field_simp
  exact Filter.Tendsto.congr' hEq (tendsto_hA_mul_zB.mono_left nhdsWithin_le_nhds)

/-- `T(h, z/h) → −1/4` as `x → 0⁻`. -/
theorem tendsto_owenT_cubic_neg :
    Tendsto (fun x => owenT (hA x) (zB x / hA x)) (nhdsWithin 0 (Iio 0)) (nhds (-(1 / 4))) := by
  refine tendsto_owenT_neg_quarter ?_ tendsto_zB_div_hA_atBot
  have hEq : ∀ᶠ x in nhdsWithin (0 : ℝ) (Iio 0), hA x * zB x = hA x ^ 2 * (zB x / hA x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne := hA_ne_zero (ne_of_lt (show x < (0 : ℝ) from hx))
    field_simp
  exact Filter.Tendsto.congr' hEq (tendsto_hA_mul_zB.mono_left nhdsWithin_le_nhds)


/-! ## The derivative of `z`

`z = P/√G` with `P = x⁶+2x⁴+3x²` and `G = q·(x⁴+4x²+1) = x⁸+5x⁶+6x⁴+5x²+1`, so

    z′ = (2P′G − P G′)/(2 G^{3/2}) = x·N / G^{3/2},
    N = 2x¹²+15x¹⁰+28x⁸+34x⁶+36x⁴+23x²+6

the middle step being the polynomial identity `2P′G − P G′ = 2xN`. -/

/-- `G = q·(x⁴+4x²+1)`. -/
def GA (x : ℝ) : ℝ := x ^ 8 + 5 * x ^ 6 + 6 * x ^ 4 + 5 * x ^ 2 + 1

theorem GA_pos (x : ℝ) : (0 : ℝ) < GA x := by unfold GA; positivity

theorem GA_eq (x : ℝ) : GA x = qA x * (x ^ 4 + 4 * x ^ 2 + 1) := by unfold GA qA; ring

theorem zB_eq' (x : ℝ) : zB x = (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2) / Real.sqrt (GA x) := by
  rw [zB_eq, GA_eq, Real.sqrt_mul (qA_pos x).le]
  ring_nf

/-- The polynomial identity behind `z′`: `2P′G − P G′ = 2xN`. -/
theorem zB_deriv_poly (x : ℝ) :
    2 * (6 * x ^ 5 + 8 * x ^ 3 + 6 * x) * GA x
        - (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2) * (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x)
      = 2 * x * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4
          + 23 * x ^ 2 + 6) := by
  unfold GA; ring

theorem hasDerivAt_GA (x : ℝ) :
    HasDerivAt GA (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) x := by
  unfold GA
  have h := ((((hasDerivAt_pow 8 x).add ((hasDerivAt_pow 6 x).const_mul 5)).add
    ((hasDerivAt_pow 4 x).const_mul 6)).add ((hasDerivAt_pow 2 x).const_mul 5)).add_const 1
  have heq : 8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x
      = (8 : ℕ) * x ^ 7 + 5 * ((6 : ℕ) * x ^ 5) + 6 * ((4 : ℕ) * x ^ 3)
        + 5 * ((2 : ℕ) * x ^ 1) := by push_cast; ring
  rw [heq]
  exact h

theorem hasDerivAt_zB_num (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 6 + 2 * y ^ 4 + 3 * y ^ 2)
      (6 * x ^ 5 + 8 * x ^ 3 + 6 * x) x := by
  have h := ((hasDerivAt_pow 6 x).add ((hasDerivAt_pow 4 x).const_mul 2)).add
    ((hasDerivAt_pow 2 x).const_mul 3)
  have heq : 6 * x ^ 5 + 8 * x ^ 3 + 6 * x
      = (6 : ℕ) * x ^ 5 + 2 * ((4 : ℕ) * x ^ 3) + 3 * ((2 : ℕ) * x ^ 1) := by push_cast; ring
  rw [heq]
  exact h

/-- `(√G)′` written with `√G` in the *numerator*, which keeps every later
cross-multiplication linear in `√G`. -/
theorem hasDerivAt_sqrt_GA (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (GA y))
      ((8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x) / (2 * GA x)) x := by
  have hG := GA_pos x
  have h := (hasDerivAt_GA x).sqrt hG.ne'
  have he : (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x) / (2 * GA x)
      = (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) / (2 * Real.sqrt (GA x)) := by
    rw [div_eq_div_iff (by positivity) (by positivity),
      show (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x)
          * (2 * Real.sqrt (GA x))
        = (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * 2
          * (Real.sqrt (GA x) * Real.sqrt (GA x)) by ring,
      Real.mul_self_sqrt hG.le]
    ring
  rw [he]
  exact h

/-- **`z′ = x·N·√G / G²`**, i.e. `x·N/G^{3/2}`. -/
theorem hasDerivAt_zB (x : ℝ) :
    HasDerivAt zB
      (x * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4 + 23 * x ^ 2 + 6)
        * Real.sqrt (GA x) / GA x ^ 2) x := by
  have hG := GA_pos x
  have hS : Real.sqrt (GA x) ≠ 0 := (Real.sqrt_pos.2 hG).ne'
  have hS2 : Real.sqrt (GA x) ^ 2 = GA x := Real.sq_sqrt hG.le
  have hdiv := (hasDerivAt_zB_num x).div (hasDerivAt_sqrt_GA x) hS
  have hfun2 : ((fun y : ℝ => y ^ 6 + 2 * y ^ 4 + 3 * y ^ 2) / fun y : ℝ => Real.sqrt (GA y))
      = zB := by
    funext y; simp only [Pi.div_apply]; exact (zB_eq' y).symm
  rw [hfun2] at hdiv
  have hnum : (6 * x ^ 5 + 8 * x ^ 3 + 6 * x) * Real.sqrt (GA x)
        - (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2)
          * ((8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x) / (2 * GA x))
      = x * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4 + 23 * x ^ 2 + 6)
        * Real.sqrt (GA x) / GA x := by
    have step : (6 * x ^ 5 + 8 * x ^ 3 + 6 * x) * Real.sqrt (GA x)
        - (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2)
          * ((8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x) / (2 * GA x))
        = Real.sqrt (GA x) * ((2 * (6 * x ^ 5 + 8 * x ^ 3 + 6 * x) * GA x
            - (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2)
              * (8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x)) / (2 * GA x)) := by
      field_simp
    rw [step, zB_deriv_poly]
    field_simp
  have heq : x * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4
        + 23 * x ^ 2 + 6) * Real.sqrt (GA x) / GA x ^ 2
      = ((6 * x ^ 5 + 8 * x ^ 3 + 6 * x) * Real.sqrt (GA x)
          - (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2)
            * ((8 * x ^ 7 + 30 * x ^ 5 + 24 * x ^ 3 + 10 * x) * Real.sqrt (GA x) / (2 * GA x)))
        / Real.sqrt (GA x) ^ 2 := by
    rw [hnum, hS2]
    field_simp
  rw [heq]
  exact hdiv


/-! ## `θ′` in closed form

`θ′ = (h z′ − z h′)/(h² + z²)`.  Both numerator and denominator reduce by two
polynomial identities (checked in sympy first, `ring` here):

    x⁶w + P²   = q x⁴ (x⁴+4x²+9)                      (equation (7))
    x⁴N − P²w  = q x⁴ (x⁸+6x⁶−6x⁴−22x²−3)

whence `θ′ = N₂/(q·√w·(x⁴+4x²+9))`, `N₂ = x⁸+6x⁶−6x⁴−22x²−3` — an explicit
algebraic function with **no** singularity, `θ′(0) = −3/9 = −1/3`. -/

/-- `h′`. -/
noncomputable def hA' (x : ℝ) : ℝ :=
  x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))

/-- `z′`. -/
noncomputable def zB' (x : ℝ) : ℝ :=
  x * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4 + 23 * x ^ 2 + 6)
    * Real.sqrt (GA x) / GA x ^ 2

theorem hasDerivAt_hA' (x : ℝ) : HasDerivAt hA (hA' x) x := hasDerivAt_hA x

theorem hasDerivAt_zB' (x : ℝ) : HasDerivAt zB (zB' x) x := hasDerivAt_zB x

theorem sqrt_GA_eq (x : ℝ) :
    Real.sqrt (GA x) = Real.sqrt (qA x) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) := by
  rw [GA_eq, Real.sqrt_mul (qA_pos x).le]

theorem zB_sq (x : ℝ) : zB x ^ 2 = (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2) ^ 2 / GA x := by
  rw [zB_eq', div_pow, Real.sq_sqrt (GA_pos x).le]

/-- **Equation (7)**: `h² + z² = x⁴(x⁴+4x²+9)/(x⁴+4x²+1)`. -/
theorem hA_sq_add_zB_sq (x : ℝ) :
    hA x ^ 2 + zB x ^ 2 = x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1) := by
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hw : (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (wA_pos x).ne'
  rw [hA_sq, zB_sq, GA_eq]
  field_simp
  unfold qA
  ring

theorem hA_mul_zB' (x : ℝ) :
    hA x * zB' x
      = x ^ 4 * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4
          + 23 * x ^ 2 + 6) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)
        / (qA x ^ 2 * (x ^ 4 + 4 * x ^ 2 + 1) ^ 2) := by
  have hS : Real.sqrt (qA x) ≠ 0 := (sqrt_qA_pos x).ne'
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hw : (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (wA_pos x).ne'
  unfold hA zB'
  rw [sqrt_GA_eq, GA_eq]
  field_simp

theorem zB_mul_hA' (x : ℝ) :
    zB x * hA' x
      = (x ^ 6 + 2 * x ^ 4 + 3 * x ^ 2) ^ 2
        / (qA x ^ 2 * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
  have hS : Real.sqrt (qA x) ≠ 0 := (sqrt_qA_pos x).ne'
  have hT : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (sqrt_wA_pos x).ne'
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hS2 : Real.sqrt (qA x) ^ 2 = qA x := Real.sq_sqrt (qA_pos x).le
  unfold hA' zB
  rw [sB_eq]
  unfold mB
  field_simp


/-- The numerator of `θ′`, cleared: `h z′ − z h′ = x⁴N₂/(q·w·√w)`. -/
theorem theta_num (x : ℝ) :
    hA x * zB' x - zB x * hA' x
      = x ^ 4 * (x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
        / (qA x * (x ^ 4 + 4 * x ^ 2 + 1) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
  have hT : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (sqrt_wA_pos x).ne'
  have hT2 : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ^ 2 = x ^ 4 + 4 * x ^ 2 + 1 :=
    Real.sq_sqrt (wA_pos x).le
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hw : (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (wA_pos x).ne'
  have e1 : x ^ 4 * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4
        + 23 * x ^ 2 + 6) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)
        / (qA x ^ 2 * (x ^ 4 + 4 * x ^ 2 + 1) ^ 2)
      = x ^ 4 * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6 + 36 * x ^ 4
          + 23 * x ^ 2 + 6)
        / (qA x ^ 2 * (x ^ 4 + 4 * x ^ 2 + 1) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (x ^ 4 * (2 * x ^ 12 + 15 * x ^ 10 + 28 * x ^ 8 + 34 * x ^ 6
      + 36 * x ^ 4 + 23 * x ^ 2 + 6) * qA x ^ 2 * (x ^ 4 + 4 * x ^ 2 + 1)) * hT2
  rw [hA_mul_zB', zB_mul_hA', e1]
  field_simp
  unfold qA
  ring

/-- **`θ′ = N₂/(q·√w·(x⁴+4x²+9))`**, with `N₂ = x⁸+6x⁶−6x⁴−22x²−3`.  Explicit,
algebraic, and regular at the origin (`θ′(0) = −1/3`) — unlike the quotient form,
which is `0/0` there. -/
theorem theta_deriv_eq {x : ℝ} (hx : x ≠ 0) :
    (hA x * zB' x - zB x * hA' x) / (hA x ^ 2 + zB x ^ 2)
      = (x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
        / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by
  have hT : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (sqrt_wA_pos x).ne'
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hw : (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (wA_pos x).ne'
  have hd : (x ^ 4 + 4 * x ^ 2 + 9) ≠ 0 := by positivity
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx
  rw [theta_num, hA_sq_add_zB_sq]
  field_simp


/-- **Equation (8), in usable form.**  With `v = √w/q` and `θ′` as above,

    v + θ′ = 2(x⁴+6x²+3) / (√(x⁴+4x²+1)·(x⁴+4x²+9)) ,

which is exactly the second factor of the target integrand.  The content is the
polynomial identity `w(x⁴+4x²+9) + N₂ = 2(x⁴+6x²+3)q` (`KacRice.eq8_numerator`). -/
theorem v_add_theta_deriv {x : ℝ} (hx : x ≠ 0) :
    Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x
        + (hA x * zB' x - zB x * hA' x) / (hA x ^ 2 + zB x ^ 2)
      = 2 * (x ^ 4 + 6 * x ^ 2 + 3)
        / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by
  have hT : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := (sqrt_wA_pos x).ne'
  have hT2 : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) ^ 2 = x ^ 4 + 4 * x ^ 2 + 1 :=
    Real.sq_sqrt (wA_pos x).le
  have hq : qA x ≠ 0 := (qA_pos x).ne'
  have hd : (x ^ 4 + 4 * x ^ 2 + 9) ≠ 0 := by positivity
  rw [theta_deriv_eq hx]
  have hstep : Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x
        + (x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
          / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9))
      = (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1)
            * (x ^ 4 + 4 * x ^ 2 + 9) + (x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3))
        / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by
    field_simp
  rw [hstep, Real.mul_self_sqrt (wA_pos x).le, GaussianCubic.eq8_numerator]
  field_simp


/-! ## Integrability of `Ψ′`

Because `theta_deriv_eq` gives `θ′` in closed form, `owenPsiDeriv hA zB hA' zB'`
agrees off the null set `{0}` with a **continuous** function `psiC`, and `psiC` is
dominated globally by `10·e^{−x²/6}`.  The three ingredients are
`|h′| ≤ 3` (from `P ≤ 3qx²`), `|θ′| ≤ 3` (from `√w ≥ x²+1`), and
`e^{−h²/2} ≤ (6/5) e^{−x²/6}`. -/

@[fun_prop] theorem continuous_hA : Continuous hA := by
  unfold hA
  exact Continuous.div (by fun_prop) (by unfold qA; fun_prop) fun x => (sqrt_qA_pos x).ne'

@[fun_prop] theorem continuous_hA' : Continuous hA' := by
  unfold hA'
  refine Continuous.div (by fun_prop) ?_ fun x => ?_
  · exact (by unfold qA; fun_prop : Continuous qA).mul (by unfold qA; fun_prop)
  · exact (mul_pos (qA_pos x) (sqrt_qA_pos x)).ne'

@[fun_prop] theorem continuous_zB : Continuous zB := by
  have hfun : zB = fun y : ℝ => (y ^ 6 + 2 * y ^ 4 + 3 * y ^ 2) / Real.sqrt (GA y) :=
    funext zB_eq'
  rw [hfun]
  exact Continuous.div (by fun_prop) (by unfold GA; fun_prop)
    fun x => (Real.sqrt_pos.2 (GA_pos x)).ne'

theorem sqrt_qA_ge (x : ℝ) : x ^ 2 ≤ Real.sqrt (qA x) := by
  rw [show x ^ 2 = Real.sqrt ((x ^ 2) ^ 2) from (Real.sqrt_sq (sq_nonneg x)).symm]
  exact Real.sqrt_le_sqrt (by unfold qA; nlinarith [sq_nonneg x])

theorem sqrt_wA_ge (x : ℝ) : x ^ 2 + 1 ≤ Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) := by
  rw [show x ^ 2 + 1 = Real.sqrt ((x ^ 2 + 1) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

/-- `|h′| ≤ 3`. -/
theorem abs_hA'_le (x : ℝ) : |hA' x| ≤ 3 := by
  have hq := qA_pos x
  have hs := sqrt_qA_pos x
  have hnn : 0 ≤ x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x)) := by positivity
  unfold hA'
  rw [abs_of_nonneg hnn, div_le_iff₀ (by positivity)]
  have h1 : x ^ 2 * qA x ≤ Real.sqrt (qA x) * qA x :=
    mul_le_mul_of_nonneg_right (sqrt_qA_ge x) hq.le
  calc x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) ≤ 3 * (x ^ 2 * qA x) := by
        unfold qA; nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3)]
    _ ≤ 3 * (Real.sqrt (qA x) * qA x) := by linarith
    _ = 3 * (qA x * Real.sqrt (qA x)) := by ring

/-- `|θ′| ≤ 3`, from `√w ≥ x²+1`. -/
theorem abs_theta_le (x : ℝ) :
    |(x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
      / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9))| ≤ 3 := by
  have hq := qA_pos x
  have hT := sqrt_wA_pos x
  have hD : (0 : ℝ) < x ^ 4 + 4 * x ^ 2 + 9 := by positivity
  have hden : (0 : ℝ) < qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9) := by
    positivity
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hnum : |x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3|
      ≤ x ^ 8 + 6 * x ^ 6 + 6 * x ^ 4 + 22 * x ^ 2 + 3 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x ^ 4), sq_nonneg (x ^ 3), sq_nonneg x]
    · nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]
  have hstep : x ^ 8 + 6 * x ^ 6 + 6 * x ^ 4 + 22 * x ^ 2 + 3
      ≤ 3 * (qA x * (x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by
    unfold qA; nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3)]
  have hmono : 3 * (qA x * (x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9))
      ≤ 3 * (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by
    have := sqrt_wA_ge x
    nlinarith [hq, hD]
  linarith

/-- `e^{−h²/2} ≤ (6/5)·e^{−x²/6}`. -/
theorem exp_hA_le (x : ℝ) :
    Real.exp (-hA x ^ 2 / 2) ≤ 6 / 5 * Real.exp (-x ^ 2 / 6) := by
  have hpos : (0 : ℝ) < Real.exp (-x ^ 2 / 6) := Real.exp_pos _
  rcases le_or_gt 1 |x| with hx | hx
  · have h := hA_sq_ge hx
    have : Real.exp (-hA x ^ 2 / 2) ≤ Real.exp (-x ^ 2 / 6) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · have h1 : Real.exp (-hA x ^ 2 / 2) ≤ 1 := by
      have hx2 : Real.exp (-hA x ^ 2 / 2) ≤ Real.exp 0 :=
        Real.exp_le_exp.2 (by nlinarith [sq_nonneg (hA x)])
      rwa [Real.exp_zero] at hx2
    have h2 : (5 : ℝ) / 6 ≤ Real.exp (-x ^ 2 / 6) := by
      have := Real.add_one_le_exp (-x ^ 2 / 6)
      have hx2 : x ^ 2 < 1 := by nlinarith [sq_abs x, abs_nonneg x]
      linarith
    linarith


/-- The continuous representative of `Ψ′`, using `θ′`'s closed form. -/
noncomputable def psiC (x : ℝ) : ℝ :=
  φ (hA x) * hA' x * (2 * Φ (zB x) - 1)
    - 1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
      * ((x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
        / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))

theorem continuous_psiC : Continuous psiC := by
  have hw : ∀ x : ℝ, (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := fun x => (wA_pos x).ne'
  have hd : ∀ x : ℝ,
      qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9) ≠ 0 := fun x => by
    have h1 := qA_pos x; have h2 := sqrt_wA_pos x; positivity
  unfold psiC
  refine Continuous.sub (by fun_prop) (Continuous.mul (Continuous.mul continuous_const ?_) ?_)
  · exact Real.continuous_exp.comp
      (((Continuous.div (by fun_prop) (by fun_prop) hw).neg).div_const 2)
  · exact Continuous.div (by fun_prop)
      (Continuous.mul (Continuous.mul (by unfold qA; fun_prop)
        (Real.continuous_sqrt.comp (by fun_prop))) (by fun_prop)) hd

/-- Off the origin, `Ψ′` *is* `psiC`. -/
theorem psiC_eq {x : ℝ} (hx : x ≠ 0) : owenPsiDeriv hA zB hA' zB' x = psiC x := by
  unfold owenPsiDeriv psiC
  rw [theta_deriv_eq hx, hA_sq_add_zB_sq]

theorem abs_psiC_le (x : ℝ) : |psiC x| ≤ 10 * Real.exp (-x ^ 2 / 6) := by
  have hE : (0 : ℝ) < Real.exp (-x ^ 2 / 6) := Real.exp_pos _
  have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hs1 : (1 : ℝ) ≤ Real.sqrt (2 * π) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hexp := exp_hA_le x
  have hφ : φ (hA x) ≤ 6 / 5 * Real.exp (-x ^ 2 / 6) := by
    have h : φ (hA x) ≤ Real.exp (-hA x ^ 2 / 2) := by
      unfold φ
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.exp_pos (-hA x ^ 2 / 2)]
    linarith
  have hz : Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
      ≤ 6 / 5 * Real.exp (-x ^ 2 / 6) := by
    have h1 : Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
        ≤ Real.exp (-hA x ^ 2 / 2) := by
      refine Real.exp_le_exp.2 ?_
      have h := hA_sq_add_zB_sq x
      nlinarith [sq_nonneg (zB x)]
    linarith
  have hab1 : |φ (hA x) * hA' x * (2 * Φ (zB x) - 1)| ≤ 18 / 5 * Real.exp (-x ^ 2 / 6) := by
    have h3 := abs_hA'_le x
    have h2 := abs_two_Φ_sub_one_le (zB x)
    have key : |φ (hA x) * hA' x * (2 * Φ (zB x) - 1)| ≤ φ (hA x) * 3 := by
      rw [abs_mul, abs_mul, abs_of_pos (φ_pos (hA x))]
      have h1 : φ (hA x) * |hA' x| * |2 * Φ (zB x) - 1| ≤ φ (hA x) * 3 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 (φ_pos _).le) h2 (abs_nonneg _)
          (by have := (φ_pos (hA x)).le; positivity)
      linarith
    linarith
  have hab2 : |1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
        * ((x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
          / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))|
      ≤ 18 / 5 * Real.exp (-x ^ 2 / 6) := by
    have hth := abs_theta_le x
    have hinvπ : 1 / π ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hEp := Real.exp_pos
      (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
    have key : |1 / π
          * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
          * ((x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
            / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))|
        ≤ Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2) * 3 := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π),
        abs_of_pos hEp]
      have h1 : 1 / π
            * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
            * |(x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
              / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9))|
          ≤ 1 * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
            * 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hinvπ hEp.le) hth (abs_nonneg _)
          (by positivity)
      linarith
    linarith
  unfold psiC
  calc |φ (hA x) * hA' x * (2 * Φ (zB x) - 1)
        - 1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
          * ((x ^ 8 + 6 * x ^ 6 - 6 * x ^ 4 - 22 * x ^ 2 - 3)
            / (qA x * Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))|
      ≤ _ + _ := abs_sub _ _
    _ ≤ 18 / 5 * Real.exp (-x ^ 2 / 6) + 18 / 5 * Real.exp (-x ^ 2 / 6) := by linarith
    _ ≤ 10 * Real.exp (-x ^ 2 / 6) := by linarith

theorem integrable_psiC : Integrable psiC := by
  have hg : Integrable fun x : ℝ => 10 * Real.exp (-(1 / 6 : ℝ) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul 10
  refine Integrable.mono' hg continuous_psiC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, show -(1 / 6 : ℝ) * x ^ 2 = -x ^ 2 / 6 by ring]
  exact abs_psiC_le x

/-- **`Ψ′` is integrable.**  It agrees with `psiC` off the null set `{0}`. -/
theorem integrable_owenPsiDeriv : Integrable (owenPsiDeriv hA zB hA' zB') := by
  refine integrable_psiC.congr ?_
  have h : {(0 : ℝ)}ᶜ ⊆ {x | psiC x = owenPsiDeriv hA zB hA' zB' x} := by
    intro x hx
    exact (psiC_eq (by simpa using hx)).symm
  refine Filter.eventuallyEq_of_mem (?_ : {(0 : ℝ)}ᶜ ∈ MeasureTheory.ae volume) h
  rw [MeasureTheory.mem_ae_iff, compl_compl]
  exact MeasureTheory.measure_singleton 0


/-! ## The Owen's-`T` cancellation for the monic Gaussian cubic -/

/-- **The Owen's-`T` cancellation, instantiated.**  Every hypothesis of
`integral_owenPsiDeriv_eq_one` is now proved for `h = hA`, `z = zB`:

    ∫_ℝ [ φ(h)h′(2Φ(z)−1) − (1/π)e^{−(h²+z²)/2}·(hz′−zh′)/(h²+z²) ] dx = 1

i.e. `∫_ℝ φ(h)h′(2Φ(z)−1) dx = 1 + (1/π)∫_ℝ e^{−(h²+z²)/2} θ′ dx` — with the `1`
coming entirely from the jump of `Ψ = −2T(h, z/h)` at the origin. -/
theorem cubic_owen_cancellation : ∫ x, owenPsiDeriv hA zB hA' zB' x = 1 :=
  integral_owenPsiDeriv_eq_one hasDerivAt_hA' hasDerivAt_zB'
    (fun _ hx => hA_ne_zero hx) tendsto_owenT_cubic_pos tendsto_owenT_cubic_neg
    tendsto_exp_hA_atTop tendsto_exp_hA_atBot integrable_owenPsiDeriv


/-- `2φ(h)φ(z) = (1/π)·e^{−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1))}`. -/
theorem two_phi_mul_phi (x : ℝ) :
    2 * φ (hA x) * φ (zB x)
      = 1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have he : Real.exp (-hA x ^ 2 / 2) * Real.exp (-zB x ^ 2 / 2)
      = Real.exp (-(hA x ^ 2 + zB x ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hA_sq_add_zB_sq, ← he]
  unfold φ
  field_simp
  linear_combination -hs

/-- **The Kac–Rice integrand splits as target + `Ψ′`.**

    φ(h)·[2vφ(z) + h′(2Φ(z)−1)]
      = (1/π)·e^{−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1))}·2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9))
        + Ψ′(x)

The first summand is **exactly the integrand of the target formula**; the second
integrates to `1` (`cubic_owen_cancellation`).  So `E[N] = 1 + 2p` will give `p`
as `(1/2π)` times the integral of the target integrand over `ℝ`. -/
theorem kacRice_integrand_split {x : ℝ} (hx : x ≠ 0) :
    φ (hA x) * (2 * (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * φ (zB x)
        + hA' x * (2 * Φ (zB x) - 1))
      = 1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
          * (2 * (x ^ 4 + 6 * x ^ 2 + 3)
            / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))
        + owenPsiDeriv hA zB hA' zB' x := by
  have hpp := two_phi_mul_phi x
  rw [← v_add_theta_deriv hx]
  unfold owenPsiDeriv
  rw [hA_sq_add_zB_sq]
  linear_combination (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * hpp

end NonmonicCubic.Gaussian
