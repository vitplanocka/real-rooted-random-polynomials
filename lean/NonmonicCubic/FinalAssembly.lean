/-
# Assembling `E[N]`

Every mathematical ingredient of Problem A is proved; this file does the
measure-theoretic bookkeeping that joins them.

Step 1 here: the `(a,b)`-integral of the Kac–Rice integrand at fixed `x`, as an
integral over `ℝ × ℝ` rather than iterated — this is `Assembly.inner_lintegral_eq`
plus `lintegral_prod`.
-/
import NonmonicCubic.CubicLimits
import NonmonicCubic.KacRiceIntegral
import NonmonicCubic.BandRoots

namespace NonmonicCubic.Gaussian

open MeasureTheory Real Filter Set
open scoped ENNReal
open NonmonicCubic.AreaFormula NonmonicCubic.KacRiceIntegral NonmonicCubic.GaussianCubic

/-- The Kac–Rice integrand of the monic Gaussian cubic, as a function of `x`. -/
noncomputable def kacRiceReal (x : ℝ) : ℝ :=
  φ (hA x) * (2 * (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) * φ (zB x)
    + x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x)) * (2 * Φ (zB x) - 1))

theorem continuous_kacRiceSection (x : ℝ) :
    Continuous fun p : ℝ × ℝ => φ p.1 * φ p.2 * |dcub p.1 p.2 x| * φ (cub p.1 p.2 x) := by
  unfold cub dcub
  fun_prop

/-- **The `(a,b)`-integral at fixed `x`.**  `Assembly.inner_lintegral_eq` stated
over `ℝ × ℝ` instead of iterated. -/
theorem lintegral_ab_kacRice (x : ℝ) :
    ∫⁻ p : ℝ × ℝ, kacRice p.1 p.2 x = ENNReal.ofReal (kacRiceReal x) := by
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => kacRice p.1 p.2 x)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (ENNReal.measurable_ofReal.comp (continuous_kacRiceSection x).measurable).aemeasurable
  rw [Measure.volume_eq_prod, MeasureTheory.lintegral_prod _ hmeas]
  exact inner_lintegral_eq x


/-- **Step 2: the Tonelli swap applied.**  `E[N]`, written as `∫⁻ over (a,b)` of
the `x`-integral, equals the `x`-integral of the Kac–Rice integrand. -/
theorem lintegral_kacRice_total :
    ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, kacRice p.1 p.2 x
      = ∫⁻ x : ℝ, ENNReal.ofReal (kacRiceReal x) := by
  rw [lintegral_kacRice_swap]
  exact lintegral_congr fun x => lintegral_ab_kacRice x

/-- `z = h′/v`: the ratio form of `z`, needed to see the Kac–Rice bracket as a
folded-normal mean. -/
theorem zB_eq_div (x : ℝ) :
    zB x = (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x)))
      / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) := by
  have hq : (0 : ℝ) < qA x := qA_pos x
  have hs : (0 : ℝ) < Real.sqrt (qA x) := sqrt_qA_pos x
  have hT : (0 : ℝ) < Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) := sqrt_wA_pos x
  rw [zB_eq]
  field_simp

/-- **The Kac–Rice integrand is nonnegative** — it is a folded-normal mean,
`∫ |h′ + v s| φ(s) ds`, times `φ(h)`. -/
theorem kacRiceReal_nonneg (x : ℝ) : 0 ≤ kacRiceReal x := by
  have hv : (0 : ℝ) < Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x :=
    div_pos (sqrt_wA_pos x) (qA_pos x)
  have hbr := integral_abs_scaled (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x)))
    (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x) hv
  have hnn : 0 ≤ ∫ s : ℝ, |x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))
      + Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) / qA x * s| * φ s :=
    integral_nonneg fun s => mul_nonneg (abs_nonneg _) (φ_pos s).le
  rw [hbr, ← zB_eq_div] at hnn
  unfold kacRiceReal
  exact mul_nonneg (φ_pos _).le hnn


/-! ## The target integrand -/

/-- The integrand of the boxed formula. -/
noncomputable def targetIntegrand (x : ℝ) : ℝ :=
  1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
    * (2 * (x ^ 4 + 6 * x ^ 2 + 3)
      / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))

theorem continuous_targetIntegrand : Continuous targetIntegrand := by
  have hw : ∀ x : ℝ, (x ^ 4 + 4 * x ^ 2 + 1) ≠ 0 := fun x => (wA_pos x).ne'
  have hd : ∀ x : ℝ, Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9) ≠ 0 :=
    fun x => by have := sqrt_wA_pos x; positivity
  unfold targetIntegrand
  refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
  · exact Real.continuous_exp.comp
      (((Continuous.div (by fun_prop) (by fun_prop) hw).neg).div_const 2)
  · exact Continuous.div (by fun_prop)
      (Continuous.mul (Real.continuous_sqrt.comp (by fun_prop)) (by fun_prop)) hd

/-- The target integrand is even. -/
theorem targetIntegrand_neg (x : ℝ) : targetIntegrand (-x) = targetIntegrand x := by
  unfold targetIntegrand
  norm_num

theorem targetIntegrand_nonneg (x : ℝ) : 0 ≤ targetIntegrand x := by
  have := sqrt_wA_pos x
  unfold targetIntegrand
  positivity

theorem abs_targetIntegrand_le (x : ℝ) : |targetIntegrand x| ≤ 10 * Real.exp (-x ^ 2 / 6) := by
  have hE : (0 : ℝ) < Real.exp (-x ^ 2 / 6) := Real.exp_pos _
  have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hinvπ : 1 / π ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hT := sqrt_wA_pos x
  have hD : (0 : ℝ) < x ^ 4 + 4 * x ^ 2 + 9 := by positivity
  -- the exponential factor
  have hz : Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
      ≤ 6 / 5 * Real.exp (-x ^ 2 / 6) := by
    have h1 : Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
        ≤ Real.exp (-hA x ^ 2 / 2) := by
      refine Real.exp_le_exp.2 ?_
      have h := hA_sq_add_zB_sq x
      nlinarith [sq_nonneg (zB x)]
    linarith [exp_hA_le x]
  -- the algebraic factor
  have hamp : 2 * (x ^ 4 + 6 * x ^ 2 + 3)
      / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hs := sqrt_wA_ge x
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), hD]
  have hamp0 : 0 ≤ 2 * (x ^ 4 + 6 * x ^ 2 + 3)
      / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)) := by positivity
  rw [abs_of_nonneg (targetIntegrand_nonneg x)]
  unfold targetIntegrand
  have hEp := Real.exp_pos (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
  calc 1 / π * Real.exp (-(x ^ 4 * (x ^ 4 + 4 * x ^ 2 + 9) / (x ^ 4 + 4 * x ^ 2 + 1)) / 2)
        * (2 * (x ^ 4 + 6 * x ^ 2 + 3)
          / (Real.sqrt (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 4 + 4 * x ^ 2 + 9)))
      ≤ 1 * (6 / 5 * Real.exp (-x ^ 2 / 6)) * 1 := by
        apply mul_le_mul (mul_le_mul hinvπ hz hEp.le (by norm_num)) hamp hamp0 (by positivity)
    _ ≤ 10 * Real.exp (-x ^ 2 / 6) := by linarith

theorem integrable_targetIntegrand : Integrable targetIntegrand := by
  have hg : Integrable fun x : ℝ => 10 * Real.exp (-(1 / 6 : ℝ) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul 10
  refine Integrable.mono' hg continuous_targetIntegrand.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, show -(1 / 6 : ℝ) * x ^ 2 = -x ^ 2 / 6 by ring]
  exact abs_targetIntegrand_le x


/-! ## The Kac–Rice integral splits as `target + 1` -/

theorem kacRiceReal_ae_eq :
    kacRiceReal =ᵐ[volume] fun x => targetIntegrand x + owenPsiDeriv hA zB hA' zB' x := by
  have h : {(0 : ℝ)}ᶜ ⊆ {x | kacRiceReal x = targetIntegrand x + owenPsiDeriv hA zB hA' zB' x} := by
    intro x hx
    exact kacRice_integrand_split (by simpa using hx)
  refine Filter.eventuallyEq_of_mem (?_ : {(0 : ℝ)}ᶜ ∈ MeasureTheory.ae volume) h
  rw [MeasureTheory.mem_ae_iff, compl_compl]
  exact MeasureTheory.measure_singleton 0

theorem integrable_kacRiceReal : Integrable kacRiceReal :=
  (integrable_targetIntegrand.add integrable_owenPsiDeriv).congr kacRiceReal_ae_eq.symm

/-- **`∫ Kac–Rice integrand = ∫ target + 1`.**  The `+1` is the Owen's-`T`
cancellation. -/
theorem integral_kacRiceReal :
    ∫ x, kacRiceReal x = (∫ x, targetIntegrand x) + 1 := by
  rw [integral_congr_ae kacRiceReal_ae_eq,
    integral_add integrable_targetIntegrand integrable_owenPsiDeriv,
    cubic_owen_cancellation]

/-! ## Evenness -/

theorem integral_targetIntegrand_eq_two_mul :
    ∫ x, targetIntegrand x = 2 * ∫ x in Ioi (0 : ℝ), targetIntegrand x := by
  have hIic : IntegrableOn targetIntegrand (Iic 0) := integrable_targetIntegrand.integrableOn
  have hIoi : IntegrableOn targetIntegrand (Ioi 0) := integrable_targetIntegrand.integrableOn
  have h1 : (∫ x in Iic (0 : ℝ), targetIntegrand x) + ∫ x in Ioi (0 : ℝ), targetIntegrand x
      = ∫ x, targetIntegrand x := intervalIntegral.integral_Iic_add_Ioi hIic hIoi
  have h2 : (∫ x in Iic (0 : ℝ), targetIntegrand x) = ∫ x in Ioi (0 : ℝ), targetIntegrand x := by
    simpa [targetIntegrand_neg] using integral_comp_neg_Iic (0 : ℝ) targetIntegrand
  linarith

/-- **The Kac–Rice integral in the final shape.**

    ∫_ℝ φ(h)[2vφ(z) + h′(2Φ(z)−1)] dx  =  1 + 2·∫₀^∞ (target integrand) ,

so once the left side is identified with `E[N]` and `E[N] = 1 + 2p`, the boxed
formula `p = (1/π)∫₀^∞ e^{−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1))}·2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9)) dx`
follows. -/
theorem integral_kacRiceReal_eq :
    ∫ x, kacRiceReal x = 1 + 2 * ∫ x in Ioi (0 : ℝ), targetIntegrand x := by
  rw [integral_kacRiceReal, integral_targetIntegrand_eq_two_mul]
  ring


/-- **The whole Kac–Rice quantity, evaluated.**

    ∫⁻ (a,b) ∫⁻ x  φ(a)φ(b)·|f′(x)|·φ(f(x)−c-part)
      = 1 + 2·∫₀^∞ e^{−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1))}·2(x⁴+6x²+3)/(π√(x⁴+4x²+1)(x⁴+4x²+9)) dx

The left-hand side is `E[N]` once the counting is put in
(`AreaFormula.lintegral_cub` with `BandRoots.three_distinct_iff_mem_band`); the
right-hand side is `1 + 2p` with `p` the boxed formula. -/
theorem lintegral_kacRice_eq_target :
    ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, kacRice p.1 p.2 x
      = ENNReal.ofReal (1 + 2 * ∫ x in Ioi (0 : ℝ), targetIntegrand x) := by
  rw [lintegral_kacRice_total, ← integral_kacRiceReal_eq,
    ← ofReal_integral_eq_lintegral_ofReal integrable_kacRiceReal
      (Filter.Eventually.of_forall kacRiceReal_nonneg)]


/-! ## `E[N] = 1 + 2p`: the counting side

`AreaFormula.lintegral_cub_roots` states the area formula with the
three-real-roots set in place of the band, so the fibre becomes
`φ(a)φ(b)·(1 + 2·P(three roots | a,b))` literally. -/

/-- The Gaussian measure of the three-real-roots region, as an iterated
`lintegral`. -/
noncomputable def rootProb : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (φ p.1 * φ p.2)
    * ∫⁻ y in {y : ℝ | HasThreeDistinctRealRoots 1 p.1 p.2 (-y)}, ENNReal.ofReal (φ y)

/-- The fibre, by root count. -/
theorem lintegral_x_kacRice_roots (a b : ℝ) :
    ∫⁻ x : ℝ, kacRice a b x
      = ENNReal.ofReal (φ a * φ b)
        * (1 + 2 * ∫⁻ y in {y : ℝ | HasThreeDistinctRealRoots 1 a b (-y)},
            ENNReal.ofReal (φ y)) := by
  have hpull : ∀ x : ℝ, kacRice a b x
      = ENNReal.ofReal (φ a * φ b)
        * (ENNReal.ofReal |dcub a b x| * ENNReal.ofReal (φ (cub a b x))) := by
    intro x
    unfold kacRice
    rw [← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (mul_pos (φ_pos a) (φ_pos b)).le]
    ring_nf
  simp_rw [hpull]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cub_roots a b fun y => ENNReal.ofReal (φ y), lintegral_ofReal_φ]

theorem lintegral_phi_prod : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (φ p.1 * φ p.2) = 1 := by
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1 * φ p.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous
      fun p : ℝ × ℝ => φ p.1 * φ p.2).measurable).aemeasurable
  rw [Measure.volume_eq_prod, MeasureTheory.lintegral_prod _ hmeas]
  have hstep : ∀ a : ℝ, (∫⁻ b : ℝ, ENNReal.ofReal (φ a * φ b))
      = ENNReal.ofReal (φ a) := by
    intro a
    have h : ∀ b : ℝ, ENNReal.ofReal (φ a * φ b)
        = ENNReal.ofReal (φ a) * ENNReal.ofReal (φ b) :=
      fun b => ENNReal.ofReal_mul (φ_pos a).le
    simp_rw [h]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_φ, mul_one]
  simp_rw [hstep]
  exact lintegral_ofReal_φ

/-- **`E[N] = 1 + 2p`.** -/
theorem lintegral_kacRice_eq_one_add : ∫⁻ p : ℝ × ℝ, ∫⁻ x : ℝ, kacRice p.1 p.2 x
      = 1 + 2 * rootProb := by
  have hpt : ∀ p : ℝ × ℝ, (∫⁻ x : ℝ, kacRice p.1 p.2 x)
      = ENNReal.ofReal (φ p.1 * φ p.2)
        + 2 * (ENNReal.ofReal (φ p.1 * φ p.2)
          * ∫⁻ y in {y : ℝ | HasThreeDistinctRealRoots 1 p.1 p.2 (-y)},
            ENNReal.ofReal (φ y)) := by
    intro p
    rw [lintegral_x_kacRice_roots p.1 p.2, mul_add, mul_one]
    ring
  have hm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1 * φ p.2))
      (volume : Measure (ℝ × ℝ)) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous
      fun p : ℝ × ℝ => φ p.1 * φ p.2).measurable).aemeasurable
  simp_rw [hpt]
  rw [lintegral_add_left' hm, lintegral_phi_prod,
    lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  rfl


/-! ## The result -/

/-- **Problem A, closed.**

    P(x³ + a x² + b x + c has three distinct real roots),  (a,b,c) i.i.d. N(0,1)
      = (1/π) ∫₀^∞ exp(−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1)))
                   · 2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9)) dx

The left-hand side is `rootProb`, the Gaussian measure of the three-real-roots
region; the right-hand side is `∫₀^∞ targetIntegrand`.  Everything in between —
the area formula, the Tonelli swap, the folded-normal mean, the affine change of
variables, and the Owen's-`T` cancellation — is proved, with no appeal to
Rice's formula, the coarea formula, or any theory of stochastic processes. -/
theorem rootProb_eq :
    rootProb = ENNReal.ofReal (∫ x in Ioi (0 : ℝ), targetIntegrand x) := by
  have hT : 0 ≤ ∫ x in Ioi (0 : ℝ), targetIntegrand x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => targetIntegrand_nonneg x
  have h := lintegral_kacRice_eq_one_add.symm.trans lintegral_kacRice_eq_target
  rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_one,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have h2 : (2 : ℝ≥0∞) * rootProb
      = ENNReal.ofReal 2 * ENNReal.ofReal (∫ x in Ioi (0 : ℝ), targetIntegrand x) :=
    WithTop.add_left_cancel ENNReal.one_ne_top h
  rw [ENNReal.ofReal_ofNat] at h2
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h2

end NonmonicCubic.Gaussian
