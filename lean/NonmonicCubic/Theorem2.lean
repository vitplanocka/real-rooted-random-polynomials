/-
# Theorem 2

> Let `(a,b,c)` be i.i.d. uniform on `[0,1]`.  Then
> `P( x³ + a x² + b x + c has three real roots ) = 1/2880`.

Same discriminant and same band as Theorem 1, but on the unit cube the band *is*
clipped — from below, by the window's floor `c = 0`, and exactly on the region
`b ≤ a²/4` (`reference/THEOREMS.md`, "Proof of Theorem 2", step 3).  The top is
never clipped: `cHi ≤ 1/9` there (`cHi_le_one_unit`).

So the slice area splits at `b = a²/4`:

    ∫₀^{a²/4} cHi db  +  ∫_{a²/4}^{a²/3} (4/27)(a²-3b)^{3/2} db
      = 19a⁵/12960 + a⁵/1620 = a⁵/480,

all fractional powers cancelling (the "small miracle" of Theorem 2), and
`∫₀¹ a⁵/480 da = 1/2880`.

One measure-theoretic wrinkle absent from Theorem 1: because the floor really
does clip, the slice of the cube and the open region between the clipped edges
differ on `{c = 0}` — a null set — rather than being equal.  That is handled by
`slice2_ae_eq` rather than by a set equality.
-/
import NonmonicCubic.Theorem1

namespace NonmonicCubic

open Real Set MeasureTheory intervalIntegral

/-- The real-rooted region of the unit cube `[0,1]³`. -/
def T2Set : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (0 : ℝ) 1 ∧
    0 < Δ₃ p.1 p.2.1 p.2.2}

/-- The band's lower edge after clipping by the window floor `c = 0`. -/
noncomputable def cLo0 (a b : ℝ) : ℝ := max (cLo a b) 0

theorem continuous_cLo0 (a : ℝ) : Continuous (cLo0 a) :=
  (continuous_cLo a).max continuous_const

theorem measurableSet_T2Set : MeasurableSet T2Set := by
  have h : T2Set = ((Prod.fst ⁻¹' Icc (0 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' Icc (0 : ℝ) 1)
      ∩ ((fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' Icc (0 : ℝ) 1))
      ∩ {p : ℝ × ℝ × ℝ | 0 < Δ₃ p.1 p.2.1 p.2.2} := by
    ext p; simp only [T2Set, mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
  rw [h]
  exact (((measurable_fst measurableSet_Icc).inter
      ((measurable_fst.comp measurable_snd) measurableSet_Icc)).inter
      ((measurable_snd.comp measurable_snd) measurableSet_Icc)).inter
    (measurableSet_lt measurable_const continuous_Δ₃.measurable)

/-- The clipped region is contained in the slice. -/
theorem region_subset_slice2 {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3)) ⊆ Prod.mk a ⁻¹' T2Set := by
  obtain ⟨ha0, ha1⟩ := ha
  rintro ⟨b, c⟩ ⟨⟨hb0, hb2⟩, hc1, hc2⟩
  have hnn : 0 ≤ a ^ 2 - 3 * b := by linarith
  have hcHi1 : cHi a b ≤ 1 := cHi_le_one_unit ha0 ha1 hb0 (by linarith)
  have hc0 : 0 ≤ c := le_trans (le_max_right (cLo a b) 0) hc1.le
  refine ⟨⟨ha0, ha1⟩, ⟨hb0, by nlinarith⟩, ⟨hc0, by linarith⟩, ?_⟩
  exact (Δ₃_pos_iff hnn c).2 ⟨lt_of_le_of_lt (le_max_left _ _) hc1, hc2⟩

/-- Conversely the slice sits inside the clipped region together with the null
set `{c = 0}`: the only points of the cube with `Δ₃ > 0` that the open region
misses are those sitting exactly on the clipping floor. -/
theorem slice2_sdiff_subset {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (Prod.mk a ⁻¹' T2Set) \ regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3))
      ⊆ {q : ℝ × ℝ | q.2 = 0} := by
  obtain ⟨ha0, ha1⟩ := ha
  rintro ⟨b, c⟩ ⟨⟨-, ⟨hb0, -⟩, ⟨hc0, -⟩, hΔ⟩, hout⟩
  by_contra hc
  refine hout ?_
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  have hnn : 0 ≤ a ^ 2 - 3 * b := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hΔ (not_lt.2 (Δ₃_neg_of_lt hlt c).le)
  have hband := (Δ₃_pos_iff hnn c).1 hΔ
  have hp : 0 < p32 (a ^ 2 - 3 * b) := by
    have h1 := cHi_sub_cLo a b
    have h2 : cLo a b < cHi a b := lt_trans hband.1 hband.2
    linarith
  have hb2 : b < a ^ 2 / 3 := by
    rcases lt_or_eq_of_le hnn with h | h
    · linarith
    · exfalso; unfold p32 at hp; rw [← h] at hp; simp at hp
  exact ⟨⟨hb0, hb2⟩, max_lt hband.1 hcpos, hband.2⟩

theorem volume_snd_eq_zero : (volume : Measure (ℝ × ℝ)) {q : ℝ × ℝ | q.2 = 0} = 0 := by
  have h : {q : ℝ × ℝ | q.2 = 0} = (univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    ext q; simp
  rw [h, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod]
  simp

theorem volume_slice2 {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    volume (Prod.mk a ⁻¹' T2Set)
      = volume (regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3))) := by
  refine le_antisymm ?_ (measure_mono (region_subset_slice2 ha))
  calc volume (Prod.mk a ⁻¹' T2Set)
      ≤ volume (regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3))
          ∪ {q : ℝ × ℝ | q.2 = 0}) := by
        refine measure_mono ?_
        intro q hq
        by_cases h : q ∈ regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3))
        · exact Or.inl h
        · exact Or.inr (slice2_sdiff_subset ha ⟨hq, h⟩)
    _ ≤ volume (regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3)))
          + volume {q : ℝ × ℝ | q.2 = 0} := measure_union_le _ _
    _ = volume (regionBetween (cLo0 a) (cHi a) (Ico 0 (a ^ 2 / 3))) := by
        rw [volume_snd_eq_zero, add_zero]

/-! ## The slice area is `a⁵/480` -/

/-- **The "small miracle" of Theorem 2**: all fractional powers cancel and the
clipped slice area is the polynomial `a⁵/480`. -/
theorem slice2_area {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∫ b in Ico 0 (a ^ 2 / 3), (cHi a - cLo0 a) b = a ^ 5 / 480 := by
  obtain ⟨ha0, ha1⟩ := ha
  have h4 : (0 : ℝ) ≤ a ^ 2 / 4 := by positivity
  have h43 : a ^ 2 / 4 ≤ a ^ 2 / 3 := by nlinarith [sq_nonneg a]
  have h03 : (0 : ℝ) ≤ a ^ 2 / 3 := by positivity
  have hcont : Continuous fun b => (cHi a - cLo0 a) b :=
    (continuous_cHi a).sub (continuous_cLo0 a)
  rw [integral_Ico_eq_integral_Ioc, ← integral_of_le h03,
    ← integral_add_adjacent_intervals (b := a ^ 2 / 4)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  -- lower piece: the floor clips, so the integrand is just `cHi`
  have hlow : ∫ b in (0 : ℝ)..(a ^ 2 / 4), (cHi a - cLo0 a) b
      = ∫ b in (0 : ℝ)..(a ^ 2 / 4), cHi a b := by
    refine integral_congr fun b hb => ?_
    rw [uIcc_of_le h4, mem_Icc] at hb
    have : cLo0 a b = 0 := max_eq_right (cLo_nonpos hb.1 (by linarith [hb.2]))
    simp [this]
  -- upper piece: no clipping, so the integrand is the full band width
  have hhigh : ∫ b in (a ^ 2 / 4)..(a ^ 2 / 3), (cHi a - cLo0 a) b
      = ∫ b in (a ^ 2 / 4)..(a ^ 2 / 3), 4 / 27 * p32 (a ^ 2 - 3 * b) := by
    refine integral_congr fun b hb => ?_
    rw [uIcc_of_le h43, mem_Icc] at hb
    have hb0 : cLo0 a b = cLo a b :=
      max_eq_left (cLo_nonneg ha0 (by linarith [hb.1]) (by linarith [hb.2]))
    simp only [Pi.sub_apply, hb0]
    exact cHi_sub_cLo a b
  rw [hlow, hhigh, integral_cHi_gen h4 h43, integral_band_width_gen h43 le_rfl]
  -- evaluate the three `p52` values, using `a ≥ 0`
  rw [show a ^ 2 - 3 * (a ^ 2 / 4) = (a / 2) ^ 2 by ring,
    show a ^ 2 - 3 * (0 : ℝ) = a ^ 2 by ring,
    show a ^ 2 - 3 * (a ^ 2 / 3) = 0 by ring,
    p52_eq_sq_mul (by linarith : (0 : ℝ) ≤ a / 2), p52_eq_sq_mul ha0]
  simp only [p52_zero]
  ring

/-! ## Assembly -/

theorem volume_T2Set : volume T2Set = ENNReal.ofReal (1 / 2880) := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply measurableSet_T2Set]
  have hfun : (fun a => (volume : Measure (ℝ × ℝ)) (Prod.mk a ⁻¹' T2Set))
      = (Icc (0 : ℝ) 1).indicator (fun a => ENNReal.ofReal (a ^ 5 / 480)) := by
    funext a
    by_cases ha : a ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha, volume_slice2 ha,
        show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        volume_regionBetween_eq_integral
          ((continuous_cLo0 a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
          ((continuous_cHi a).continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
          measurableSet_Ico ?_, slice2_area ha]
      intro b hb
      have hnn : 0 ≤ a ^ 2 - 3 * b := by have := hb.2; linarith
      exact max_le (cLo_le_cHi a b hnn) (cHi_nonneg ha.1 hb.1 (by linarith))
    · rw [Set.indicator_of_notMem ha]
      have hempty : Prod.mk a ⁻¹' T2Set = ∅ := by
        ext ⟨b, c⟩
        simp only [mem_preimage, T2Set, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h ha
      rw [hempty, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Icc]
  have hcont : Continuous fun a : ℝ => a ^ 5 / 480 := (continuous_pow 5).div_const _
  have hint : IntegrableOn (fun a : ℝ => a ^ 5 / 480) (Icc (0 : ℝ) 1) :=
    hcont.continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun a : ℝ => a ^ 5 / 480 := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun a ha => by
      simp only [Pi.zero_apply]
      have : 0 ≤ a := ha.1
      positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => y ^ 6 / 2880)
    (fun x _ => by
      have h : HasDerivAt (fun y : ℝ => y ^ 6 / 2880) (6 * x ^ 5 / 2880) x := by
        simpa using ((hasDerivAt_id x).fun_pow 6).div_const 2880
      exact h.congr_deriv (by ring))
    (hcont.intervalIntegrable _ _)]
  norm_num

/-- **Theorem 2**: the volume of `{Δ₃ > 0}` inside `[0,1]³` is `1/2880`, and
since the unit cube has volume `1` that is also the probability. -/
theorem theorem2 :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2.2 ∈ Icc (0 : ℝ) 1 ∧ 0 < Δ₃ p.1 p.2.1 p.2.2}
      = ENNReal.ofReal (1 / 2880) := volume_T2Set

/-- The volume of the unit cube `[0,1]³` is `1`. -/
theorem volume_cube_unit :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_Icc]
  norm_num

/-- **Theorem 2, probability form.** -/
theorem theorem2_probability :
    (volume T2Set).toReal
      / (volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).toReal
      = 1 / 2880 := by
  rw [volume_T2Set, volume_cube_unit, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

end NonmonicCubic
