/-
# The Owen's-`T` cancellation: `∫_ℝ Ψ′ = 1`

`Ψ(x) = −2 T(h x, z x / h x)` has, away from `h = 0`,

    Ψ′ = φ(h) h′ (2Φ(z) − 1) − (1/π) e^{−(h²+z²)/2} · (h z′ − z h′)/(h² + z²)

(`OwenChain.hasDerivAt_owenPsi`).  `Ψ` is *not* continuous at `x = 0`: it jumps
by `−1` there, because `h(0) = 0` sends `z/h → ±∞` and `T(0,±∞) = ±1/4`.  So the
fundamental theorem of calculus is applied on the two half-lines separately, to
the two functions obtained from `Ψ` by filling in its one-sided limit at the
origin.  The two boundary terms are `1/2` each, giving

    ∫_ℝ Ψ′ = 1 ,

i.e. `∫_ℝ φ(h)h′(2Φ(z)−1) dx = 1 + (1/π)∫_ℝ e^{−(h²+z²)/2} θ′ dx` — the Owen's-`T`
cancellation, with the `1` of `E[N] = 1 + 2p` produced by the jump.

Everything here is stated for an abstract pair `(h, z)` satisfying the boundary
hypotheses, so it is independent of the particular cubic.
-/
import NonmonicCubic.OwenChain

namespace NonmonicCubic.Gaussian

open MeasureTheory Real Filter Set intervalIntegral

/-- The integrand `Ψ′`. -/
noncomputable def owenPsiDeriv (h z h' z' : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ (h x) * h' x * (2 * Φ (z x) - 1)
    - 1 / π * Real.exp (-(h x ^ 2 + z x ^ 2) / 2)
      * ((h x * z' x - z x * h' x) / (h x ^ 2 + z x ^ 2))

/-- `Ψ` itself. -/
noncomputable def owenPsi (h z : ℝ → ℝ) (x : ℝ) : ℝ := -2 * owenT (h x) (z x / h x)

/-- `Ψ` completed at the origin by its right limit `−1/2`. -/
noncomputable def owenPsiR (h z : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then -(1 / 2) else owenPsi h z x

/-- `Ψ` completed at the origin by its left limit `1/2`. -/
noncomputable def owenPsiL (h z : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 / 2 else owenPsi h z x

variable {h z h' z' : ℝ → ℝ}

theorem owenPsiR_zero : owenPsiR h z 0 = -(1 / 2) := by simp [owenPsiR]

theorem owenPsiL_zero : owenPsiL h z 0 = 1 / 2 := by simp [owenPsiL]

theorem owenPsiR_eventuallyEq_pos {x : ℝ} (hx : 0 < x) :
    owenPsiR h z =ᶠ[nhds x] owenPsi h z := by
  filter_upwards [eventually_gt_nhds hx] with y hy
  simp [owenPsiR, not_le.2 hy]

theorem owenPsiL_eventuallyEq_neg {x : ℝ} (hx : x < 0) :
    owenPsiL h z =ᶠ[nhds x] owenPsi h z := by
  filter_upwards [eventually_lt_nhds hx] with y hy
  simp [owenPsiL, not_le.2 hy]

/-- `Ψ′` really is the derivative of `Ψ`, off the origin. -/
theorem hasDerivAt_owenPsi' (hh : ∀ x, HasDerivAt h (h' x) x) (hz : ∀ x, HasDerivAt z (z' x) x)
    {x : ℝ} (hne : h x ≠ 0) :
    HasDerivAt (owenPsi h z) (owenPsiDeriv h z h' z' x) x :=
  hasDerivAt_owenPsi (hh x) (hz x) hne

/-! ## The two half-line integrals -/

theorem integral_Ioi_owenPsiDeriv
    (hh : ∀ x, HasDerivAt h (h' x) x) (hz : ∀ x, HasDerivAt z (z' x) x)
    (hne : ∀ x : ℝ, x ≠ 0 → h x ≠ 0)
    (hlim : Tendsto (fun x => owenT (h x) (z x / h x)) (nhdsWithin 0 (Ioi 0)) (nhds (1 / 4)))
    (hinf : Tendsto (fun x => Real.exp (-(h x) ^ 2 / 2)) atTop (nhds 0))
    (hint : IntegrableOn (owenPsiDeriv h z h' z') (Ioi 0)) :
    ∫ x in Ioi (0 : ℝ), owenPsiDeriv h z h' z' x = 1 / 2 := by
  have hcont : ContinuousWithinAt (owenPsiR h z) (Ici 0) 0 := by
    rw [ContinuousWithinAt, ← Set.Ioi_insert, nhdsWithin_insert, Filter.tendsto_sup]
    refine ⟨tendsto_pure_nhds _ _, ?_⟩
    rw [owenPsiR_zero]
    have hEq : owenPsiR h z =ᶠ[nhdsWithin 0 (Ioi 0)] owenPsi h z := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [owenPsiR, not_le.2 (show (0 : ℝ) < y from hy)]
    refine Filter.Tendsto.congr' hEq.symm ?_
    have h2 := hlim.const_mul (-2 : ℝ)
    rw [show (-2 : ℝ) * (1 / 4) = -(1 / 2) by norm_num] at h2
    exact h2
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (owenPsiR h z) (owenPsiDeriv h z h' z' x) x := by
    intro x hx
    exact (hasDerivAt_owenPsi' hh hz (hne x (ne_of_gt hx))).congr_of_eventuallyEq
      (owenPsiR_eventuallyEq_pos hx)
  have htop : Tendsto (owenPsiR h z) atTop (nhds 0) := by
    have hEq : owenPsiR h z =ᶠ[atTop] owenPsi h z := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      simp [owenPsiR, not_le.2 hy]
    refine Filter.Tendsto.congr' hEq.symm ?_
    have h2 := (tendsto_owenT_zero_of_exp (a := fun x => z x / h x) hinf).const_mul (-2 : ℝ)
    rw [show (-2 : ℝ) * 0 = 0 by norm_num] at h2
    exact h2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [owenPsiR_zero] at h
  rw [h]; ring

theorem integral_Iic_owenPsiDeriv
    (hh : ∀ x, HasDerivAt h (h' x) x) (hz : ∀ x, HasDerivAt z (z' x) x)
    (hne : ∀ x : ℝ, x ≠ 0 → h x ≠ 0)
    (hlim : Tendsto (fun x => owenT (h x) (z x / h x)) (nhdsWithin 0 (Iio 0))
      (nhds (-(1 / 4))))
    (hinf : Tendsto (fun x => Real.exp (-(h x) ^ 2 / 2)) atBot (nhds 0))
    (hint : IntegrableOn (owenPsiDeriv h z h' z') (Iic 0)) :
    ∫ x in Iic (0 : ℝ), owenPsiDeriv h z h' z' x = 1 / 2 := by
  have hcont : ContinuousWithinAt (owenPsiL h z) (Iic 0) 0 := by
    rw [ContinuousWithinAt, ← Set.Iio_insert, nhdsWithin_insert, Filter.tendsto_sup]
    refine ⟨tendsto_pure_nhds _ _, ?_⟩
    rw [owenPsiL_zero]
    have hEq : owenPsiL h z =ᶠ[nhdsWithin 0 (Iio 0)] owenPsi h z := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [owenPsiL, not_le.2 (show y < (0 : ℝ) from hy)]
    refine Filter.Tendsto.congr' hEq.symm ?_
    have h2 := hlim.const_mul (-2 : ℝ)
    rw [show (-2 : ℝ) * -(1 / 4) = 1 / 2 by norm_num] at h2
    exact h2
  have hderiv : ∀ x ∈ Iio (0 : ℝ), HasDerivAt (owenPsiL h z) (owenPsiDeriv h z h' z' x) x := by
    intro x hx
    exact (hasDerivAt_owenPsi' hh hz (hne x (ne_of_lt hx))).congr_of_eventuallyEq
      (owenPsiL_eventuallyEq_neg hx)
  have hbot : Tendsto (owenPsiL h z) atBot (nhds 0) := by
    have hEq : owenPsiL h z =ᶠ[atBot] owenPsi h z := by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
      simp [owenPsiL, not_le.2 hy]
    refine Filter.Tendsto.congr' hEq.symm ?_
    have h2 := (tendsto_owenT_zero_of_exp (a := fun x => z x / h x) hinf).const_mul (-2 : ℝ)
    rw [show (-2 : ℝ) * 0 = 0 by norm_num] at h2
    exact h2
  have h := integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv hint hbot
  rw [owenPsiL_zero] at h
  rw [h]; ring

/-- **The Owen's-`T` cancellation.**  `∫_ℝ Ψ′ = 1`: the two half-lines contribute
`1/2` each, the boundary terms at `±∞` vanishing and the jump of `Ψ` at the origin
supplying the whole of it. -/
theorem integral_owenPsiDeriv_eq_one
    (hh : ∀ x, HasDerivAt h (h' x) x) (hz : ∀ x, HasDerivAt z (z' x) x)
    (hne : ∀ x : ℝ, x ≠ 0 → h x ≠ 0)
    (hposlim : Tendsto (fun x => owenT (h x) (z x / h x)) (nhdsWithin 0 (Ioi 0)) (nhds (1 / 4)))
    (hneglim : Tendsto (fun x => owenT (h x) (z x / h x)) (nhdsWithin 0 (Iio 0))
      (nhds (-(1 / 4))))
    (hinfTop : Tendsto (fun x => Real.exp (-(h x) ^ 2 / 2)) atTop (nhds 0))
    (hinfBot : Tendsto (fun x => Real.exp (-(h x) ^ 2 / 2)) atBot (nhds 0))
    (hint : Integrable (owenPsiDeriv h z h' z')) :
    ∫ x, owenPsiDeriv h z h' z' x = 1 := by
  rw [← integral_Iic_add_Ioi (b := (0 : ℝ)) hint.integrableOn hint.integrableOn,
    integral_Iic_owenPsiDeriv hh hz hne hneglim hinfBot hint.integrableOn,
    integral_Ioi_owenPsiDeriv hh hz hne hposlim hinfTop hint.integrableOn]
  norm_num

end NonmonicCubic.Gaussian
