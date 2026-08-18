/-
# The chain rule for `x ↦ T(k x, a x)`

Mathlib has no C¹ criterion (continuous partials ⇒ differentiable), so the total
derivative of Owen's `T` as a function of two variables is not available off the
shelf.  It is also not needed: what the Owen's-`T` cancellation requires is the
derivative of the **one-variable** composite `x ↦ T(k x, a x)`, and that can be
proved directly.

The argument is the standard split

    T(k x, a x) − T(k x₀, a x₀)
      = [T(k x, a x) − T(k x, a x₀)]  +  [T(k x, a x₀) − T(k x₀, a x₀)] .

The second bracket is a genuine one-variable composition, so
`hasDerivAt_owenT_left` plus the ordinary chain rule handles it.  The first
bracket is `(1/2π)∫_{a x₀}^{a x} F(k x, t) dt` — no derivative under an integral
sign is involved — and it is `o(x − x₀)` because `F` is *jointly* continuous, so
the integrand is uniformly close to `F(k x₀, a x₀)` on the shrinking interval,
while the interval length is `O(x − x₀)`.

So joint **continuity** suffices; joint differentiability is never needed.
-/
import NonmonicCubic.OwenT

namespace NonmonicCubic.Gaussian

open MeasureTheory Real Filter Asymptotics intervalIntegral

/-- The Owen integrand as a function on `ℝ × ℝ`, so that joint continuity can be
stated. -/
noncomputable def owenF (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1 ^ 2 * (1 + p.2 ^ 2) / 2) / (1 + p.2 ^ 2)

theorem continuous_owenF : Continuous owenF := by
  unfold owenF
  exact Continuous.div (by fun_prop) (by fun_prop) fun p => (one_add_sq_pos p.2).ne'

theorem owenF_apply (k t : ℝ) :
    owenF (k, t) = Real.exp (-k ^ 2 * (1 + t ^ 2) / 2) / (1 + t ^ 2) := rfl

/-- `T(k,b) − T(k,c)` is the integral over `[c,b]`: pure interval-integral
algebra, no fundamental theorem needed. -/
theorem owenT_sub (k b c : ℝ) :
    owenT k b - owenT k c = 1 / (2 * π) * ∫ t in c..b, owenF (k, t) := by
  unfold owenT
  rw [← mul_sub]
  congr 1
  exact intervalIntegral.integral_interval_sub_left
    ((continuous_owenIntegrand k).intervalIntegrable (μ := volume) 0 b)
    ((continuous_owenIntegrand k).intervalIntegrable (μ := volume) 0 c)

/-- **The uniformity that replaces joint differentiability.**  For every `c > 0`,
eventually in `x` the integrand stays within `c` of `owenF (k x₀, a x₀)` across
the whole shrinking interval `Ι (a x₀) (a x)`. -/
theorem owenF_unif {k a : ℝ → ℝ} {x₀ : ℝ} (hk : ContinuousAt k x₀) (ha : ContinuousAt a x₀)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in nhds x₀, ∀ t ∈ Set.uIoc (a x₀) (a x),
      ‖owenF (k x, t) - owenF (k x₀, a x₀)‖ ≤ c := by
  have hS : ∀ᶠ p in nhds ((k x₀, a x₀) : ℝ × ℝ),
      ‖owenF p - owenF (k x₀, a x₀)‖ < c := by
    have h := Metric.tendsto_nhds.1
      (continuous_owenF.continuousAt (x := ((k x₀, a x₀) : ℝ × ℝ))) c hc
    simpa [dist_eq_norm] using h
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hS
  obtain ⟨pk, hpk, pa, hpa, hall⟩ := hS
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.1 hpa
  filter_upwards [hk.eventually hpk, ha (Metric.ball_mem_nhds (a x₀) hδ)] with x hxk hxa
  intro t ht
  have hax : |a x - a x₀| < δ := by simpa [Real.dist_eq] using hxa
  have htmem : t ∈ Set.uIcc (a x₀) (a x) := Set.Ioc_subset_Icc_self ht
  have hdist : dist t (a x₀) < δ := by
    rw [Real.dist_eq, abs_lt]
    rw [abs_lt] at hax
    obtain ⟨h1, h2⟩ := hax
    rcases Set.mem_uIcc.1 htmem with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  exact le_of_lt (hall hxk (hδball hdist))


/-- **The chain rule for `x ↦ T(k x, a x)`.**  Both partials of `T` are proved
(`hasDerivAt_owenT_left`, `hasDerivAt_owenT_right`); this contracts them against
`k′` and `a′` without ever needing `T` to be differentiable as a function of two
variables — only that its `a`-integrand is *jointly continuous*. -/
theorem hasDerivAt_owenT_comp {k a : ℝ → ℝ} {k' a' x₀ : ℝ}
    (hk : HasDerivAt k k' x₀) (ha : HasDerivAt a a' x₀) :
    HasDerivAt (fun x => owenT (k x) (a x))
      (-(φ (k x₀) * (2 * Φ (a x₀ * k x₀) - 1)) / 2 * k'
        + 1 / (2 * π) * owenF (k x₀, a x₀) * a') x₀ := by
  have hkc : ContinuousAt k x₀ := hk.continuousAt
  have hac : ContinuousAt a x₀ := ha.continuousAt
  have hbig : (fun x => a x - a x₀) =O[nhds x₀] (fun x => x - x₀) :=
    ha.hasFDerivAt.isBigO_sub
  have hu : (fun x => ∫ t in (a x₀)..(a x), (owenF (k x, t) - owenF (k x₀, a x₀)))
      =o[nhds x₀] (fun x => a x - a x₀) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [owenF_unif hkc hac hc] with x hx
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => owenF (k x, t) - owenF (k x₀, a x₀)) (a := a x₀) (b := a x) (C := c) hx
    simpa [Real.norm_eq_abs] using h
  have h2 : HasDerivAt (fun x => owenT (k x) (a x₀))
      (-(φ (k x₀) * (2 * Φ (a x₀ * k x₀) - 1)) / 2 * k') x₀ := by
    simpa [Function.comp_def] using (hasDerivAt_owenT_left (a x₀) (k x₀)).comp x₀ hk
  have hR : HasDerivAt (fun x => owenT (k x) (a x) - owenT (k x) (a x₀))
      (1 / (2 * π) * owenF (k x₀, a x₀) * a') x₀ := by
    rw [hasDerivAt_iff_isLittleO]
    have hdecomp : ∀ x : ℝ,
        owenT (k x) (a x) - owenT (k x) (a x₀)
          - (owenT (k x₀) (a x₀) - owenT (k x₀) (a x₀))
          - (x - x₀) • (1 / (2 * π) * owenF (k x₀, a x₀) * a')
        = 1 / (2 * π) * (∫ t in (a x₀)..(a x), (owenF (k x, t) - owenF (k x₀, a x₀)))
          + 1 / (2 * π) * owenF (k x₀, a x₀) * (a x - a x₀ - (x - x₀) * a') := by
      intro x
      have hcont : Continuous fun t : ℝ => owenF (k x, t) := continuous_owenF.comp (by fun_prop)
      have hi1 := hcont.intervalIntegrable (μ := volume) (a x₀) (a x)
      have hi2 := (continuous_const (y := owenF (k x₀, a x₀))).intervalIntegrable
        (μ := volume) (a x₀) (a x)
      have hsplit : (∫ t in (a x₀)..(a x), (owenF (k x, t) - owenF (k x₀, a x₀)))
          = (∫ t in (a x₀)..(a x), owenF (k x, t))
            - (a x - a x₀) • owenF (k x₀, a x₀) := by
        rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const]
      rw [owenT_sub, hsplit, sub_self]
      simp only [smul_eq_mul]
      ring
    simp_rw [hdecomp]
    refine Asymptotics.IsLittleO.add ?_ ?_
    · exact (hu.trans_isBigO hbig).const_mul_left _
    · have hA : (fun x => a x - a x₀ - (x - x₀) * a') =o[nhds x₀] (fun x => x - x₀) := by
        simpa [smul_eq_mul] using hasDerivAt_iff_isLittleO.1 ha
      exact hA.const_mul_left _
  have hsum := h2.add hR
  have hfun : ((fun x => owenT (k x) (a x₀)) + fun x => owenT (k x) (a x) - owenT (k x) (a x₀))
      = fun x => owenT (k x) (a x) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hfun] at hsum
  exact hsum


/-! ## `Ψ′`

`Ψ(x) = −2 T(h x, z x / h x)`.  Away from `h = 0` the chain rule and
`owen_chain_rule_algebra` give exactly the Owen's-`T` cancellation. -/

/-- **`Ψ′ = φ(h)h′(2Φ(z) − 1) − (1/π)e^{−(h²+z²)/2}·θ′`** where
`θ′ = (h z′ − z h′)/(h² + z²)`.  Valid wherever `h ≠ 0`. -/
theorem hasDerivAt_owenPsi {h z : ℝ → ℝ} {h' z' x₀ : ℝ}
    (hh : HasDerivAt h h' x₀) (hz : HasDerivAt z z' x₀) (hne : h x₀ ≠ 0) :
    HasDerivAt (fun x => -2 * owenT (h x) (z x / h x))
      (φ (h x₀) * h' * (2 * Φ (z x₀) - 1)
        - 1 / π * Real.exp (-(h x₀ ^ 2 + z x₀ ^ 2) / 2)
          * ((h x₀ * z' - z x₀ * h') / (h x₀ ^ 2 + z x₀ ^ 2))) x₀ := by
  have hA : HasDerivAt (fun x => z x / h x) ((z' * h x₀ - z x₀ * h') / h x₀ ^ 2) x₀ :=
    hz.div hh hne
  have h2 := (hasDerivAt_owenT_comp hh hA).const_mul (-2 : ℝ)
  rw [owenF_apply] at h2
  rwa [owen_chain_rule_algebra (h x₀) (z x₀) h' z' hne] at h2


/-! ## The boundary values of `Ψ`

At `x → ±∞`, `h → ±∞` and the uniform bound `|T(k,a)| ≤ e^{−k²/2}/4` kills `Ψ`.

At `x → 0^±` the situation looks harder — `h → 0` while `z/h → ±∞`, a genuine
two-variable limit — but a *crude* bound suffices:
`|T(k,a) − T(0,a)| ≤ (1/2π)(k²/2)|a|`, and in the application
`k² a = h²·(z/h) = h z → 0`.  So `T(h, z/h) − T(0, z/h) → 0`, and `T(0, ·) → ±1/4`
is already proved.  No uniform-in-`a` estimate is needed. -/

theorem one_sub_exp_neg_le (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  have := Real.add_one_le_exp (-u)
  linarith

theorem owenT_sub_left (k a : ℝ) :
    owenT k a - owenT 0 a = 1 / (2 * π) * ∫ t in (0 : ℝ)..a, (owenF (k, t) - owenF (0, t)) := by
  have hk := (continuous_owenIntegrand k).intervalIntegrable (μ := volume) 0 a
  have h0 := (continuous_owenIntegrand 0).intervalIntegrable (μ := volume) 0 a
  simp only [owenF_apply]
  unfold owenT
  rw [← mul_sub]
  congr 1
  rw [intervalIntegral.integral_sub hk h0]

/-- The crude comparison with `k = 0`: `|T(k,a) − T(0,a)| ≤ (1/2π)(k²/2)|a|`. -/
theorem abs_owenT_sub_owenT_zero_le (k a : ℝ) :
    |owenT k a - owenT 0 a| ≤ 1 / (2 * π) * (k ^ 2 / 2) * |a| := by
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) a, ‖owenF (k, t) - owenF (0, t)‖ ≤ k ^ 2 / 2 := by
    intro t _
    have h1 : (0 : ℝ) < 1 + t ^ 2 := one_add_sq_pos t
    have hE : Real.exp (-k ^ 2 * (1 + t ^ 2) / 2)
        = Real.exp (-(k ^ 2 * (1 + t ^ 2) / 2)) := by congr 1; ring
    have hE0 : Real.exp (-(0 : ℝ) ^ 2 * (1 + t ^ 2) / 2) = 1 := by norm_num
    have hu : (0 : ℝ) ≤ k ^ 2 * (1 + t ^ 2) / 2 := by positivity
    have hle : Real.exp (-(k ^ 2 * (1 + t ^ 2) / 2)) ≤ 1 := by
      have hx : Real.exp (-(k ^ 2 * (1 + t ^ 2) / 2)) ≤ Real.exp 0 :=
        Real.exp_le_exp.2 (by linarith)
      rwa [Real.exp_zero] at hx
    have hge := one_sub_exp_neg_le (k ^ 2 * (1 + t ^ 2) / 2)
    rw [owenF_apply, owenF_apply, Real.norm_eq_abs, hE, hE0, div_sub_div_same, abs_div,
      abs_of_pos h1, div_le_iff₀ h1]
    have habs : |Real.exp (-(k ^ 2 * (1 + t ^ 2) / 2)) - 1|
        = 1 - Real.exp (-(k ^ 2 * (1 + t ^ 2) / 2)) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs]
    linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, sub_zero] at h
  rw [owenT_sub_left, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  calc 1 / (2 * π) * |∫ t in (0 : ℝ)..a, (owenF (k, t) - owenF (0, t))|
      ≤ 1 / (2 * π) * (k ^ 2 / 2 * |a|) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / (2 * π) * (k ^ 2 / 2) * |a| := by ring

/-- `T(k x, a x) → 1/4` when `a → +∞` and `k² a → 0`. -/
theorem tendsto_owenT_quarter {k a : ℝ → ℝ} {l : Filter ℝ}
    (hka : Filter.Tendsto (fun x => k x ^ 2 * a x) l (nhds 0))
    (ha : Filter.Tendsto a l Filter.atTop) :
    Filter.Tendsto (fun x => owenT (k x) (a x)) l (nhds (1 / 4)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : Filter.Tendsto (fun x => owenT 0 (a x)) l (nhds (1 / 4)) :=
    tendsto_owenT_zero_atTop.comp ha
  have h2 : Filter.Tendsto (fun x => owenT (k x) (a x) - owenT 0 (a x)) l (nhds 0) := by
    have hb : Filter.Tendsto (fun x => 1 / (4 * π) * |k x ^ 2 * a x|) l (nhds 0) := by
      simpa using (hka.abs).const_mul (1 / (4 * π))
    refine squeeze_zero_norm (fun x => ?_) hb
    rw [Real.norm_eq_abs]
    calc |owenT (k x) (a x) - owenT 0 (a x)| ≤ 1 / (2 * π) * (k x ^ 2 / 2) * |a x| :=
          abs_owenT_sub_owenT_zero_le _ _
      _ = 1 / (4 * π) * |k x ^ 2 * a x| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (k x))]
          field_simp
          ring
  have hfun : (fun x => owenT 0 (a x) + (owenT (k x) (a x) - owenT 0 (a x)))
      = fun x => owenT (k x) (a x) := by funext x; ring
  have hsum := h1.add h2
  rw [hfun] at hsum
  simpa using hsum

/-- `T(k x, a x) → −1/4` when `a → −∞` and `k² a → 0`. -/
theorem tendsto_owenT_neg_quarter {k a : ℝ → ℝ} {l : Filter ℝ}
    (hka : Filter.Tendsto (fun x => k x ^ 2 * a x) l (nhds 0))
    (ha : Filter.Tendsto a l Filter.atBot) :
    Filter.Tendsto (fun x => owenT (k x) (a x)) l (nhds (-(1 / 4))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : Filter.Tendsto (fun x => owenT 0 (a x)) l (nhds (-(1 / 4))) :=
    tendsto_owenT_zero_atBot.comp ha
  have h2 : Filter.Tendsto (fun x => owenT (k x) (a x) - owenT 0 (a x)) l (nhds 0) := by
    have hb : Filter.Tendsto (fun x => 1 / (4 * π) * |k x ^ 2 * a x|) l (nhds 0) := by
      simpa using (hka.abs).const_mul (1 / (4 * π))
    refine squeeze_zero_norm (fun x => ?_) hb
    rw [Real.norm_eq_abs]
    calc |owenT (k x) (a x) - owenT 0 (a x)| ≤ 1 / (2 * π) * (k x ^ 2 / 2) * |a x| :=
          abs_owenT_sub_owenT_zero_le _ _
      _ = 1 / (4 * π) * |k x ^ 2 * a x| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (k x))]
          field_simp
          ring
  have hfun : (fun x => owenT 0 (a x) + (owenT (k x) (a x) - owenT 0 (a x)))
      = fun x => owenT (k x) (a x) := by funext x; ring
  have hsum := h1.add h2
  rw [hfun] at hsum
  simpa using hsum

/-- `T(k x, a x) → 0` whenever `e^{−(k x)²/2} → 0`, i.e. `|k x| → ∞`. -/
theorem tendsto_owenT_zero_of_exp {k a : ℝ → ℝ} {l : Filter ℝ}
    (hk : Filter.Tendsto (fun x => Real.exp (-(k x) ^ 2 / 2)) l (nhds 0)) :
    Filter.Tendsto (fun x => owenT (k x) (a x)) l (nhds 0) := by
  refine squeeze_zero_norm (fun x => ?_) (by simpa using hk.div_const 4)
  simpa [Real.norm_eq_abs] using abs_owenT_le (k x) (a x)

end NonmonicCubic.Gaussian
