/-
# The area formula for a real cubic

This is step 1 of the Rice-formula-free route to Problem A described in
`KacRice.lean`.

For `(a,b,c)` i.i.d. `N(0,1)`, the real roots of `f(x) = x³ + a x² + b x + c`
are, for **fixed** `(a,b)`, the solutions of `cub a b x = −c` where

    cub a b x = x³ + a x² + b x

is a *deterministic* cubic.  So `E[#roots]` never needs a statement about random
processes: integrating `c` out first turns it into the 1-D area formula

    ∫ φ(cub x) |cub′ x| dx  =  ∫ φ(y) · #{x : cub x = y} dy .

Mathlib has no coarea formula and no Banach indicatrix (checked 2026-08-18), but
it does not need one here: `cub′ = 3x² + 2ax + b` has at most two zeros, so `ℝ`
splits into at most **three** intervals on which `cub` is monotone, and on each
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn` applies —
a change-of-variables lemma with *no injectivity hypothesis* and an arbitrary
measurable domain.  The multiplicity function is then a sum of at most three
indicators, by construction rather than by a general theorem.

**The area formula is proved here in full.**  The headline is `lintegral_cub`:
for every `(a,b)` there are levels `B ≤ A` with

    ∫⁻ x, |cub′ x| · u (cub x)  =  ∫⁻ y, u y  +  2 ∫⁻ y in Icc B A, u y

for every `u : ℝ → ℝ≥0∞`.  When `a² ≤ 3b` the band is empty
(`lintegral_cub_of_le`); otherwise `A = cub x₁` and `B = cub x₂` are the two
critical values (`lintegral_cub_eq`).

Read with `u = φ` the standard normal density, this says

    E[#real roots | a, b]  =  1 + 2·P(−c lands between the critical values)
                           =  1 + 2·P(three real roots | a, b),

which is the `E[N] = 1 + 2p` bookkeeping of the Kac–Rice route — obtained with
no counting argument, no coarea formula and no Rice's formula.  What remains
before `E[N]` becomes the 1-D integral is the Tonelli swap and the inner
Gaussian integral (`KacRice.lean`); see `HANDOFF.md`.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import NonmonicCubic.Basic

namespace NonmonicCubic.AreaFormula

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- `cub a b x = x³ + a x² + b x`: the monic cubic with its constant term removed.
For fixed `(a,b)`, the roots of `x³ + a x² + b x + c` are the solutions of
`cub a b x = −c`. -/
def cub (a b x : ℝ) : ℝ := x ^ 3 + a * x ^ 2 + b * x

/-- The derivative of `cub a b`. -/
def dcub (a b x : ℝ) : ℝ := 3 * x ^ 2 + 2 * a * x + b

theorem hasDerivAt_cub (a b x : ℝ) : HasDerivAt (cub a b) (dcub a b x) x := by
  unfold cub dcub
  have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h2 : HasDerivAt (fun y : ℝ => a * y ^ 2) (a * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul a
  have h3 : HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have heq : 3 * x ^ 2 + 2 * a * x + b = 3 * x ^ 2 + a * (2 * x) + b := by ring
  rw [heq]
  exact (h1.add h2).add h3

@[fun_prop]
theorem continuous_cub (a b : ℝ) : Continuous (cub a b) := by
  unfold cub; fun_prop

theorem deriv_cub (a b x : ℝ) : deriv (cub a b) x = dcub a b x :=
  (hasDerivAt_cub a b x).deriv

theorem differentiable_cub (a b : ℝ) : Differentiable ℝ (cub a b) :=
  fun x => (hasDerivAt_cub a b x).differentiableAt

/-! ## Behaviour at infinity

Once `|x| ≥ |a| + |b| + 1` the quadratic `x² + a x + b − 1` is nonnegative, so
`cub a b x − x = x (x² + a x + b − 1)` has the sign of `x`.  That single bound
gives both `Tendsto` statements, hence surjectivity and the images of the
monotone pieces. -/

/-- The one inequality behind both limits: `x² + a x + b − 1 ≥ 0` as soon as
`|x| ≥ max 1 (|a| + |b| + 1)`. -/
private theorem key_bound {a b x : ℝ} (h1 : (1 : ℝ) ≤ |x|) (h2 : |a| + |b| + 1 ≤ |x|) :
    0 ≤ x ^ 2 + a * x + b - 1 := by
  have hax : -(|a| * |x|) ≤ a * x := by
    have h := neg_abs_le (a * x); rwa [abs_mul] at h
  have hb : -|b| ≤ b := neg_abs_le b
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |x| - (|a| + |b| + 1))
      (by linarith : (0 : ℝ) ≤ |x|),
    mul_nonneg (abs_nonneg b) (by linarith : (0 : ℝ) ≤ |x| - 1)]

theorem tendsto_cub_atTop (a b : ℝ) : Tendsto (cub a b) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (max 1 (|a| + |b| + 1))] with x hx
  have h1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have h2 : |a| + |b| + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have habs : |x| = x := abs_of_nonneg hx0
  have key : 0 ≤ x ^ 2 + a * x + b - 1 :=
    key_bound (by rw [habs]; linarith) (by rw [habs]; linarith)
  have : x ≤ cub a b x := by unfold cub; nlinarith [mul_nonneg hx0 key]
  simpa using this

theorem tendsto_cub_atBot (a b : ℝ) : Tendsto (cub a b) atBot atBot := by
  refine tendsto_atBot_mono' atBot ?_ tendsto_id
  filter_upwards [eventually_le_atBot (-(max 1 (|a| + |b| + 1)))] with x hx
  have h0 : max 1 (|a| + |b| + 1) ≤ -x := by linarith
  have h1 : (1 : ℝ) ≤ -x := le_trans (le_max_left _ _) h0
  have h2 : |a| + |b| + 1 ≤ -x := le_trans (le_max_right _ _) h0
  have hx0 : x ≤ (0 : ℝ) := by linarith
  have habs : |x| = -x := abs_of_nonpos hx0
  have key : 0 ≤ x ^ 2 + a * x + b - 1 :=
    key_bound (by rw [habs]; linarith) (by rw [habs]; linarith)
  have : cub a b x ≤ x := by
    unfold cub; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x) key]
  simpa using this

theorem surjective_cub (a b : ℝ) : Function.Surjective (cub a b) :=
  (continuous_cub a b).surjective (tendsto_cub_atTop a b) (tendsto_cub_atBot a b)

theorem image_univ_cub (a b : ℝ) : cub a b '' univ = univ := by
  rw [Set.image_univ, (surjective_cub a b).range_eq]

/-! ## The case `a² ≤ 3b`: `cub` is monotone and every level has one root -/

/-- `3x² + 2ax + b ≥ 0` exactly when the discriminant `4a² − 12b` is `≤ 0`. -/
theorem dcub_nonneg (a b : ℝ) (hab : a ^ 2 ≤ 3 * b) (x : ℝ) : 0 ≤ dcub a b x := by
  unfold dcub
  nlinarith [sq_nonneg (3 * x + a)]

theorem monotone_cub (a b : ℝ) (hab : a ^ 2 ≤ 3 * b) : Monotone (cub a b) := by
  refine monotone_of_deriv_nonneg (differentiable_cub a b) fun x => ?_
  rw [deriv_cub]
  exact dcub_nonneg a b hab x

/-- The area formula in the form the change-of-variables lemma delivers it, with
the derivative not yet wrapped in an absolute value.  `lintegral_cub_of_le` is
the version to quote. -/
theorem lintegral_cub_of_le' (a b : ℝ) (hab : a ^ 2 ≤ 3 * b) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (dcub a b x) * u (cub a b x) = ∫⁻ y, u y := by
  have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (f := cub a b) (f' := dcub a b) (s := univ) MeasurableSet.univ
    (fun x _ => (hasDerivAt_cub a b x).hasDerivWithinAt)
    ((monotone_cub a b hab).monotoneOn univ) u
  rw [image_univ_cub] at key
  simp only [Measure.restrict_univ] at key
  exact key.symm

/-- **The area formula for a cubic with nonnegative derivative.**

When `a² ≤ 3b` the map `cub a b` is a monotone bijection of `ℝ`, so for every
`u : ℝ → ℝ≥0∞`

    ∫⁻ x, |cub′ a b x| · u (cub a b x)  =  ∫⁻ y, u y .

Read with `u = φ` the standard normal density, the right-hand side is `1`: in
the region `a² ≤ 3b` the cubic has exactly one real root for every value of `c`.
Obtained with no counting argument and no Rice's formula — only a `MonotoneOn`
change of variables. -/
theorem lintegral_cub_of_le (a b : ℝ) (hab : a ^ 2 ≤ 3 * b) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (|dcub a b x|) * u (cub a b x) = ∫⁻ y, u y := by
  rw [← lintegral_cub_of_le' a b hab u]
  exact lintegral_congr fun x => by rw [abs_of_nonneg (dcub_nonneg a b hab x)]


/-! ## The case `a² > 3b`: three monotone pieces and the three-root band

Now `dcub a b` factors as `3(x − x₁)(x − x₂)` with `x₁ < x₂`, and `ℝ` splits into
`Iic x₁` (increasing), `Icc x₁ x₂` (decreasing), `Ici x₂` (increasing).  Rather
than introduce square roots, the factorisation is taken as a hypothesis;
`exists_factorisation_dcub` produces it from `a² ≥ 3b`.

The result is the *whole* area formula: the level `y` is hit once, twice or three
times according to where it sits relative to `cub x₂ ≤ cub x₁`, and

    ∫⁻ x, |cub′ x| · u (cub x)  =  ∫⁻ y, u y  +  2 ∫⁻ y in Icc (cub x₂) (cub x₁), u y .

With `u = φ` this is exactly `E[#roots | a, b] = 1 + 2·P(three roots | a, b)`. -/

/-- The critical points, when the discriminant of `cub′` is nonnegative. -/
theorem exists_factorisation_dcub (a b : ℝ) (hab : 3 * b ≤ a ^ 2) :
    ∃ x₁ x₂ : ℝ, x₁ ≤ x₂ ∧ ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂) := by
  set s := Real.sqrt (a ^ 2 - 3 * b) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 - 3 * b := Real.sq_sqrt (by linarith)
  refine ⟨(-a - s) / 3, (-a + s) / 3, by linarith, fun x => ?_⟩
  unfold dcub
  field_simp
  nlinarith [hs2]

variable {a b x₁ x₂ : ℝ}

theorem dcub_nonneg_Iic (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) {x : ℝ} (hx : x ∈ Iic x₁) : 0 ≤ dcub a b x := by
  rw [hfac]
  have h1 : x - x₁ ≤ 0 := by simpa using hx
  nlinarith

theorem dcub_nonpos_Icc (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    {x : ℝ} (hx : x ∈ Icc x₁ x₂) : dcub a b x ≤ 0 := by
  rw [hfac]; nlinarith [hx.1, hx.2]

theorem dcub_nonneg_Ici (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) {x : ℝ} (hx : x ∈ Ici x₂) : 0 ≤ dcub a b x := by
  rw [hfac]
  have h2 : 0 ≤ x - x₂ := by simpa using hx
  nlinarith

theorem monotoneOn_cub_Iic (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) : MonotoneOn (cub a b) (Iic x₁) := by
  refine monotoneOn_of_deriv_nonneg (convex_Iic _) (continuous_cub a b).continuousOn
    (differentiable_cub a b).differentiableOn fun x hx => ?_
  rw [interior_Iic] at hx
  exact deriv_cub a b x ▸ dcub_nonneg_Iic hfac hlt (Set.mem_Iic.2 hx.le)

theorem antitoneOn_cub_Icc (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂)) :
    AntitoneOn (cub a b) (Icc x₁ x₂) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (continuous_cub a b).continuousOn
    (differentiable_cub a b).differentiableOn fun x hx => ?_
  rw [interior_Icc] at hx
  exact deriv_cub a b x ▸ dcub_nonpos_Icc hfac (Set.mem_Icc.2 ⟨hx.1.le, hx.2.le⟩)

theorem monotoneOn_cub_Ici (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) : MonotoneOn (cub a b) (Ici x₂) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) (continuous_cub a b).continuousOn
    (differentiable_cub a b).differentiableOn fun x hx => ?_
  rw [interior_Ici] at hx
  exact deriv_cub a b x ▸ dcub_nonneg_Ici hfac hlt (Set.mem_Ici.2 hx.le)

/-- **The area formula for a cubic, general case.**  The three monotone pieces
contribute the three intervals `Iic (cub x₁)`, `Icc (cub x₂) (cub x₁)` and
`Ici (cub x₂)` — i.e. exactly the levels hit by each branch. -/
theorem lintegral_cub_split (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (|dcub a b x|) * u (cub a b x)
      = ((∫⁻ y in Iic (cub a b x₁), u y) + ∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y)
        + ∫⁻ y in Ici (cub a b x₂), u y := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|dcub a b x|) * u (cub a b x) with hF
  -- split the line at the two critical points
  have hsplit : ∫⁻ x, F x = ((∫⁻ x in Iic x₁, F x) + ∫⁻ x in Ioc x₁ x₂, F x)
      + ∫⁻ x in Ioi x₂, F x := by
    rw [← lintegral_union measurableSet_Ioc (Set.Iic_disjoint_Ioc le_rfl),
      Set.Iic_union_Ioc_eq_Iic hlt,
      ← lintegral_union measurableSet_Ioi (Set.Iic_disjoint_Ioi le_rfl),
      Set.Iic_union_Ioi, Measure.restrict_univ]
  -- the half-open pieces may be closed up: endpoints are null
  have hIoc : ∫⁻ x in Ioc x₁ x₂, F x = ∫⁻ x in Icc x₁ x₂, F x :=
    setLIntegral_congr Ioc_ae_eq_Icc
  have hIoi : ∫⁻ x in Ioi x₂, F x = ∫⁻ x in Ici x₂, F x :=
    setLIntegral_congr Ioi_ae_eq_Ici
  rw [hsplit, hIoc, hIoi]
  -- now change variables on each piece
  have e1 : ∫⁻ x in Iic x₁, F x = ∫⁻ y in Iic (cub a b x₁), u y := by
    have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (f := cub a b) (f' := dcub a b) (s := Iic x₁) measurableSet_Iic
      (fun x _ => (hasDerivAt_cub a b x).hasDerivWithinAt) (monotoneOn_cub_Iic hfac hlt) u
    rw [(continuous_cub a b).continuousOn.image_Iic_of_monotoneOn (monotoneOn_cub_Iic hfac hlt)
      (tendsto_cub_atBot a b)] at key
    rw [key]
    refine setLIntegral_congr_fun measurableSet_Iic fun x hx => ?_
    rw [hF]; simp only; rw [abs_of_nonneg (dcub_nonneg_Iic hfac hlt hx)]
  have e2 : ∫⁻ x in Icc x₁ x₂, F x = ∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y := by
    have key := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (f := cub a b) (f' := dcub a b) (s := Icc x₁ x₂) measurableSet_Icc
      (fun x _ => (hasDerivAt_cub a b x).hasDerivWithinAt) (antitoneOn_cub_Icc hfac) u
    rw [(continuous_cub a b).continuousOn.image_Icc_of_antitoneOn hlt
      (antitoneOn_cub_Icc hfac)] at key
    rw [key]
    refine setLIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    rw [hF]; simp only; rw [abs_of_nonpos (dcub_nonpos_Icc hfac hx)]
  have e3 : ∫⁻ x in Ici x₂, F x = ∫⁻ y in Ici (cub a b x₂), u y := by
    have key := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (f := cub a b) (f' := dcub a b) (s := Ici x₂) measurableSet_Ici
      (fun x _ => (hasDerivAt_cub a b x).hasDerivWithinAt) (monotoneOn_cub_Ici hfac hlt) u
    rw [(continuous_cub a b).continuousOn.image_Ici_of_monotoneOn (monotoneOn_cub_Ici hfac hlt)
      (tendsto_cub_atTop a b)] at key
    rw [key]
    refine setLIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [hF]; simp only; rw [abs_of_nonneg (dcub_nonneg_Ici hfac hlt hx)]
  rw [e1, e2, e3]


/-- **`E[#roots | a,b] = 1 + 2·(band)`.**  Reorganising `lintegral_cub_split` by
inclusion–exclusion (`Iic A ∪ Ici B = ℝ` and `Iic A ∩ Ici B = Icc B A` for
`B ≤ A`) gives the form the Kac–Rice bookkeeping actually uses:

    ∫⁻ x, |cub′ x| · u (cub x)  =  ∫⁻ y, u y  +  2 ∫⁻ y in Icc (cub x₂) (cub x₁), u y .

With `u = φ` the standard normal density: the first term is `1`, and the second
is twice the probability that `−c` lands in the band between the two critical
values — i.e. exactly the event that the cubic has three real roots.  This is
`E[N] = 1 + 2 P(N = 3)` at fixed `(a,b)`, proved without Rice's formula. -/
theorem lintegral_cub_eq (hfac : ∀ x, dcub a b x = 3 * (x - x₁) * (x - x₂))
    (hlt : x₁ ≤ x₂) (u : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (|dcub a b x|) * u (cub a b x)
      = (∫⁻ y, u y) + 2 * ∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y := by
  have hBA : cub a b x₂ ≤ cub a b x₁ :=
    antitoneOn_cub_Icc hfac (Set.mem_Icc.2 ⟨le_rfl, hlt⟩) (Set.mem_Icc.2 ⟨hlt, le_rfl⟩) hlt
  have dj1 : Disjoint (Iio (cub a b x₂)) (Icc (cub a b x₂) (cub a b x₁)) :=
    Set.disjoint_left.2 fun y hy hy' => absurd hy'.1 (not_le.2 hy)
  have dj2 : Disjoint (Icc (cub a b x₂) (cub a b x₁)) (Ioi (cub a b x₁)) :=
    Set.disjoint_left.2 fun y hy hy' => absurd hy.2 (not_le.2 hy')
  have d1 : ∫⁻ y in Iic (cub a b x₁), u y
      = (∫⁻ y in Iio (cub a b x₂), u y) + ∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y := by
    rw [← lintegral_union measurableSet_Icc dj1, Set.Iio_union_Icc_eq_Iic hBA]
  have d2 : ∫⁻ y in Ici (cub a b x₂), u y
      = (∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y) + ∫⁻ y in Ioi (cub a b x₁), u y := by
    rw [← lintegral_union measurableSet_Ioi dj2, Set.Icc_union_Ioi_eq_Ici hBA]
  have d3 : ∫⁻ y, u y = ((∫⁻ y in Iio (cub a b x₂), u y)
      + ∫⁻ y in Icc (cub a b x₂) (cub a b x₁), u y) + ∫⁻ y in Ioi (cub a b x₁), u y := by
    rw [← lintegral_union measurableSet_Icc dj1, Set.Iio_union_Icc_eq_Iic hBA,
      ← lintegral_union measurableSet_Ioi (Set.Iic_disjoint_Ioi le_rfl),
      Set.Iic_union_Ioi, Measure.restrict_univ]
  rw [lintegral_cub_split hfac hlt u, d1, d2, d3]
  ring

/-- The two cases combined: for **every** `(a,b)`, `∫⁻ |cub′| · u ∘ cub` is
`∫⁻ u` plus twice a band term, the band being empty exactly when `a² ≤ 3b`. -/
theorem lintegral_cub (a b : ℝ) (u : ℝ → ℝ≥0∞) :
    ∃ B A : ℝ, ∫⁻ x, ENNReal.ofReal (|dcub a b x|) * u (cub a b x)
      = (∫⁻ y, u y) + 2 * ∫⁻ y in Icc B A, u y := by
  rcases le_or_gt (a ^ 2) (3 * b) with hab | hab
  · refine ⟨1, 0, ?_⟩
    rw [lintegral_cub_of_le a b hab u, Set.Icc_eq_empty (by norm_num)]
    simp
  · obtain ⟨y₁, y₂, hlt, hfac⟩ := exists_factorisation_dcub a b hab.le
    exact ⟨cub a b y₂, cub a b y₁, lintegral_cub_eq hfac hlt u⟩

end NonmonicCubic.AreaFormula
