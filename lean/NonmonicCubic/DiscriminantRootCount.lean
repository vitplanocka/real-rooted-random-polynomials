/-
# Stage 5 — the classical link between `sign Δ` and the number of real roots

Everything in Theorems 1–3 is a statement about the **sign of a polynomial** `Δ`.
The informal claims say "…has three real roots".  Bridging the two needs, for
`a ≠ 0`:

> `Δ₄ a b c d > 0`  ↔  `a x³ + b x² + c x + d` has three **distinct real** roots.

This is completely classical, and is used without citation as a background fact
in the project's public explainer.  It is **not** in Mathlib.  What Mathlib has
(checked by grepping `.lake/packages/mathlib`, 2026-08-17):

* `Cubic.discr` (`Mathlib/Algebra/CubicDiscriminant.lean:461`) — the same
  polynomial as our `Δ₄` (proved: `Δ₄_eq_cubic_discr` in `Theorem3Statement.lean`);
* `Cubic.discr_ne_zero_iff_roots_nodup` (ibid.:477) and
  `Cubic.card_roots_of_discr_ne_zero` (ibid.:486) — these relate `discr ≠ 0` to
  the roots being *distinct*, **over a splitting field**, and say nothing about
  the *sign* of `discr` or about how many roots are *real*;
* `discrim` (`Mathlib/Algebra/QuadraticDiscriminant.lean:48`) — quadratic only,
  and it *does* have the sign↔real-roots story, but only in degree 2.

So the degree-3 sign↔real-root-count statement is a genuine gap in Mathlib, not
merely something we did not look up.

## Status in this file

* `Δ₄_of_roots` and `Δ₄_pos_of_three_distinct_roots`: **PROVED.**  The direction
  "three distinct real roots ⟹ `Δ₄ > 0`" is a `ring` identity
  (`Δ₄ = a⁴((x-y)(x-z)(y-z))²`) plus positivity.
* `three_distinct_roots_of_Δ₄_pos`: **PROVED.**  The converse is a real analysis
  argument: `Δ₄ > 0` forces `b² - 3ac > 0`, so the cubic's two critical points
  `x∓ = (-b ∓ √(b²-3ac))/(3a)` exist; the values there have strictly opposite
  signs; three sign changes give three roots by the intermediate value theorem;
  and three distinct roots of a cubic determine its factorisation.
* `Δ₄_pos_iff_three_distinct_real_roots`: **PROVED**, being the conjunction.

Consequently, for **Theorems 1 and 2** — which are themselves fully proved — the
English sentence "P(three real roots) = …" is now machine-checked end to end:
see `theorem1_root_count` and `theorem2_root_count` at the bottom of this file.
The same now holds for **Theorem 3**: `Theorem3Proof.theorem3` is proved, and
this file supplies the other half of that bridge.
-/
import NonmonicCubic.Theorem3Statement

namespace NonmonicCubic

open Real Set

/-- "`a x³ + b x² + c x + d` has three distinct real roots", stated elementarily
as a complete real factorisation with pairwise distinct roots. -/
def HasThreeDistinctRealRoots (a b c d : ℝ) : Prop :=
  ∃ x y z : ℝ, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ∀ t : ℝ, a * t ^ 3 + b * t ^ 2 + c * t + d = a * (t - x) * (t - y) * (t - z)

/-- **PROVED.**  The discriminant in terms of the roots: `Δ = a⁴ ∏ (rᵢ - rⱼ)²`.
Pure `ring`. -/
theorem Δ₄_of_roots (a x y z : ℝ) :
    Δ₄ a (-(a * (x + y + z))) (a * (x * y + y * z + z * x)) (-(a * (x * y * z)))
      = a ^ 4 * ((x - y) * (x - z) * (y - z)) ^ 2 := by
  unfold Δ₄; ring

/-- **PROVED.**  Reading the coefficients off a complete factorisation. -/
theorem coeffs_of_factorisation {a b c d x y z : ℝ}
    (h : ∀ t : ℝ, a * t ^ 3 + b * t ^ 2 + c * t + d = a * (t - x) * (t - y) * (t - z)) :
    b = -(a * (x + y + z)) ∧ c = a * (x * y + y * z + z * x) ∧ d = -(a * (x * y * z)) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  refine ⟨by nlinarith [h0, h1, h2], by nlinarith [h0, h1, h2], by nlinarith [h0]⟩

/-- **PROVED.**  Three distinct real roots force `Δ₄ > 0`. -/
theorem Δ₄_pos_of_three_distinct_roots {a b c d : ℝ} (ha : a ≠ 0)
    (h : HasThreeDistinctRealRoots a b c d) : 0 < Δ₄ a b c d := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hfac⟩ := h
  obtain ⟨hb, hc, hd⟩ := coeffs_of_factorisation hfac
  subst hb; subst hc; subst hd
  rw [Δ₄_of_roots]
  have h1 : (0 : ℝ) < a ^ 4 := by positivity
  have h2 : ((x - y) * (x - z) * (y - z)) ^ 2 > 0 := by
    have : (x - y) * (x - z) * (y - z) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> [exact sub_ne_zero.2 hxy;
        exact sub_ne_zero.2 hxz; exact sub_ne_zero.2 hyz]
    positivity
  positivity

/-! ### Ingredients for the converse

`DiscriminantRootCount` is imported by `Theorem3Proof`, so we cannot import the
latter's `Δ₄_completeSquare`; the identity is a one-line `ring` fact and is
simply restated here under a different name. -/

/-- Local copy of the completed-square identity `-27a²Δ = q² - 4p³` with
`p = b² - 3ac`, `q = 27a²d - 9abc + 2b³`.  (`Theorem3Proof.Δ₄_completeSquare`
says the same thing, but importing it here would create a cycle.) -/
private theorem Δ₄_completeSquare_local (a b c d : ℝ) :
    -27 * a ^ 2 * Δ₄ a b c d
      = (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) ^ 2 - 4 * (b ^ 2 - 3 * a * c) ^ 3 := by
  unfold Δ₄; ring

/-- A quadratic with three distinct roots is identically zero. -/
private theorem quadratic_zero_of_three_roots {A B C r₁ r₂ r₃ : ℝ}
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (e₁ : A * r₁ ^ 2 + B * r₁ + C = 0) (e₂ : A * r₂ ^ 2 + B * r₂ + C = 0)
    (e₃ : A * r₃ ^ 2 + B * r₃ + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have k₁₂ : A * (r₁ + r₂) + B = 0 := by
    have hz : (r₁ - r₂) * (A * (r₁ + r₂) + B) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 h₁₂)
  have k₁₃ : A * (r₁ + r₃) + B = 0 := by
    have hz : (r₁ - r₃) * (A * (r₁ + r₃) + B) = 0 := by linear_combination e₁ - e₃
    exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 h₁₃)
  have hA : A = 0 := by
    have hz : (r₂ - r₃) * A = 0 := by linear_combination k₁₂ - k₁₃
    exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 h₂₃)
  have hB : B = 0 := by linear_combination k₁₂ - (r₁ + r₂) * hA
  exact ⟨hA, hB, by linear_combination e₁ - r₁ ^ 2 * hA - r₁ * hB⟩

/-- Three distinct roots of `a t³ + b t² + c t + d` give the full factorisation.
This is the converse of `coeffs_of_factorisation`, proved by elementary linear
algebra rather than by polynomial division. -/
private theorem factorisation_of_three_roots {a b c d r₁ r₂ r₃ : ℝ}
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃)
    (e₁ : a * r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0)
    (e₂ : a * r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0)
    (e₃ : a * r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0) :
    ∀ t : ℝ, a * t ^ 3 + b * t ^ 2 + c * t + d = a * (t - r₁) * (t - r₂) * (t - r₃) := by
  obtain ⟨hA, hB, hC⟩ :=
    quadratic_zero_of_three_roots (A := b + a * (r₁ + r₂ + r₃))
      (B := c - a * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) (C := d + a * (r₁ * r₂ * r₃))
      h₁₂ h₁₃ h₂₃ (by linear_combination e₁) (by linear_combination e₂)
      (by linear_combination e₃)
  intro t
  linear_combination t ^ 2 * hA + t * hB + hC

/-- `x² < y²` with `0 < y` pins `x` inside `(-y, y)`.  (Mathlib's
`abs_lt_abs_of_sq_lt_sq` does not exist in this version.) -/
private theorem lt_and_lt_of_sq_lt_sq {x y : ℝ} (hy : 0 < y) (h : x ^ 2 < y ^ 2) :
    -y < x ∧ x < y :=
  ⟨by nlinarith [sq_nonneg (x + y)], by nlinarith [sq_nonneg (x - y)]⟩

/-- The value of `27a²·f` at a point where `3at + b = s`, given `s² = b² - 3ac`.
Identity 1: `27a²·f t = u³ - 3pu + q` for `u = 3at + b`. -/
private theorem cubic_at_crit {a b c d s t : ℝ} (hu : 3 * a * t + b = s)
    (hs2 : s ^ 2 = b ^ 2 - 3 * a * c) :
    27 * a ^ 2 * (a * t ^ 3 + b * t ^ 2 + c * t + d)
      = -2 * s ^ 3 + (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) := by
  linear_combination ((3 * a * t + b - s) ^ 2 + 3 * (3 * a * t + b - s) * s + 3 * s ^ 2
    - 3 * (b ^ 2 - 3 * a * c)) * hu + (3 * s) * hs2

/-- With positive leading coefficient the cubic is eventually negative to the
left: an explicit point `L ≤ m` with `f L < 0`. -/
theorem exists_le_cubic_neg {a b c d : ℝ} (ha : 0 < a) (m : ℝ) :
    ∃ L : ℝ, L ≤ m ∧ a * L ^ 3 + b * L ^ 2 + c * L + d < 0 := by
  have ha' : a ≠ 0 := ha.ne'
  obtain ⟨T, hT1, haT, hTm⟩ :
      ∃ T : ℝ, 1 ≤ T ∧ a * T = |b| + |c| + |d| + a * |m| + a ∧ -T ≤ m := by
    refine ⟨(|b| + |c| + |d|) / a + |m| + 1, ?_, by field_simp, ?_⟩
    · have h₁ : (0 : ℝ) ≤ (|b| + |c| + |d|) / a := by positivity
      have h₂ : (0 : ℝ) ≤ |m| := abs_nonneg m
      linarith
    · have h₁ : (0 : ℝ) ≤ (|b| + |c| + |d|) / a := by positivity
      have h₂ : -|m| ≤ m := neg_abs_le m
      linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hsq : T ≤ T ^ 2 := by nlinarith
  refine ⟨-T, hTm, ?_⟩
  have hb : b * T ^ 2 ≤ |b| * T ^ 2 := by nlinarith [le_abs_self b, sq_nonneg T]
  have hc : -(c * T) ≤ |c| * T ^ 2 := by
    have h₁ : (0 : ℝ) ≤ (|c| + c) * T := mul_nonneg (by linarith [neg_abs_le c]) hT0.le
    have h₂ : (0 : ℝ) ≤ |c| * (T ^ 2 - T) := mul_nonneg (abs_nonneg c) (by linarith)
    nlinarith
  have hd : d ≤ |d| * T ^ 2 := by
    have h₁ : (0 : ℝ) ≤ |d| * (T ^ 2 - 1) := mul_nonneg (abs_nonneg d) (by nlinarith)
    nlinarith [le_abs_self d]
  have hkey : a * T ^ 3 = (|b| + |c| + |d|) * T ^ 2 + (a * |m| + a) * T ^ 2 := by
    linear_combination T ^ 2 * haT
  have hpos : 0 < (a * |m| + a) * T ^ 2 :=
    mul_pos (by nlinarith [abs_nonneg m]) (pow_pos hT0 2)
  nlinarith [hb, hc, hd, hkey, hpos]

/-- Mirror image of `exists_le_cubic_neg`: an explicit point `R ≥ M` with
`f R > 0`. -/
theorem exists_ge_cubic_pos {a b c d : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ R : ℝ, M ≤ R ∧ 0 < a * R ^ 3 + b * R ^ 2 + c * R + d := by
  obtain ⟨L, hLle, hLneg⟩ := exists_le_cubic_neg (a := a) (b := -b) (c := c) (d := -d) ha (-M)
  exact ⟨-L, by linarith, by nlinarith [hLneg]⟩

/-- **PROVED.**  The converse in the case of positive leading coefficient. -/
private theorem three_distinct_roots_of_pos_lead {a b c d : ℝ} (ha : 0 < a)
    (h : 0 < Δ₄ a b c d) : HasThreeDistinctRealRoots a b c d := by
  have ha' : a ≠ 0 := ha.ne'
  have ha2 : (0 : ℝ) < 27 * a ^ 2 := by positivity
  have hcs := Δ₄_completeSquare_local a b c d
  have hq2 : (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) ^ 2
      < 4 * (b ^ 2 - 3 * a * c) ^ 3 := by nlinarith [mul_pos ha2 h]
  have hp : 0 < b ^ 2 - 3 * a * c := by
    nlinarith [sq_nonneg (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3),
      sq_nonneg (b ^ 2 - 3 * a * c)]
  obtain ⟨s, hs, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = b ^ 2 - 3 * a * c :=
    ⟨Real.sqrt (b ^ 2 - 3 * a * c), Real.sqrt_pos.2 hp, Real.sq_sqrt hp.le⟩
  have hs6 : s ^ 6 = (b ^ 2 - 3 * a * c) ^ 3 := by rw [← hs2]; ring
  obtain ⟨hlow, hhigh⟩ :=
    lt_and_lt_of_sq_lt_sq (x := 27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) (y := 2 * s ^ 3)
      (by positivity) (by nlinarith [hq2, hs6])
  obtain ⟨xm, hxm⟩ : ∃ t : ℝ, 3 * a * t + b = -s := ⟨(-b - s) / (3 * a), by field_simp; ring⟩
  obtain ⟨xM, hxM⟩ : ∃ t : ℝ, 3 * a * t + b = s := ⟨(-b + s) / (3 * a), by field_simp; ring⟩
  have hfm : 27 * a ^ 2 * (a * xm ^ 3 + b * xm ^ 2 + c * xm + d)
      = 2 * s ^ 3 + (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) := by
    have hfm' := cubic_at_crit (a := a) (b := b) (c := c) (d := d) (s := -s) (t := xm) hxm
      (by linear_combination hs2)
    linear_combination hfm'
  have hfM : 27 * a ^ 2 * (a * xM ^ 3 + b * xM ^ 2 + c * xM + d)
      = -2 * s ^ 3 + (27 * a ^ 2 * d - 9 * a * b * c + 2 * b ^ 3) := cubic_at_crit hxM hs2
  have hFm : 0 < a * xm ^ 3 + b * xm ^ 2 + c * xm + d := by nlinarith [hfm, hlow, ha2]
  have hFM : a * xM ^ 3 + b * xM ^ 2 + c * xM + d < 0 := by nlinarith [hfM, hhigh, ha2]
  have hlt : xm < xM := by nlinarith [hxm, hxM, hs, ha]
  have hcont : Continuous fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d := by fun_prop
  obtain ⟨L, hLle, hLneg⟩ := exists_le_cubic_neg (b := b) (c := c) (d := d) ha xm
  obtain ⟨R, hRge, hRpos⟩ := exists_ge_cubic_pos (b := b) (c := c) (d := d) ha xM
  obtain ⟨r₁, hm₁, hr₁⟩ := intermediate_value_Icc hLle hcont.continuousOn
    (show (0 : ℝ) ∈ Icc ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) L)
      ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) xm) by
        simp only [Set.mem_Icc]; exact ⟨hLneg.le, hFm.le⟩)
  obtain ⟨r₂, hm₂, hr₂⟩ := intermediate_value_Icc' hlt.le hcont.continuousOn
    (show (0 : ℝ) ∈ Icc ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) xM)
      ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) xm) by
        simp only [Set.mem_Icc]; exact ⟨hFM.le, hFm.le⟩)
  obtain ⟨r₃, hm₃, hr₃⟩ := intermediate_value_Icc hRge hcont.continuousOn
    (show (0 : ℝ) ∈ Icc ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) xM)
      ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) R) by
        simp only [Set.mem_Icc]; exact ⟨hFM.le, hRpos.le⟩)
  have e₁ : a * r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0 := hr₁
  have e₂ : a * r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0 := hr₂
  have e₃ : a * r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0 := hr₃
  have o₁ : r₁ < xm := lt_of_le_of_ne hm₁.2 (by rintro rfl; linarith)
  have o₂ : xm < r₂ := lt_of_le_of_ne hm₂.1 (by rintro rfl; linarith)
  have o₃ : r₂ < xM := lt_of_le_of_ne hm₂.2 (by rintro rfl; linarith)
  have o₄ : xM < r₃ := lt_of_le_of_ne hm₃.1 (by rintro rfl; linarith)
  have h₁₂ : r₁ ≠ r₂ := by intro hEq; rw [hEq] at o₁; linarith
  have h₁₃ : r₁ ≠ r₃ := by intro hEq; rw [hEq] at o₁; linarith
  have h₂₃ : r₂ ≠ r₃ := by intro hEq; rw [hEq] at o₃; linarith
  exact ⟨r₁, r₂, r₃, h₁₂, h₁₃, h₂₃, factorisation_of_three_roots h₁₂ h₁₃ h₂₃ e₁ e₂ e₃⟩

/-- **PROVED.**  The converse: a positive discriminant forces three distinct
real roots.

`Δ₄ > 0` and `a ≠ 0` force `p = b² - 3ac > 0` (via the completed-square identity
`-27a²Δ₄ = q² - 4p³`, whose left-hand side is negative).  Writing `s = √p`, the
two points `x∓ = (-b ∓ s)/(3a)` satisfy `3a·x∓ + b = ∓s`, and Identity 1
`27a²·f t = (3at+b)³ - 3p(3at+b) + q` evaluates `27a²·f x∓` to `±2s³ + q`.  Since
`q² < 4p³ = (2s³)²` we get `|q| < 2s³`, hence `f x₋ > 0 > f x₊`.  Three
applications of the intermediate value theorem — on `[L, x₋]`, `[x₋, x₊]` and
`[x₊, R]` for explicit far-out points `L`, `R` — produce three roots
`r₁ < x₋ < r₂ < x₊ < r₃`, and `factorisation_of_three_roots` turns them into the
required factorisation.  The case `a < 0` is reduced to `a > 0` by `Δ₄_neg`. -/
theorem three_distinct_roots_of_Δ₄_pos {a b c d : ℝ} (ha : a ≠ 0)
    (h : 0 < Δ₄ a b c d) : HasThreeDistinctRealRoots a b c d := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h' : 0 < Δ₄ (-a) (-b) (-c) (-d) := by rw [Δ₄_neg]; exact h
    obtain ⟨x, y, z, hxy, hxz, hyz, hfac⟩ :=
      three_distinct_roots_of_pos_lead (by linarith : (0 : ℝ) < -a) h'
    exact ⟨x, y, z, hxy, hxz, hyz, fun t => by linear_combination -hfac t⟩
  · exact three_distinct_roots_of_pos_lead hpos h

/-- **STAGE 5, the classical fact, fully proved.**

`Δ₄ a b c d > 0 ↔ a x³ + b x² + c x + d has three distinct real roots` (`a ≠ 0`).
The `←` direction is `Δ₄_pos_of_three_distinct_roots`; the `→` direction is
`three_distinct_roots_of_Δ₄_pos`. -/
theorem Δ₄_pos_iff_three_distinct_real_roots {a b c d : ℝ} (ha : a ≠ 0) :
    0 < Δ₄ a b c d ↔ HasThreeDistinctRealRoots a b c d :=
  ⟨three_distinct_roots_of_Δ₄_pos ha, Δ₄_pos_of_three_distinct_roots ha⟩

/-- The monic specialisation, which is what Theorems 1 and 2 would need. -/
theorem Δ₃_pos_iff_three_distinct_real_roots (b c d : ℝ) :
    0 < Δ₃ b c d ↔ HasThreeDistinctRealRoots 1 b c d := by
  rw [← Δ₄_one]
  exact Δ₄_pos_iff_three_distinct_real_roots one_ne_zero

/-! ## Theorems 1 and 2 in genuine root-count form

Combining the fully-proved volume computations with the equivalence above gives
the two theorems as statements about *roots*, with no discriminant in sight —
i.e. exactly the sentences of `reference/THEOREMS.md`. -/

/-- **THEOREM 1, root-count form, fully proved.**  The set of `(a,b,c) ∈ [-1,1]³`
for which `x³ + a x² + b x + c` has three distinct real roots has measure
`8 · (383/4860 + log 3 / 48)`; dividing by `vol([-1,1]³) = 8` gives the
probability `383/4860 + log 3 / 48`. -/
theorem theorem1_root_count :
    MeasureTheory.volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2.1 ∈ Icc (-1 : ℝ) 1 ∧
      p.2.2 ∈ Icc (-1 : ℝ) 1 ∧ HasThreeDistinctRealRoots 1 p.1 p.2.1 p.2.2}
      = ENNReal.ofReal ((383 / 4860 + Real.log 3 / 48) * 8) := by
  rw [← theorem1]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Δ₃_pos_iff_three_distinct_real_roots]

/-- **THEOREM 2, root-count form, fully proved.**  Same on `[0,1]³`, giving
probability `1/2880` (the unit cube has volume `1`). -/
theorem theorem2_root_count :
    MeasureTheory.volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2.2 ∈ Icc (0 : ℝ) 1 ∧ HasThreeDistinctRealRoots 1 p.1 p.2.1 p.2.2}
      = ENNReal.ofReal (1 / 2880) := by
  rw [← theorem2]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Δ₃_pos_iff_three_distinct_real_roots]

end NonmonicCubic
