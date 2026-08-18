/-
# The negative-discriminant half of the root-count bridge

`DiscriminantRootCount.lean` proves the classical fact

> `Δ₄ a b c d > 0  ↔  a x³ + b x² + c x + d` has three **distinct real** roots.

That is one half of the sign↔root-count dictionary.  This file supplies the
other half:

> for `a ≠ 0` and `Δ₄ a b c d ≠ 0`:
> `Δ₄ a b c d < 0  ↔  a x³ + b x² + c x + d` has **exactly one** real root.

The hypothesis `Δ₄ ≠ 0` is not removable: `x³` has exactly one real root and
`Δ₄ 1 0 0 0 = 0`.  It costs nothing in the intended application, where the
coefficients are drawn from a distribution absolutely continuous with respect to
Lebesgue measure and `{Δ₄ = 0}` is a null set.

## Why this is the missing piece

The Kac–Rice bridge for the number `N` of real roots of a random cubic reads
`p = (E[N] − 1)/2`, which is exactly the statement that `N ∈ {1, 3}` almost
surely with `N = 3` on the event whose probability is `p`.  Theorems 1–3 of this
development compute `P(Δ₃ > 0)`; `Δ₃_pos_iff_three_distinct_real_roots` turns
that into `P(N = 3)`.  `Δ₃_neg_iff_hasExactlyOneRealRoot` below turns the
complementary event into `P(N = 1)`, so the dichotomy `N ∈ {1,3}` off the null
set `{Δ₃ = 0}` is now machine-checked.

## The engine

Everything rests on one polynomial identity.  If `r` is a root of the cubic then
the cubic factors as `(t − r)·(a t² + B t + C)` with `B = b + a r`,
`C = c + b r + a r²`, and — this is the point —

    Δ₄ a b c d = f′(r)² · (B² − 4 a C)                                    (★)

where `f′(r) = 3 a r² + 2 b r + c`.  Both factors have a transparent meaning:
`f′(r)` vanishes iff `r` is a repeated root, and `B² − 4 a C` is the
discriminant of the remaining quadratic.  So `Δ₄ < 0` says precisely "`r` is a
simple root and the other two roots are non-real", which is the statement to be
proved.  `(★)` is `Δ₄_eq_at_root`, and it is a `linear_combination` — no case
analysis, no analysis at all.

The only genuinely analytic ingredient is the existence of *some* real root,
which is the intermediate value theorem applied between the explicit
far-out points supplied by `exists_le_cubic_neg` / `exists_ge_cubic_pos`.
Mathlib has no "a real polynomial of odd degree has a real root" lemma
(checked 2026-08-18), so `exists_real_root_cubic` proves the cubic case here.
-/
import NonmonicCubic.DiscriminantRootCount

namespace NonmonicCubic

open Set

/-- "`a x³ + b x² + c x + d` has exactly one real root", stated as a `∃!`. -/
def HasExactlyOneRealRoot (a b c d : ℝ) : Prop :=
  ∃! x : ℝ, a * x ^ 3 + b * x ^ 2 + c * x + d = 0

/-! ## The two algebraic identities at a root -/

/-- **Factorisation at a root.**  If `f r = 0` then
`f t = (t − r)(a t² + (b + a r) t + (c + b r + a r²))` for every `t`. -/
theorem cubic_factor_at_root {a b c d r : ℝ}
    (hr : a * r ^ 3 + b * r ^ 2 + c * r + d = 0) (t : ℝ) :
    a * t ^ 3 + b * t ^ 2 + c * t + d
      = (t - r) * (a * t ^ 2 + (b + a * r) * t + (c + b * r + a * r ^ 2)) := by
  linear_combination hr

/-- **Identity (★).**  At a root `r` the discriminant splits as
`Δ₄ = f′(r)² · (B² − 4aC)`, the square of the derivative times the discriminant
of the complementary quadratic. -/
theorem Δ₄_eq_at_root {a b c d r : ℝ}
    (hr : a * r ^ 3 + b * r ^ 2 + c * r + d = 0) :
    Δ₄ a b c d
      = (3 * a * r ^ 2 + 2 * b * r + c) ^ 2
        * ((b + a * r) ^ 2 - 4 * a * (c + b * r + a * r ^ 2)) := by
  unfold Δ₄
  linear_combination (27 * a ^ 3 * r ^ 3 + 27 * a ^ 2 * b * r ^ 2 + 27 * a ^ 2 * c * r
    - 27 * a ^ 2 * d + 18 * a * b * c - 4 * b ^ 3) * hr

/-- A real root of `a y² + B y + C` forces its discriminant to be a square,
hence nonnegative.  (`(2ay + B)² = B² − 4aC` on the nose.) -/
theorem discrim_nonneg_of_root {a B C y : ℝ} (hy : a * y ^ 2 + B * y + C = 0) :
    0 ≤ B ^ 2 - 4 * a * C := by
  have h : B ^ 2 - 4 * a * C = (2 * a * y + B) ^ 2 := by linear_combination (-4 * a) * hy
  rw [h]; positivity

/-! ## Existence of a real root -/

/-- **A real cubic with `a ≠ 0` has a real root.**  Mathlib has no odd-degree
version of this; here it is the intermediate value theorem between the explicit
points of `exists_le_cubic_neg` and `exists_ge_cubic_pos`. -/
theorem exists_real_root_cubic {a b c d : ℝ} (ha : a ≠ 0) :
    ∃ x : ℝ, a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  have key : ∀ a b c d : ℝ, 0 < a → ∃ x : ℝ, a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
    intro a b c d hpos
    obtain ⟨L, _, hLneg⟩ := exists_le_cubic_neg (b := b) (c := c) (d := d) hpos 0
    obtain ⟨R, _, hRpos⟩ := exists_ge_cubic_pos (b := b) (c := c) (d := d) hpos L
    have hcont : Continuous fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d := by fun_prop
    have hLR : L ≤ R := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [hLneg, hRpos]
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hLR hcont.continuousOn
      (show (0 : ℝ) ∈ Icc ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) L)
        ((fun t : ℝ => a * t ^ 3 + b * t ^ 2 + c * t + d) R) by
          simp only [Set.mem_Icc]; exact ⟨hLneg.le, hRpos.le⟩)
    exact ⟨x, hx⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · obtain ⟨x, hx⟩ := key (-a) (-b) (-c) (-d) (by linarith)
    exact ⟨x, by linarith [hx]⟩
  · exact key a b c d hpos

/-! ## `Δ₄ < 0` gives exactly one real root -/

/-- **`Δ₄ < 0` ⟹ at most one real root.**  Given one root `r`, identity (★)
forces the complementary quadratic to have negative discriminant, so it has no
real root; and every root other than `r` is a root of it. -/
theorem subsingleton_roots_of_Δ₄_neg {a b c d : ℝ} (h : Δ₄ a b c d < 0)
    {x y : ℝ} (hx : a * x ^ 3 + b * x ^ 2 + c * x + d = 0)
    (hy : a * y ^ 3 + b * y ^ 2 + c * y + d = 0) : x = y := by
  by_contra hne
  -- the discriminant of the quadratic left over after dividing by `(t - x)`
  set B := b + a * x with hB
  set C := c + b * x + a * x ^ 2 with hC
  have hfac : a * y ^ 2 + B * y + C = 0 := by
    have h0 := (cubic_factor_at_root hx y).symm.trans hy
    rcases mul_eq_zero.1 h0 with h1 | h2
    · exact absurd (by linarith [sub_eq_zero.1 h1] : x = y) hne
    · exact h2
  have hdisc : 0 ≤ B ^ 2 - 4 * a * C := discrim_nonneg_of_root hfac
  have hstar := Δ₄_eq_at_root hx
  have hsq : (0 : ℝ) ≤ (3 * a * x ^ 2 + 2 * b * x + c) ^ 2 := sq_nonneg _
  rw [hstar] at h
  nlinarith [h, hsq, hdisc]

/-- **`Δ₄ < 0` ⟹ exactly one real root.** -/
theorem hasExactlyOneRealRoot_of_Δ₄_neg {a b c d : ℝ} (ha : a ≠ 0)
    (h : Δ₄ a b c d < 0) : HasExactlyOneRealRoot a b c d := by
  obtain ⟨x, hx⟩ := exists_real_root_cubic (a := a) (b := b) (c := c) (d := d) ha
  exact ⟨x, hx, fun y hy => subsingleton_roots_of_Δ₄_neg h hy hx⟩

/-! ## The converse, and the dichotomy -/

/-- Three distinct real roots rule out having exactly one. -/
theorem not_hasExactlyOneRealRoot_of_three {a b c d : ℝ}
    (h : HasThreeDistinctRealRoots a b c d) : ¬ HasExactlyOneRealRoot a b c d := by
  obtain ⟨x, y, z, hxy, _, _, hfac⟩ := h
  rintro ⟨w, _, huniq⟩
  have hx : a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by rw [hfac x]; ring
  have hy : a * y ^ 3 + b * y ^ 2 + c * y + d = 0 := by rw [hfac y]; ring
  exact hxy ((huniq x hx).trans (huniq y hy).symm)

/-- **The negative half of the bridge.**  For `a ≠ 0` and `Δ₄ ≠ 0`,

    `Δ₄ a b c d < 0  ↔  a x³ + b x² + c x + d` has exactly one real root.

The hypothesis `Δ₄ ≠ 0` is necessary: `x³` has exactly one real root and
`Δ₄ 1 0 0 0 = 0`. -/
theorem Δ₄_neg_iff_hasExactlyOneRealRoot {a b c d : ℝ} (ha : a ≠ 0)
    (hΔ : Δ₄ a b c d ≠ 0) :
    Δ₄ a b c d < 0 ↔ HasExactlyOneRealRoot a b c d := by
  refine ⟨hasExactlyOneRealRoot_of_Δ₄_neg ha, fun hone => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  exact not_hasExactlyOneRealRoot_of_three
    (three_distinct_roots_of_Δ₄_pos ha (lt_of_le_of_ne hcon (Ne.symm hΔ))) hone

/-- **The dichotomy.**  Off the null set `{Δ₄ = 0}`, a real cubic has either
exactly one real root or three distinct real roots — never anything else.  This
is the statement `N ∈ {1, 3}` that the Kac–Rice bridge `p = (E[N] − 1)/2`
requires. -/
theorem exactlyOne_or_threeDistinct {a b c d : ℝ} (ha : a ≠ 0) (hΔ : Δ₄ a b c d ≠ 0) :
    HasExactlyOneRealRoot a b c d ∨ HasThreeDistinctRealRoots a b c d := by
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · exact Or.inl (hasExactlyOneRealRoot_of_Δ₄_neg ha hneg)
  · exact Or.inr (three_distinct_roots_of_Δ₄_pos ha hpos)

/-- The two alternatives of `exactlyOne_or_threeDistinct` are exclusive. -/
theorem not_both_exactlyOne_and_three {a b c d : ℝ} :
    ¬ (HasExactlyOneRealRoot a b c d ∧ HasThreeDistinctRealRoots a b c d) :=
  fun ⟨h1, h3⟩ => not_hasExactlyOneRealRoot_of_three h3 h1

/-! ## Monic specialisations

These are the forms Theorems 1–3 of this development speak in. -/

/-- Monic form of `Δ₄_neg_iff_hasExactlyOneRealRoot`. -/
theorem Δ₃_neg_iff_hasExactlyOneRealRoot {b c d : ℝ} (hΔ : Δ₃ b c d ≠ 0) :
    Δ₃ b c d < 0 ↔ HasExactlyOneRealRoot 1 b c d := by
  rw [← Δ₄_one]
  exact Δ₄_neg_iff_hasExactlyOneRealRoot one_ne_zero (by rwa [Δ₄_one])

/-- Monic form of the dichotomy: off `{Δ₃ = 0}`, the monic cubic
`x³ + b x² + c x + d` has exactly one real root or three distinct real roots. -/
theorem monic_exactlyOne_or_threeDistinct {b c d : ℝ} (hΔ : Δ₃ b c d ≠ 0) :
    HasExactlyOneRealRoot 1 b c d ∨ HasThreeDistinctRealRoots 1 b c d :=
  exactlyOne_or_threeDistinct one_ne_zero (by rwa [Δ₄_one])

end NonmonicCubic
