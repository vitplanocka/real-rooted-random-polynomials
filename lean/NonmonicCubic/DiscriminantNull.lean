/-
# `{Δ₃ = 0}` is a null set

`OneRealRoot.lean` proves the dichotomy `N ∈ {1,3}` **off** `{Δ₄ = 0}`, and notes
that the hypothesis `Δ₄ ≠ 0` is not removable (`x³` has one real root and
`Δ₄ = 0`).  For the probabilistic statement that is no restriction, because
`{Δ₃ = 0}` is Lebesgue-null in `ℝ³`.  This file proves that.

The argument is the cheap one: for **fixed** `(a,b)` the discriminant

    Δ₃ a b c = −27 c² + (18ab − 4a³) c + (a²b² − 4b³)

is a genuine quadratic in `c` — its leading coefficient is the constant `−27` —
so it has at most two roots, a finite hence null set.  A set all of whose
`c`-sections are null is null, by `measure_prod_null_of_ae_null`.

Mathlib has no "the zero set of a nonzero multivariate polynomial is null"
(checked 2026-08-18: no file mentions both `MvPolynomial` and any measure
identifier), so the section argument is the route.  Here it is also the *easy*
route, since one variable already suffices.

Consequence (`ae_dichotomy`): almost every `(a,b,c)` gives a cubic with either
exactly one real root or three distinct real roots.
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Polynomial.Roots
import NonmonicCubic.OneRealRoot

namespace NonmonicCubic

open MeasureTheory Set

/-- For fixed `(a,b)`, `Δ₃ a b ·` is a quadratic with leading coefficient `−27`,
so it vanishes on a finite set. -/
theorem finite_setOf_Δ₃_eq_zero (a b : ℝ) : {c : ℝ | Δ₃ a b c = 0}.Finite := by
  set P : Polynomial ℝ := Polynomial.C (a ^ 2 * b ^ 2 - 4 * b ^ 3)
    + Polynomial.C (18 * a * b - 4 * a ^ 3) * Polynomial.X
    + Polynomial.C (-27) * Polynomial.X ^ 2 with hP
  have hcoeff : P.coeff 2 = -27 := by
    simp only [hP, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X]
    norm_num
  have hP0 : P ≠ 0 := fun h => by rw [h] at hcoeff; simp at hcoeff
  have hset : {c : ℝ | Δ₃ a b c = 0} = {c : ℝ | P.IsRoot c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hP, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    unfold Δ₃
    constructor <;> intro h <;> linear_combination h
  rw [hset]
  exact Polynomial.finite_setOfPred_isRoot hP0

/-- The vanishing locus of `Δ₃` is measurable: it is the preimage of `{0}` under
a polynomial, hence continuous, map. -/
theorem measurableSet_Δ₃_eq_zero :
    MeasurableSet {p : (ℝ × ℝ) × ℝ | Δ₃ p.1.1 p.1.2 p.2 = 0} := by
  have hc : Continuous fun p : (ℝ × ℝ) × ℝ => Δ₃ p.1.1 p.1.2 p.2 := by
    unfold Δ₃; fun_prop
  exact hc.measurable (measurableSet_singleton 0)

/-- **`{Δ₃ = 0}` is Lebesgue-null in `ℝ³`.**  Every `c`-section is finite. -/
theorem volume_Δ₃_eq_zero : volume {p : (ℝ × ℝ) × ℝ | Δ₃ p.1.1 p.1.2 p.2 = 0} = 0 := by
  rw [Measure.volume_eq_prod]
  refine Measure.measure_prod_null_of_ae_null measurableSet_Δ₃_eq_zero
    (Filter.Eventually.of_forall ?_)
  rintro ⟨a, b⟩
  exact (finite_setOf_Δ₃_eq_zero a b).measure_zero volume

/-- **Almost every monic cubic has either exactly one real root or three distinct
real roots.**  This is `OneRealRoot.exactlyOne_or_threeDistinct` with the
exceptional set discharged — the statement `N ∈ {1,3}` a.e. that the Kac–Rice
bookkeeping `E[N] = 1 + 2·P(N = 3)` rests on. -/
theorem ae_dichotomy :
    ∀ᵐ p : (ℝ × ℝ) × ℝ, HasExactlyOneRealRoot 1 p.1.1 p.1.2 p.2
      ∨ HasThreeDistinctRealRoots 1 p.1.1 p.1.2 p.2 := by
  have h := volume_Δ₃_eq_zero
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) h
  by_contra hcon
  exact hp (monic_exactlyOne_or_threeDistinct (by simpa using hcon))

end NonmonicCubic
