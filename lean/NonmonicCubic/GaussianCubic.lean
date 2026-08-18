/-
# Problem A (monic cubic, Gaussian coefficients): the algebraic core, formalized

For `(a,b,c)` i.i.d. `N(0,1)`,

    P(x³ + a x² + b x + c has three real roots)
      = (1/π) ∫₀^∞ exp(−x⁴(x⁴+4x²+9)/(2(x⁴+4x²+1)))
                   · 2(x⁴+6x²+3)/(√(x⁴+4x²+1)(x⁴+4x²+9)) dx

(established numerically to 79 agreeing digits against an independent quadrature;
see `~/math/open-problems/VERDICT.md`).

**Scope of this file.**  The *probabilistic* content — the Kac–Rice/Rice
level-crossing formula and the Owen's-`T` cancellation — is far beyond what is
reasonable to formalize here.  What *is* formalized is the complete **algebraic
skeleton** the derivation rests on: every identity that was checked in `sympy`
during verification is re-proved here by `ring`, plus the one genuine calculus
step (`h′`).  So the parts of the argument that are pure algebra are now
machine-checked rather than CAS-checked.

Setup.  With `w(x) = (x², x, 1)` and `q(x) = ‖w(x)‖² = x⁴+x²+1`, the unit vector
`u = w/√q` gives `f(x) = x³ + √q(x)·Z(x)` for `Z = (a,b,c)·u`, so the real roots
of `f` are the crossings of the moving level `−h`, `h = x³/√q`.
-/
import NonmonicCubic.Basic

namespace NonmonicCubic.GaussianCubic

open Real

/-- `q(x) = ‖(x²,x,1)‖² = x⁴+x²+1`. -/
def qA (x : ℝ) : ℝ := x ^ 4 + x ^ 2 + 1

theorem qA_pos (x : ℝ) : 0 < qA x := by
  unfold qA; positivity

theorem qA_ne_zero (x : ℝ) : qA x ≠ 0 := ne_of_gt (qA_pos x)

/-! ## 1. `u = w/√q` is a unit vector, and `Z ⟂ Z′` -/

/-- `‖w‖² = q`: the normalisation that makes `Z(x) ~ N(0,1)` pointwise. -/
theorem normSq_w (x : ℝ) : (x ^ 2) ^ 2 + x ^ 2 + 1 ^ 2 = qA x := by
  unfold qA; ring

/-- `w · w′ = q′/2`.  Together with `‖w‖² = q` this is what forces
`u · u′ = ½(‖u‖²)′ = 0`, i.e. **`Z` and `Z′` are independent** — the fact that
makes the conditional expectation in Rice's formula factorise. -/
theorem dot_w_dw (x : ℝ) :
    (x ^ 2) * (2 * x) + x * 1 + 1 * 0 = (4 * x ^ 3 + 2 * x) / 2 := by
  ring

/-! ## 2. The variance of `Z′` -/

/-- **The `v²` identity, cleared of denominators.**  Since
`‖u′‖² = (4q‖w′‖² − (q′)²)/(4q²)` with `‖w′‖² = 4x²+1` and `q′ = 4x³+2x`, the
claim `‖u′‖² = (x⁴+4x²+1)/q²` is exactly this polynomial identity. -/
theorem key_v2 (x : ℝ) :
    4 * qA x * (4 * x ^ 2 + 1) - (4 * x ^ 3 + 2 * x) ^ 2 = 4 * (x ^ 4 + 4 * x ^ 2 + 1) := by
  unfold qA; ring

/-- `v(x)² := ‖u′(x)‖² = (x⁴+4x²+1)/q(x)²`, in the divided form. -/
theorem v_sq_eq (x : ℝ) :
    (4 * qA x * (4 * x ^ 2 + 1) - (4 * x ^ 3 + 2 * x) ^ 2) / (4 * qA x ^ 2)
      = (x ^ 4 + 4 * x ^ 2 + 1) / qA x ^ 2 := by
  rw [key_v2]
  field_simp

/-! ## 3. The exponent: equation (7) -/

/-- **Equation (7)**, cleared of denominators: with `h = x³/√q`, `z = h′/v`,

    h² + z² = x⁴(x⁴+4x²+9)/(x⁴+4x²+1).

After clearing, this is the polynomial identity below. -/
theorem key_eq7 (x : ℝ) :
    x ^ 2 * (x ^ 4 + 4 * x ^ 2 + 1) + (x ^ 4 + 2 * x ^ 2 + 3) ^ 2
      = qA x * (x ^ 4 + 4 * x ^ 2 + 9) := by
  unfold qA; ring

/-! ## 4. The amplitude: equation (8) -/

/-- **Equation (8)**, cleared of *both* nested radicals.  The claim

    v + θ′ = 2(x⁴+6x²+3) / (√(x⁴+4x²+1)·(x⁴+4x²+9)),   θ = arctan(z/h),

is equivalent, after squaring, to the polynomial identity below; both
pre-squared sides have all-positive coefficients, hence are positive for `x > 0`,
so squaring loses nothing.

This is the step a CAS could *not* close symbolically during verification (it
would not collapse the nested radicals); reducing it to this identity is what
made it exact rather than numerical. -/
theorem key_eq8 (x : ℝ) :
    (x ^ 4 + 4 * x ^ 2 + 1) * (x ^ 8 + 7 * x ^ 6 + 10 * x ^ 4 + 9 * x ^ 2 + 3) ^ 2
      = (x ^ 4 + 6 * x ^ 2 + 3) ^ 2
        * (x ^ 12 + 6 * x ^ 10 + 12 * x ^ 8 + 16 * x ^ 6 + 12 * x ^ 4 + 6 * x ^ 2 + 1) := by
  ring

/-- Both pre-squared sides of `key_eq8` are positive for `x > 0`, so the square
root branch is the right one. -/
theorem eq8_sides_pos {x : ℝ} (hx : 0 < x) :
    0 < x ^ 8 + 7 * x ^ 6 + 10 * x ^ 4 + 9 * x ^ 2 + 3 ∧
    0 < x ^ 4 + 6 * x ^ 2 + 3 := by
  constructor <;> positivity

/-! ## 5. The one genuine calculus step: `h′` -/

/-- `h(x) = x³/√(q(x))`. -/
noncomputable def hA (x : ℝ) : ℝ := x ^ 3 / Real.sqrt (qA x)

/-- **`h′ = x²(x⁴+2x²+3)/q^{3/2}`**, written as `… / (q·√q)`.

This is the only step of the algebraic skeleton that is not a polynomial
identity, and it is what feeds `z = h′/v` in equations (7) and (8). -/
theorem hasDerivAt_hA (x : ℝ) :
    HasDerivAt hA (x ^ 2 * (x ^ 4 + 2 * x ^ 2 + 3) / (qA x * Real.sqrt (qA x))) x := by
  have hq : (0 : ℝ) < qA x := qA_pos x
  have hs : (0 : ℝ) < Real.sqrt (qA x) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (qA x) ^ 2 = qA x := Real.sq_sqrt hq.le
  have hinner : HasDerivAt qA (4 * x ^ 3 + 2 * x) x := by
    unfold qA
    simpa using ((((hasDerivAt_id x).fun_pow 4).add ((hasDerivAt_id x).fun_pow 2)).add_const 1)
  have hden : HasDerivAt (fun y => Real.sqrt (qA y))
      ((4 * x ^ 3 + 2 * x) / (2 * Real.sqrt (qA x))) x := hinner.sqrt (ne_of_gt hq)
  have hnum : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_id x).fun_pow 3
  refine ((hnum.div hden (ne_of_gt hs)).congr_deriv ?_)
  have h1 : Real.sqrt (qA x) ≠ 0 := ne_of_gt hs
  field_simp
  rw [hsq]
  unfold qA
  ring

/-! ## 6. Equation (9): the external derivation's discriminant form is ours -/

/-- **Equation (9)** of the external derivation,
`Δ = −27(c − ab/3 + 2a³/27)² + (4/27)(a²−3b)³`, is *literally* the discriminant
`Δ₃` this project already formalized — so that half of the cross-check needs no
new content, only this identification. -/
theorem eq9_eq_Δ₃ (a b c : ℝ) :
    -27 * (c - a * b / 3 + 2 * a ^ 3 / 27) ^ 2 + (4 / 27) * (a ^ 2 - 3 * b) ^ 3
      = Δ₃ a b c := by
  unfold Δ₃; ring

/-- Consistency with the completed square already proved in `Basic.lean`. -/
theorem eq9_consistent (a b c : ℝ) :
    -27 * (-27 * (c - a * b / 3 + 2 * a ^ 3 / 27) ^ 2 + (4 / 27) * (a ^ 2 - 3 * b) ^ 3)
      = (27 * c - 9 * a * b + 2 * a ^ 3) ^ 2 - 4 * (a ^ 2 - 3 * b) ^ 3 := by
  rw [eq9_eq_Δ₃]
  exact disc_completeSquare a b c

end NonmonicCubic.GaussianCubic
