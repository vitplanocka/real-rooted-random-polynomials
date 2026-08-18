# REPORT — Lean 4 / Mathlib formalization of the non-monic cubic theorem

Session of 2026-08-17 22:00 – 2026-08-18 00:20 local.
Toolchain `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0` from a pre-warmed
`.olean` cache.

## Bottom line

**All three theorems are fully proved, with zero `sorry`, plus the classical
discriminant↔root-count bridge that Mathlib was missing.**

`lake build` succeeds with **no errors and no warnings of any kind**. The string
`sorry` does not occur anywhere in `NonmonicCubic/` except in one docstring
saying so. `#print axioms` on every headline theorem returns exactly
`[propext, Classical.choice, Quot.sound]` — the three standard Lean axioms, no
`sorryAx`, nothing exotic.

3780 lines across 7 files; full rebuild from a warm Mathlib cache: **55 s**.

---

## Summary table

| Stage | Deliverable | Status | `sorry` |
|---|---|---|---|
| 0 | environment | **DONE** (~10 s; cache pre-warmed) | — |
| 1 | Theorem 1, `[-1,1]³`, `383/4860 + ln3/48` | **DONE** | **0** |
| 2 | Theorem 2, `[0,1]³`, `1/2880` | **DONE** | **0** |
| 3 | Theorem 3 statement | **DONE**, cross-checked against Mathlib's own `Cubic.discr` | **0** |
| 4 | Theorem 3 proof, elementary route | **DONE** | **0** |
| 5 | `sign Δ` ↔ real-root count | **DONE** — closes a genuine Mathlib gap | **0** |

| file | lines | `sorry` |
|---|---|---|
| `NonmonicCubic/Basic.lean` | 234 | **0** |
| `NonmonicCubic/Integrals.lean` | 202 | **0** |
| `NonmonicCubic/Theorem1.lean` | 159 | **0** |
| `NonmonicCubic/Theorem2.lean` | 224 | **0** |
| `NonmonicCubic/Theorem3Statement.lean` | 103 | **0** |
| `NonmonicCubic/Theorem3Proof.lean` | 2548 | **0** |
| `NonmonicCubic/DiscriminantRootCount.lean` | 310 | **0** |

---

## The headline theorems

```lean
-- Theorem 1                                           Theorem1.lean:132, :149
theorem theorem1 :
    volume {p : ℝ×ℝ×ℝ | p.1 ∈ Icc (-1) 1 ∧ p.2.1 ∈ Icc (-1) 1 ∧ p.2.2 ∈ Icc (-1) 1
      ∧ 0 < Δ₃ p.1 p.2.1 p.2.2}
      = ENNReal.ofReal ((383 / 4860 + Real.log 3 / 48) * 8)
theorem theorem1_probability : … = 383 / 4860 + Real.log 3 / 48

-- Theorem 2                                           Theorem2.lean:202, :217
theorem theorem2 : … = ENNReal.ofReal (1 / 2880)
theorem theorem2_probability : … = 1 / 2880

-- Theorem 3                                    Theorem3Proof.lean:2532, :2537
theorem theorem3 :
    volume T3Set = ENNReal.ofReal ((641 / 2430 - Real.log 3 / 24) * 16)
theorem theorem3_probability : … = 641 / 2430 - Real.log 3 / 24

-- Stage 5: the classical bridge                DiscriminantRootCount.lean:270
theorem Δ₄_pos_iff_three_distinct_real_roots {a b c d : ℝ} (ha : a ≠ 0) :
    0 < Δ₄ a b c d ↔ HasThreeDistinctRealRoots a b c d

-- …and Theorems 1 and 2 restated about roots, no discriminant in sight
theorem theorem1_root_count :                 -- DiscriminantRootCount.lean:290
    volume {p | p ∈ [-1,1]³ ∧ HasThreeDistinctRealRoots 1 p.1 p.2.1 p.2.2}
      = ENNReal.ofReal ((383 / 4860 + Real.log 3 / 48) * 8)
theorem theorem2_root_count : … = ENNReal.ofReal (1 / 2880)   -- :301
```

`Δ₄_eq_cubic_discr` (`Theorem3Statement.lean:61`) proves by `ring` that our `Δ₄`
is **literally Mathlib's own** `Cubic.discr ⟨a,b,c,d⟩`, so the Theorem 3
statement is checked against Mathlib and not only against the prose.

---

## Findings about the reference material

Nothing in `THEOREMS.md` or `VERDICT.md` was found to be wrong; every claim
checked independently reproduced (§D). Two findings concern `TASK.md` itself,
and one is a piece of mathematics the reference does not state.

### A. `TASK.md`'s Stage-4 steer is based on a misreading of the reference

`TASK.md` says to prefer "`VERDICT.md`'s route 1 … computes the same answer by
nested integration … Every step is `intervalIntegral` of an explicit
piecewise-elementary function", and to read `src/route1_closed_a.py` because "it
IS the integrand".

**Route 1 is a numerical route and does not produce a closed form.** Three
confirmations inside the reference itself:

1. `VERDICT.md`'s results table lists route 1 as `0.21801049620261477102`
   agreeing to `7.0e-20` — a 19-digit *numerical* agreement, not an identity; the
   "exact symbolic" row is route 2.
2. `route1_closed_a.py`'s own docstring: only the innermost `a`-integral is
   closed-form; the remaining `(b, σ)` double integral is tanh-sinh /
   Gauss-Legendre with bisected breakpoints.
3. `VERDICT.md`, "a negative result worth recording", states that this
   integration order "leaves integrals of algebraic functions of the roots of a
   cubic whose coefficients move with the outer variable, which is not
   elementary in general", with PSLQ finding no closed form for `V(1/2)`, `V(1/3)`.

The `L1`/`L2`/`F(s)` material `TASK.md` cites is `VERDICT.md`'s **route 2** face
integral `S_b`, not route 1. Stage 4 here formalizes route 2.

### B. The cone step needs no divergence theorem — and this is now proved

`TASK.md` steers away from route 2 because it "needs Stokes'/divergence-theorem
machinery on a region with a non-smooth (cusped) boundary". That concern does
not apply, and the Lean development demonstrates it concretely.

`volume_conePiece1` (`Theorem3Proof.lean:399`) — the whole content of the cone
step — says: for **any** measurable cone `R ⊆ ℝ⁴`, the piece of `[-1,1]⁴` where
coordinate 1 attains `max_j |x_j|` positively has volume `(1/4)·vol₃(face)`. The
proof slices at `x₁ = t`, uses homogeneity of `R` to identify the slice with
`t · face`, and integrates `∫₀¹ t³ dt = 1/4`. That is **Fubini plus the scaling
law `vol₃(t·E) = t³ vol₃(E)`** — there is no boundary integral anywhere, so the
cusps of `{Δ₄ = 0}` never enter, and no smoothness of `∂R` is used.

The other seven pieces follow from it by measure-preserving coordinate maps built
from the two `ring`-provable symmetries of `Δ₄` (`Δ₄_neg`, `Δ₄_reverse`).

### C. A small identity that made the face computation clean

Formalizing forced out a fact the reference does not state. For `a > 0`,

    a₀(√(1−3ac)) = |(1−3ac) − 1| / 3 = |−3ac| / 3 = a·|c|          (a0_sOf)

so the window constraint `|c| ≤ 1` is **exactly** `a₀ s ≤ a` — which is exactly
the hypothesis under which `L1` says the band never clips above, and exactly the
condition defining the region of the Tonelli swap. The `(a,c)` and `(a,s)`
pictures line up with no case analysis at all.

### D. Independent numerical re-verification done in this session

Not taken on trust from the reference:

| checked | this session | reference | agreement |
|---|---|---|---|
| Theorem 1 antiderivative | central differences, 6 points | `(x²+3)^{5/2}` | ~1e-9 (FD floor) |
| Theorem 1 value | `0.10169434037605886` | `0.10169434037605886959954086…` | 16 digits |
| `F(2/3±)` continuity | `0.61805212619…`, `0.61805212620…` | `11264/18225` | 11 digits |
| `S_b = (4/3)∫₀² sF(s)ds` | `2.6746132162333494` | `1454/405 − (5/6)log3` | `−1.6e-14` |
| `P = (V(1)+S_b)/16` | `0.21801049620261376` | `641/2430 − log3/24` | `−1.0e-15` |

The `S_b` check used Gauss–Legendre with geometrically graded panels around the
integrable log singularity at `s = 1`; a naive Simpson rule saturates at ~1e-5
there — a small live demonstration of exactly the hazard `VERDICT.md`'s
post-mortem warns about.

### E. A statement of mine that was false, caught by trying to prove it

`Fs_eq_face_integral` was first written with hypotheses `0 < s`, `s < 2` only.
That is **false at `s = 1`**: there `a₀ = 0`, the integrand behaves like `1/a`,
and the integral genuinely diverges, so both sides collapse to unrelated Lean
junk values (`Fs 1 = 23/54` via `0/0 = 0` and `log 0 = 0`; a non-integrable
`intervalIntegral` is `0`). Verified in Lean, not merely asserted. The fix is a
genuine `s ≠ 1` hypothesis, harmless downstream since `{1}` is null. **A `sorry`d
lemma is an unchecked *claim*, not just an unfinished proof.**

---

## How the proofs go

### Theorems 1 and 2 — one `ring` identity does the work

`THEOREMS.md` derives the admissible `c`-band from the critical points of
`g(x) = x³+ax²+bx`. In Lean it is far cheaper to complete the square:

    -27 · Δ₃(a,b,c) = (27c − 9ab + 2a³)² − 4(a² − 3b)³        (Basic.lean:64)

which yields both branches at once — `b > a²/3 ⟹ Δ₃ < 0`, and otherwise
`Δ₃ > 0 ↔ cLo < c < cHi` with `cLo, cHi = (9ab − 2a³ ∓ 2(a²−3b)^{3/2})/27`. The
never-clipped lemma then reduces to the scalar inequality `(a−s)²(a+2s) ≤ 27` on
`a ∈ [−1,1], s ∈ [0,2]`, equality exactly at `(a,s) = (−1,2)` — the reference's
corner. Same mathematics, much less Lean.

Theorem 2's extra difficulty is that the window floor `c = 0` really does clip,
so the cube's slice and the open region between the clipped edges are **not**
equal — they differ on `{c = 0}`, handled by a sandwich rather than a set
equality. (A Lean bookkeeping point, not a gap in the informal proof.)

### Theorem 3 — route 2, in five stages

1. **Cone/face identity** `vol₄ = S_a + S_b` (`volume_T3Set_eq_faces`, :1178).
   Radial identity per piece (§B), eight pieces partitioning `[-1,1]⁴` off the
   null set of the twelve hyperplanes `x_i = ±x_j` (`volume_T3Set_sum`, :1112),
   collapsed to two by the `Δ₄` symmetries.
2. **`S_a = V(1)`** (`volume_FaceA`, :266) — the `a = 1` face *is* Theorem 1's
   region, via `Δ₄_one`. Free.
3. **The face `b = 1`**: the `d`-band from the degree-4 completed square, the
   clipping lemmas `L1`/`L2`, the substitution `c = (1−s²)/(3a)`, and **the
   Tonelli swap** (`lintegral_faceRegion_swap`, :1775) that lets `a` be
   integrated first at fixed `s` — `VERDICT.md`'s "this is the move". Done in
   `ℝ≥0∞`, so measurability only, no integrability side conditions.
4. **`F(s)`** (`Fs_eq_face_integral`, :1213) — the inner `a`-integral in closed
   form, both clipping regimes.
5. **`∫₀² s F(s) ds = 727/270 − (5/8) log 3`** (`integral_s_Fs`, :1667), hence
   `S_b = 1454/405 − (5/6) log 3`. **This is where Theorem 3's `log 3` comes
   from.** Both branches of `F` are put in `a₀`-free, `α₋`-free form; the
   apparent singularity of `K₊/(54a₀²)` at `s = 1` cancels because `K₊` and `a₀²`
   share the factor `(s−1)²`; the surviving `−s·log(s−1)` is integrable, handled
   with `Real.continuous_mul_log` (continuity of `x log x` *at 0*) and the
   unconditional `intervalIntegrable_log'`.
   *Internal check that fell out*: each half separately produces a `log 5`
   (`±(1/2)log 5`) and they cancel exactly — `log 5` is not in the answer.

### Stage 5 — the Mathlib gap

Mathlib has `Cubic.discr` and `Cubic.discr_ne_zero_iff_roots_nodup`, but those
concern `discr ≠ 0` and distinctness *over a splitting field* — nothing about
signs or realness. The degree-2 analogue (`discrim`) has the sign story, but only
in degree 2. Proved here from scratch: the completed square forces
`p = b²−3ac > 0`; at the points where `3at+b = ∓√p` the identity
`27a²·f t = u³ − 3pu + q` gives values `q ± 2p^{3/2}` whose **product** is
`−27a²Δ₄ < 0` and whose **difference** is `4p^{3/2} > 0`; IVT on three intervals
gives three roots; three distinct roots force the factorisation by linear algebra
on the quadratic remainder. No derivatives appear — the "critical points" are
just explicit numbers.

---

## Notes for future Mathlib work on this codebase

* **`lake build` runs the mathlibStandardSet linters; `lake env lean` does not.**
  Use `lake build` as the authoritative check — the long-line and
  `show`-vs-`change` lints are invisible to the other.
* `lake` must run with the project as cwd. From inside `.lake/packages/mathlib`
  it tries to build *Mathlib's* dependency tree and clones ~57 MB into the
  package directory. Grep Mathlib with absolute paths instead of `cd`-ing there.
* `volume` on `ℝ×ℝ×ℝ` (and `ℝ⁴`) is **not** an `IsAddHaarMeasure` instance out of
  the box; the only missing piece is `IsAddLeftInvariant`, and
  `(inferInstance : ((volume : Measure ℝ).prod volume).IsAddLeftInvariant)`
  supplies it. That unlocks `Measure.addHaar_smul_of_nonneg` and
  `Measure.addHaar_submodule`.
* Coordinate permutations of `ℝ⁴` are cheap: reassociate to `(ℝ×ℝ)×(ℝ×ℝ)` with
  `volume_preserving_prodAssoc`, permute with `Prod.swap`/`Prod.map`
  (`Measure.measurePreserving_swap`), reassociate back, `funext x; rfl`. Reversal
  `(a,b,c,d) ↦ (d,c,b,a)` is `Prod.swap ∘ Prod.map Prod.swap Prod.swap` there —
  four steps, not six adjacent transpositions.
* Tonelli in `ℝ≥0∞` (`lintegral_lintegral_swap`) is far cheaper than Fubini in
  `ℝ`: measurability only. Swap orders there, convert afterwards with
  `ofReal_integral_eq_lintegral_ofReal`.
* Names absent in this Mathlib (all cost time): `div_add_div_same`, `inf_eq_min`,
  `ContinuousAt.min`, `abs_lt_abs_of_sq_lt_sq`, `div_le_div_iff`, `Ne.lt_or_lt`.
  Renamed: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `measure_diff_null` →
  `measure_sdiff_null`, `Set.diff_eq_empty` → `Set.sdiff_eq_empty`; `push_neg` is
  deprecated in favour of `push Not`.
* Interval-integral notation extends to the right: `∫ s in a..b, f s + ∫ …`
  parses as `∫ s in a..b, (f s + ∫ …)`. Parenthesise sums of integrals.
* `set F := … with h` then `rw [h]` does **not** beta-reduce; add
  `have hApp : ∀ …, F a b = … := fun _ _ => rfl` and rewrite with that.
* `ℝ≥0∞` needs `open scoped ENNReal`; set-scalar `t • E` needs
  `open scoped Pointwise`.
