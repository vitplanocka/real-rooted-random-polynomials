# PROGRESS — Lean 4 / Mathlib formalization of the non-monic cubic theorem

Timestamps via `date '+%F %T'` (local).

---

## 2026-08-17 21:45:47 — Stage 0: environment sanity — DONE

- `lake build` on the bare template: **success**, 0.54s wall clock (4 jobs).
- `lakefile.toml` already requires `mathlib` at `rev = "v4.33.0"`;
  `lean-toolchain` = `leanprover/lean4:v4.33.0`. `lake update` had already been
  run by the operator (`lake-manifest.json` present, 9 packages under
  `.lake/packages/`).
- Mathlib `.olean` cache already populated: **8322** `.olean` files under
  `.lake/packages/mathlib/.lake/build/`. So `lake exe cache get` was already
  done; no re-download needed.
- `import Mathlib` compile check (`lake env lean` on a scratch file with
  `import Mathlib` + `#eval 1+1` → prints `2`): **success, 2.65s wall clock**.

**Wall-clock for Stage 0 this session: ~10 seconds** (everything was pre-warmed
by the operator). Data point for next time: with a populated olean cache,
`import Mathlib` costs ~2.6s per file invocation, which sets the floor for every
edit/compile cycle below.

---

## 2026-08-17 22:03:38 — Stage 1: Theorem 1 — **DONE, ZERO `sorry`**

Files: `NonmonicCubic/Basic.lean` (180 lines), `NonmonicCubic/Integrals.lean`
(156 lines), `NonmonicCubic/Theorem1.lean` (167 lines). Total 503 lines.

`lake build` output:
```
✔ [8709/8710] Built NonmonicCubic (4.8s)
Build completed successfully (8710 jobs).
```
Full-project build from a warm olean cache: **~5s**. Individual file check
(`lake env lean NonmonicCubic/Theorem1.lean`): 6.5s.

`#print axioms`:
```
'NonmonicCubic.theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem1_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.volume_T1Set' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only the three standard Lean axioms — **no `sorryAx`**. `grep -rn sorry
NonmonicCubic/` returns nothing.

### Statements proved

* `NonmonicCubic.theorem1` (`Theorem1.lean:142`):
  `volume {p : ℝ×ℝ×ℝ | p.1 ∈ Icc (-1) 1 ∧ p.2.1 ∈ Icc (-1) 1 ∧ p.2.2 ∈ Icc (-1) 1
   ∧ 0 < Δ₃ p.1 p.2.1 p.2.2} = ENNReal.ofReal ((383/4860 + Real.log 3/48) * 8)`
* `NonmonicCubic.theorem1_probability` (`Theorem1.lean:158`): the same as a
  probability, `(volume T1Set).toReal / (volume cube).toReal = 383/4860 + log 3/48`.

### One simplification vs. the informal proof, worth recording

`reference/THEOREMS.md` derives the band via the critical points `x₋, x₊` of
`g(x) = x³+ax²+bx` and identity S2. In Lean it is much cheaper to skip the
critical points entirely and use the single `ring`-provable identity

```
-27 * Δ₃ a b c = (27c - 9ab + 2a³)² - 4(a² - 3b)³      (Basic.lean:62)
```

which yields *both* branches at once:
* `a² - 3b < 0` ⟹ `Δ₃ < 0` (`Δ₃_neg_of_lt`, Basic.lean:120);
* `a² - 3b ≥ 0` ⟹ `Δ₃ = -27 (c - cLo)(c - cHi)` (`Δ₃_factor`, Basic.lean:96),
  hence `Δ₃ > 0 ↔ cLo < c < cHi` (`Δ₃_pos_iff`, Basic.lean:103),
with `cLo, cHi = (9ab - 2a³ ∓ 2(a²-3b)^{3/2})/27`. This is the *same* S1/S2
content, just obtained by completing the square instead of by symmetric
functions of `x₋, x₊`.

Similarly, the never-clipped lemma is not proved by the reference's
monotonicity argument (∂c_hi/∂a = −x₊² ≤ 0, then the edge a = −1) but from the
closed forms `27 cHi = (a-s)²(a+2s)`, `27 cLo = (a+s)²(a-2s)` (`cHi_eq`,
`cLo_eq`, Basic.lean:128,135): the whole lemma reduces to the scalar inequality
`(a-s)²(a+2s) ≤ 27` on `a ∈ [-1,1], s ∈ [0,2]` (`band_top_bound`,
Basic.lean:144), which `nlinarith` discharges with product hints. The equality
case `(a,s) = (-1,2)`, i.e. `(a,b) = (-1,-1)`, matches the reference's corner.

Both routes are the same mathematics; only the reference's *presentation* was
replaced, not its content. Nothing in the informal proof was found to be wrong.

### Numerical cross-check of the antiderivative (before writing it in Lean)

`F(x) = x(r⁵/6 + 5r³/8 + 45r/16) + (135/16) log(x+r)`, `r = √(x²+3)`, checked by
central differences at 6 points against `(x²+3)^{5/2}` (agreement ~1e-9, the
finite-difference floor), and `F(1)-F(-1) = 383/12 + (135/16) log 3`, giving
`P = 0.10169434037605886` vs `reference/THEOREMS.md`'s
`0.10169434037605886959954086…` — 16 digits.

---

## 2026-08-17 22:11:51 — Stage 2: Theorem 2 — **DONE, ZERO `sorry`**

File `NonmonicCubic/Theorem2.lean` (224 lines) plus 4 new sign lemmas appended to
`Basic.lean`. Whole project: 818 lines, `lake build` **success**, ~6s.

`#print axioms`:
```
'NonmonicCubic.theorem2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonmonicCubic.theorem2_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`. `grep -rn sorry NonmonicCubic/` → nothing.

Statements: `theorem2` (volume `= ENNReal.ofReal (1/2880)` on `[0,1]³`) and
`theorem2_probability` (same, divided by the unit cube's volume `1`).

### The one genuinely new difficulty vs. Theorem 1

In Theorem 1 the never-clipped lemma makes the slice of the cube *equal* to the
open region between the band edges. In Theorem 2 the window floor `c = 0` really
does clip (exactly on `b ≤ a²/4`, `cLo_nonpos`/`cLo_nonneg` in `Basic.lean`), and
then the slice and the open region `regionBetween (max cLo 0) cHi` are **not**
equal — they differ on `{c = 0}`, where the cube's slice contains points with
`Δ₃ > 0` (e.g. `Δ₃ a b 0 = b²(a²-4b) > 0`) that the open region excludes.
Handled by a sandwich (`region_subset_slice2`, `slice2_sdiff_subset`,
`volume_snd_eq_zero`, `volume_slice2`, Theorem2.lean:55–112) rather than a set
equality. This is a Lean-side bookkeeping point, not a gap in the informal proof
— the informal proof works with lengths of interval intersections, where the
endpoint is invisible.

The "small miracle" (all fractional powers cancelling) is `slice2_area`
(Theorem2.lean:118): the two `p52` values at `b = a²/4` and `b = 0` are
`(a/2)⁵` and `a⁵`, and after `integral_cHi_gen` + `integral_band_width_gen` the
whole thing is `19a⁵/12960 + a⁵/1620 = a⁵/480` by `ring`.
