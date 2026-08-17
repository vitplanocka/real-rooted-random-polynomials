# TASK: Formalize the non-monic cubic theorem in Lean 4 / Mathlib

*Briefing for the server Claude instance. Written 2026-08-17 by the session that
proved Theorems 1–3 (informally, in Python: sympy + mpmath + Monte Carlo). This
is a Lean 4 formalization project against Mathlib. Work autonomously in this
project folder (`~/math/nonmonic-cubic-lean/nonmonic_cubic/`).*

## Mission

Formalize, and prove as much as is genuinely tractable of, this theorem:

> **Theorem 3.** Let (a,b,c,d) be i.i.d. uniform on [−1,1]. Then
> P( a x³ + b x² + c x + d has three real roots ) = 641/2430 − ln(3)/24.

The full informal proof, with every step, is in `THEOREMS.md` and `VERDICT.md`
in this repo (copied into this project's `reference/` folder — read them before
writing any Lean). **Do not re-derive the mathematics from scratch**: the job is
translation and formal verification of an already-checked argument, not new
research. If you find the informal proof is actually wrong somewhere, that is a
genuinely interesting finding — stop, double check very carefully (it has 5
independent numerical confirmations already), and report it clearly rather than
silently "fixing" the Lean side to paper over a mismatch.

## Why this is worth doing, and what "done" looks like

A fully machine-checked, zero-`sorry` proof of Theorem 3 end-to-end is a
serious undertaking — plausibly not achievable in one session. That is fine.
**The primary deliverable is a formal statement that is unmistakably a correct
transcription of Theorem 3 and type-checks with zero errors.** Everything past
that is a bonus, staged by difficulty. Report exactly which stage you reached,
with file:line references, and never claim a stage is "done" if it has a
`sorry` unless you say so explicitly next to the claim.

## Staged plan (do these in order; each stage is a checkpoint)

### Stage 0 — environment sanity
Confirm `lake build` succeeds on the bare template, then add Mathlib as a
dependency (`require mathlib from git "https://github.com/leanprover-community/mathlib4"`
at a version matching your toolchain — check `lean-toolchain`), run
`lake update`, then **`lake exe cache get`** to pull prebuilt `.olean` files
(this avoids a many-hour from-scratch Mathlib build; it should be available as
a Lake script once Mathlib is a dependency). Confirm `import Mathlib` compiles.
Log wall-clock time for this step in PROGRESS.md — it's useful data for next
time.

### Stage 1 — warm-up: formalize and fully prove Theorem 1 (no `sorry`)
> P( x³ + ax² + bx + c has 3 real roots ) = 383/4860 + ln(3)/48, (a,b,c) iid U[−1,1].

This is the simplest of the three theorems and its informal proof
(`THEOREMS.md`, "Proof of Theorem 1") is fully elementary: an explicit double
integral of `(4/27)(a²−3b)^(3/2)` over a triangular-ish region, no case splits
beyond the single never-clipped lemma. Formalize:
- `Δ₃ : ℝ → ℝ → ℝ → ℝ`, the cubic discriminant `18abc − 4a³c + a²b² − 4b³ − 27c²`
  (matches `src/exact_anchors.py`'s `disc` — check it against that file).
- The volume statement: something like
  `MeasureTheory.volume {p : ℝ × ℝ × ℝ | p ∈ Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1 ∧ Δ₃ p.1 p.2.1 p.2.2 > 0} = ENNReal.ofReal ((383/4860 + Real.log 3 / 48) * 8)`
  (volume of the cube [−1,1]³ is 8; state the theorem however is most natural
  in Mathlib idiom — this is illustrative, not prescriptive).
- Prove it by direct computation: Fubini/Tonelli to reduce to iterated
  `intervalIntegral`s, then compute each one explicitly (power rule for the
  `(a²−3b)^{3/2}` term, `Real.arsinh`/`Real.log` for the final step — Mathlib
  has `intervalIntegral` lemmas for polynomials and should have enough real
  analysis for `∫ (a²+3)^{5/2}` type integrals via substitution; you may need
  to build up some auxiliary lemmas by hand).
- **Search Mathlib's actual source** (it will be on disk after `cache get`,
  under `.lake/packages/mathlib/Mathlib/...`) for the exact names of relevant
  lemmas rather than guessing from memory — `grep -r` for `intervalIntegral`,
  `MeasureTheory.volume_Icc`, `MeasureTheory.integral_prod`, `Real.arsinh`,
  etc. Wrong/hallucinated lemma names are the single most likely way to waste
  time here.

Getting Theorem 1 to compile with **zero `sorry`** is the single most valuable
checkpoint in this whole task — it validates the whole toolchain, the
statement style, and the integration techniques you'll reuse for Theorem 3.
Do not move to Stage 2 until this compiles clean. Report the compile time and
line count.

### Stage 2 — Theorem 2 (no `sorry`, should be fast given Stage 1)
> P( x³ + ax² + bx + c has 3 real roots ) = 1/2880, (a,b,c) iid U[0,1].

Same discriminant, unit cube, and (per `THEOREMS.md`) the inner integral
collapses to the polynomial a⁵/480 — likely *easier* to formalize than
Theorem 1 since there's no `arsinh`/`log`, just polynomial integration. Reuse
Stage 1's machinery.

### Stage 3 — Theorem 3 statement (must succeed; this is the deliverable if
### nothing past this point compiles)
Formalize the precise statement:
- `Δ₄ : ℝ → ℝ → ℝ → ℝ → ℝ`, `18abcd − 4b³d + b²c² − 4ac³ − 27a²d²` (check
  against `src/nonmonic_mc.py`'s `quartic_all_real`... no, wait, that's for
  the quartic. Check against `VERDICT.md`'s stated Δ formula directly, and
  against the classical cubic discriminant formula in the "primer" reference
  box described in `reference/artifact-primer-box.md` if present).
- The volume statement over `[-1,1]⁴`, target value `641/2430 − ln(3)/24`.
- This alone — a statement that type-checks and is manifestly the right
  translation (get a second pass checking it against the informal statement
  word by word) — is valuable even with the whole proof `sorry`d out. Do not
  skip carefully re-checking this against `VERDICT.md`'s exact wording.

### Stage 4 — Theorem 3 proof, elementary route (attempt; `sorry` allowed)

**Important strategic steer**: `VERDICT.md`'s actual proof route uses the
divergence theorem on a cone (Δ is homogeneous of degree 4). That is
mathematically the cleanest route but is likely much harder to formalize in
Lean than a direct, fully elementary iterated-integral computation, because it
needs Stokes'/divergence-theorem machinery on a region with a non-smooth
(cusped) boundary. **Prefer the elementary route instead**: `VERDICT.md`'s
"route 1" (no face decomposition, no divergence theorem) computes the same
answer by nested nested integration — condition on the leading coefficient a,
substitute σ = √(b²−3ac), integrate a out first in closed form, then σ, then b.
Every step is `intervalIntegral` of an explicit piecewise-elementary function
(polynomials, one `log`). This is much closer in spirit to what you'll have
just built for Theorem 1/2, and is the route to formalize. The full derivation
is in `VERDICT.md`'s "route 1 restructured" log entries and `src/route1_closed_a.py`
(read the code — it IS the integrand, just in Python).

Break this into sub-lemmas the way the informal proof does (L1, L2, the
piecewise F(s), etc. — `VERDICT.md`'s "How the closed form is obtained"
section is essentially already a Lean proof outline in prose). Prove each
sub-lemma. If a specific piece resists full proof (most likely candidate: the
piecewise case split on `s ≤ 2/3` vs `2/3 < s < 2`, or the final `∫ s F(s) ds`
closed-form evaluation), `sorry` it explicitly, write a one-line comment
explaining exactly what's missing, and continue — do not get stuck polishing
one lemma at the expense of reporting overall progress.

### Stage 5 — stretch: connect Δ to root count
Everything above is a pure statement about the sign of a real-valued function
Δ. The full informal claim ("...has three real roots") additionally needs, for
a ≠ 0: `Δ(a,b,c,d) > 0 ↔ the cubic ax³+bx²+cx+d has three distinct real roots`.
This is classical (stated, uncited, as background fact in the project's public
explainer) but may not be readily available in Mathlib for general cubics
(Mathlib's `Polynomial.discrim` is quadratic-only; check whether
`Polynomial.discr`/a general discriminant-via-resultant exists and whether
any existing lemma connects its sign to real root count — grep for it before
assuming it's missing). If it's not available, this is a legitimate `sorry`
and a real gap worth naming explicitly rather than quietly assumed away — is
scoped as its own classical-cubic-theory lemma, separate from the Theorem 3
measure computation, and should be stated as its own clearly-labeled theorem
even if unproved.

## Deliverables

1. `NonmonicCubic/Theorem1.lean`, `Theorem2.lean` — complete, `sorry`-free.
2. `NonmonicCubic/Theorem3Statement.lean` — the precise statement, type-checks,
   proof `sorry`d if needed.
3. `NonmonicCubic/Theorem3Proof.lean` (or split further) — as much of Stage 4
   as you get through, each remaining `sorry` commented with exactly what it
   needs.
4. `NonmonicCubic/DiscriminantRootCount.lean` — Stage 5, likely `sorry`d;
   state it even if unproved.
5. `PROGRESS.md` — timestamped log (`date '+%F %T'`), one entry per stage
   reached, including `lake build` output and `#print axioms <name>` output
   for anything you claim is fully proved (to catch an accidental `sorry` or
   `Classical.choice`-only reliance vs a genuinely suspicious axiom).
6. `REPORT.md` at the end — a short, honest summary table: stage reached,
   `sorry` count per file, and — this is important — which specific
   mathematical steps remain unformalized and why (hard to formalize vs. ran
   out of time vs. genuinely needs new Mathlib API that doesn't exist yet).

## Rules

- Stay inside `~/math/nonmonic-cubic-lean/`. Do not touch `/var/www`,
  `~/math/real-rooted-random-polynomials/` (a sibling project — read-only
  reference only, copy files you need into `reference/` here rather than
  editing there), or any other directory. `nice -n 10` the Mathlib
  build/cache steps.
- No git operations beyond what `lake new`/`lake update` do automatically;
  the operator syncs results back manually.
- Use the toolchain `elan` already installed (`source ~/.elan/env` if a fresh
  shell doesn't have it on PATH).
- Precision over speed: a smaller number of correctly, honestly reported
  stages beats a larger number of stages with silently broken or hand-waved
  proofs. If you're ever tempted to use `sorry` and not mention it in
  PROGRESS.md/REPORT.md, don't — every `sorry` must be visible in the report.
- If Stage 0 (environment) itself is the bottleneck (e.g. `cache get` fails,
  network issues pulling Mathlib), spend real effort fixing it before
  declaring defeat — a working Mathlib environment is reusable for future
  formalization work on this campaign's other open theorems.
