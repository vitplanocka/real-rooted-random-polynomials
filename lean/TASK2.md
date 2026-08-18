# TASK 2: Finish Theorem 3, then attack two new open problems

*Follow-on briefing, written 2026-08-18. Read this only after Theorem 3's Lean
formalization (the mission in TASK.md) is actually complete — i.e. after you
have written REPORT.md for that mission, or otherwise concluded it (including
concluding it with `sorry`s honestly reported, if that's where it lands). Do
not context-switch away from finishing Theorem 3 partway through a proof step
to start this — finish that mission's own reporting first, then start this one
fresh, since they are different kinds of work (formal proof engineering vs.
open mathematical research) and deserve a clean handoff.*

## Use subagents

For both phases below, use the Task/Agent tool whenever a piece of work is
genuinely parallelizable and independent — don't do everything serially in
the main thread. Concretely, good candidates:
- Independent Lean lemmas / independent `sorry`s that don't depend on each
  other's output.
- Phase 2's two problems (Gaussian cubic, uniform quartic) are themselves
  independent of each other — consider working them concurrently rather than
  strictly sequentially, if you judge that a better use of the session.
- Within Phase 2, independent verification routes (e.g. a high-precision
  quadrature attempt and a from-scratch Monte Carlo, or a literature/OEIS
  novelty check) are natural to fan out.
- Anywhere you'd otherwise spend a long serial stretch on a search (grepping
  Mathlib for the right API, searching for prior art on a candidate constant)
  that doesn't block other things you could be doing at the same time.
Use judgment — don't force parallelism where the steps are genuinely
sequential (e.g. a proof that depends on the previous lemma's exact
statement). Report in PROGRESS.md when and why you used a subagent, same as
any other methodological choice.

---

## Phase 2: two new open problems

Both targets below are **genuinely open** — nobody, including us, has a
closed form or a proof yet. This is real research, not a formalization
exercise: work the same way the non-monic cubic investigation did (see
`reference/VERDICT.md` and `reference/PROGRESS.md` from that campaign, copied
into this project's `reference/` folder, for the methodology and the
verification discipline to match). Set up a **new** working directory,
`~/math/open-problems/`, with the same shape as
`~/math/real-rooted-random-polynomials/`: a `.venv` with
numpy/scipy/sympy/mpmath, a `src/` for scripts, a `results/` for JSON output,
and `PROGRESS.md`/`VERDICT.md` written the same way (timestamped log; honest
about what's proved vs. conjectured vs. still just numerics). Lean
formalization is a stretch goal for *after* a closed form is found and
proved — you cannot formalize a proof of a statement nobody has derived yet,
so don't start there.

### Problem A: monic cubic, Gaussian coefficients

> P( x³+ax²+bx+c has 3 real roots ), (a,b,c) i.i.d. N(0,1).

Current best value: Monte Carlo, **0.169962 ± 4.2e-5**.

**The reduction still works, unchanged.** The band identity
(`reference/THEOREMS.md`, "The reduction (common to both)") is pure calculus
about the critical points of x³+ax²+bx — it does not depend on the
coefficient distribution at all. For b < a²/3, three real roots iff
c ∈ [c_lo(a,b), c_hi(a,b)], with c_lo, c_hi given explicitly in
`reference/exact_anchors.py`. Since c ⊥ (a,b) and c ~ N(0,1),

    P = E_(a,b)~N(0,1)² [ 1{b < a²/3} · (Φ(c_hi(a,b)) − Φ(c_lo(a,b))) ]

where Φ is the standard normal CDF. This is a **smooth 2D integral with no
case splits from clipping** — there are no cube walls to hit, so none of
Theorems 1–3's clipping-lemma machinery is needed. That is a genuine
simplification. What is *not* known is whether this integral has a closed
form at all; unlike the uniform cases, there is no a priori reason to expect
one (Gaussian integrals of algebraic functions usually don't resolve
elementarily), so give this an honest, bounded effort rather than assuming
success.

Suggested plan:
1. High-precision quadrature (Gauss–Hermite, natively matched to the
   Gaussian weight, or truncated Gauss–Legendre / tanh-sinh on
   [-8,8]²  — the tails die fast enough that truncation error is negligible
   well before double precision, let alone 30+ digit mpmath precision) to
   get 30+ digits.
2. Blind PSLQ / `mpmath.identify` against a *broad* constant basis: not just
   {1, π, ln2, ln3, √2, √3} but also erf/Φ-adjacent constants, Catalan's
   constant, Γ(1/4), and products/ratios of the above with π. Report the
   search basis you tried, not just "found nothing."
3. If nothing turns up after a serious, well-documented search, say so
   plainly, report the best available numeric value to as many digits as you
   can defend, and move on to Problem B — do not spend unbounded time
   fishing for a closed form.

### Problem B: monic quartic, uniform coefficients

> P( x⁴+bx³+cx²+dx+e has 4 real roots ), (b,c,d,e) i.i.d. U[-1,1].

Current best value: Monte Carlo, **≈0.0054749 ± 9.0e-6**
(`reference` MC engine; sign conditions Δ>0 ∧ P<0 ∧ D<0 already validated at
0/200k mismatches against a numerical root-finder — reuse that
characterization, don't rederive it).

**Correction to a claim in the paper — read before starting.** `paper.tex`'s
"Open problems" section suggests the divergence-theorem/cone trick that
solved Theorem 3 applies directly here. On reflection this is wrong, for two
reasons, and you should not spend time trying it as stated:
1. The trick needs the discriminant region to be a *cone*, which requires
   homogeneity across **all** coefficients scaled together, including the
   leading one. Fixing the leading coefficient at 1 (the monic case, which is
   the actual target here) breaks that homogeneity — different terms of the
   quartic discriminant have different total degree in the *non-leading*
   variables once the leading coefficient is fixed, so {Δ>0} in
   (b,c,d,e)-space is *not* a cone.
2. The trick, correctly applied, targets the **non-monic** quartic (5 free
   coefficients a,b,c,d,e, not 4 — the paper's "2×4=8 faces" is also off by
   one dimension; it should be 2×5=10 faces, collapsing by symmetry to fewer
   distinct pieces). And even there, one of the resulting face volumes *is*
   the monic quartic probability itself (the a=1 face) — so that route would
   need this problem solved first as an ingredient, not derive it.

So: attack the **monic** quartic directly, by genuine generalization of the
Theorems 1/2 method, not by the cone trick. The complication is that a
quartic's critical-point structure is richer than a cubic's: the derivative
4x³+3bx²+2cx+d is itself a cubic, with up to 3 real critical points of the
quartic. Characterizing "4 real roots" in terms of those critical values will
need more than a single band condition — likely a case split on how many
real critical points the derivative has, then a sign-alternation condition
across the local max/min/max chain (this is where the Δ>0 ∧ P<0 ∧ D<0
condition already in hand becomes useful as a cross-check, even if you build
the geometric picture from critical points directly). Suggested plan:
1. Work out the critical-point characterization by hand/sympy first — don't
   jump straight to numerical integration. Look for a "never-clipped" type
   lemma analogous to Lemma 1 in the paper: is there a single extremal
   corner where the band structure touches the cube boundary exactly, the
   way Theorem 1's did at (a,b,c)=(-1,-1,1)? Check this numerically (dense
   grid scan for where the boundary of the favorable region touches
   ∂[-1,1]⁴) before trying to prove anything — that's what revealed the
   Theorem 1 miracle originally.
2. If a clean band/never-clipped structure exists, follow the Theorem 1/2
   template exactly (reduce → integrate precisely → recognize the constant →
   prove symbolically).
3. If it doesn't reduce cleanly, this may be a genuinely harder problem;
   in that case pursue a *rigorous bound* instead of an exact value (e.g.
   Bhargava–Cremona–Fisher-style certified interval subdivision — see
   `reference/LITERATURE.md` §5 "Methods toolbox" for the citation and the
   general approach) and report that as the outcome rather than forcing a
   closed form that may not exist.
4. As with Problem A: report an honest best-effort outcome. A rigorous bound
   or a well-verified high-precision numeric with no closed form found is a
   legitimate, useful result — say so plainly rather than overclaiming.

## Deliverables

1. `~/math/open-problems/PROGRESS.md` — timestamped log, both problems.
2. `~/math/open-problems/VERDICT.md` — final status of each: closed form +
   proof (best case), rigorous bound (good case), or best numeric + honest
   "no closed form found despite search" (acceptable case). Same standard of
   evidence as the non-monic cubic VERDICT.md: multiple independent checks
   for anything claimed as exact.
3. If either resolves to a proved closed form: start a Lean formalization
   the same way `TASK.md` did for Theorem 3, in a fresh `lean/` subfolder,
   staged (statement first, full proof as a stretch goal), and note this
   explicitly in VERDICT.md so it's easy to pick up later.
4. Update `~/math/real-rooted-random-polynomials/README.md`'s "Open targets"
   table and `LITERATURE.md`'s "Ranked next targets" to reflect whatever you
   found — but only that specific file; do not otherwise touch the
   `real-rooted-random-polynomials` project directory, which is a sibling
   project kept as read-only reference (`reference/` here is a copy, not a
   link).

## Rules

Same as `TASK.md`: stay inside `~/math/open-problems/` (plus the two
specific file edits named above), `nice -n 10` heavy computation, no git
operations, precision over speed, every `sorry` and every unresolved search
visible in the report rather than glossed over.
