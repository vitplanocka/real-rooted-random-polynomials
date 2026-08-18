# TASK: Non-monic cubic on [0,1]^4 — the missing corner

## The problem

Let $(a,b,c,d)$ be i.i.d. uniform on **[0,1]**. Compute in closed form
$$P = \Pr\big(ax^3+bx^2+cx+d \text{ has three real roots}\big).$$

This completes a 2x2 table already three-quarters done in the sibling project
`~/math/real-rooted-random-polynomials/` (which is now a published paper +
zero-sorry Lean development — read its `paper/paper.tex` and `docs/THEOREMS.md`
for the three known cells):

| | uniform [-1,1] | uniform [0,1] |
|---|---|---|
| **monic** x^3+ax^2+bx+c | Thm 1 = 383/4860 + ln3/48 | Thm 2 = **1/2880** |
| **non-monic** (leading coeff also random) | Thm 3 = 641/2430 - ln3/24 | **THIS TASK** |

Likely new: Li (1988) — the only prior work claiming exact random-cubic
results — treats symmetric intervals only, so the one-sided [0,1] case is
almost certainly not covered. Confirm as part of the writeup, don't assume.

## The reduction (sketch — DERIVE IT RIGOROUSLY YOURSELF, do not trust this)

The quartic-coefficient discriminant Delta(a,b,c,d) is homogeneous of degree 4,
so R = {Delta>0} is a cone. The **exact same cone/slicing lemma** proved in
Theorem 3 applies on [0,1]^4 — but the positive orthant has only **4 faces**
(x_j = 1 for each coordinate j) rather than 8, because all coordinates are
positive so max_i |x_i| = max_i x_i. Slicing at x_j = t and using homogeneity
+ the scaling law vol_3(t.E) = t^3 vol_3(E), then integrating int_0^1 t^3 dt = 1/4:

$$P = \tfrac14\,(F_a + F_b + F_c + F_d),$$

where F_j = vol_3 of the real-rooted region on the face x_j = 1, the other three
coords ranging over [0,1]^3. Two identifications collapse this:

- **Reciprocal symmetry** (a,b,c,d) -> (d,c,b,a) sends each root x to 1/x,
  preserves both R and [0,1]^4, so F_a = F_d and F_b = F_c.
- **The a=1 face is exactly Theorem 2.** On x_a=1 the polynomial is
  x^3+bx^2+cx+d, monic, (b,c,d) uniform on [0,1]^3 — identically Theorem 2's
  model, so F_a = 1/2880. By reciprocal, F_d = 1/2880 too.

Hence
$$P = \tfrac{1}{5760} + \tfrac12 S, \qquad
S := F_b = \text{vol}_3\{(a,c,d)\in[0,1]^3 : a x^3 + x^2 + c x + d \text{ has 3 real roots}\}.$$

**S is Theorem 3's S_b computation restricted to the positive orthant.** In T3,
S_b used the substitution s = sqrt(1-3ac) with s ranging over (0,2) on [-1,1]^3.
Here a,c in [0,1] force ac in [0,1/3] for real critical points, so **s ranges
over [0,1]** instead. The claimed shape of the answer (sketch, verify!):

- the d-band clips below only for s > 1/2,
- the a-integral is int a^{-3} da (elementary),
- the (s-1)^2 factor in K_+ cancels against (1-s^2)^{-2},

leaving a **rational integrand in s** — so the answer should be
**rationals + ln 2 + ln 3**, no arcsinh/arctan. But this is a sketch; the actual
band structure, clip conditions, and s-range must be re-derived from scratch.

## Reference material to reuse (real files on this server)

- **T3 S_b closed form (Python):** `~/math/real-rooted-random-polynomials/src/face_exact.py`
  and `face_verify.py`, `scout_face.py`, `weighted_cone_check.py`. These compute
  and verify S_b on [-1,1]^3. Your S is the same integral on [0,1]^3 — read them,
  understand the substitution and the K_+/K_- band, then adapt. Do NOT blindly
  copy: the domain change (orthant, s-range, clip conditions) is exactly where
  the mathematics differs and where a copy-paste error would hide.
- **T3 cone/face Lean machinery:** `~/math/nonmonic-cubic-lean/nonmonic_cubic/NonmonicCubic/Theorem3Proof.lean`
  — contains `volume_conePiece` and the face-symmetry maps. The Lean phase of
  THIS task should reuse them nearly verbatim (4 pieces instead of 8).
- **Anchors:** Theorem 2 = 1/2880 exactly; Theorem 3 = 641/2430 - ln3/24.

## What to do, in order

1. **Get a target number first.** Write a clean, independent Monte Carlo
   (raw sign of the degree-4 discriminant of a x^3+b x^2+c x+d on [0,1]^4, or
   equivalently a numerical real-root count) at large N. This is the number every
   later step must reproduce — establish it before deriving anything, so a wrong
   closed form can't rationalize itself. Record N, estimate, and std error.

2. **Validate the reduction before using it.** The reduction P = 1/5760 + S/2
   is only trustworthy if independently checked. Compute S by its own direct
   3-D Monte Carlo / quadrature (the b=1 face), plug into 1/5760 + S/2, and
   confirm it matches the step-1 target to MC precision. Separately, confirm the
   a=1 face really integrates to 1/2880 (this is a free, decisive check that the
   cone slicing + face identification is set up right — if it doesn't reproduce
   Theorem 2, the whole reduction is wrong and nothing downstream matters).

3. **Derive the closed form for S** by adapting the T3 S_b calculation to
   [0,1]^3 / s in [0,1]. Keep every algebraic identity checked in exact
   arithmetic (sympy, residual exactly 0), the way `closed_form.py` /
   `face_exact.py` do in the sibling project.

4. **Verify the closed form** to the campaign's standard — do NOT declare it done
   on one check:
   - exact symbolic simplification (sympy) that P - candidate = 0 identically;
   - an **independent** high-precision quadrature of S (mpmath, >= 30 digits),
     structurally different from the derivation, matching the closed form;
   - blind PSLQ / mpmath.identify on the high-precision value of S against a
     basis {1, ln2, ln3, ...} recovering the exact form unprompted;
   - the step-1 Monte Carlo within its error bar.
   A quadrature routine's own error estimate is NOT evidence — only agreement
   between independent computations is (this bit us before: a scipy error bar of
   5e-8 on a value that was actually wrong by 1.7e-5).

5. **Only after the closed form is verified numerically & symbolically**, do the
   Lean formalization as a new file in the existing
   `~/math/nonmonic-cubic-lean/nonmonic_cubic/` project, reusing
   `volume_conePiece` and the face machinery from `Theorem3Proof.lean`. Zero
   sorry, standard axioms only, same as the rest of that development.

6. **Novelty check + writeup.** Confirm Li (1988) really is symmetric-intervals-
   only (its MR review is quoted in the sibling paper's novelty section).
   Write results into this project's own `VERDICT.md` and `PROGRESS.md`.

## Discipline (from the campaign's LESSONS_LEARNED.md)

- A write-up claiming verification is not verification — re-derive, don't re-read.
- Reproduce known anchors (Thm 2 = 1/2880) through every new code path before
  trusting a new number out of it.
- The hardest step is often easier than it looks — but attempt it to find out;
  don't assume the sketch above is right just because it's plausible.
- Log any unverified claim as UNVERIFIED explicitly; don't let it harden into an
  assumed fact.
- Use subagents for genuinely independent sub-checks (e.g. an independent MC and
  an independent quadrature can run in parallel).
- Commit working intermediate results as you go; don't wait for the whole thing.
- Watch context usage; wrap up cleanly (commit + write PROGRESS.md/VERDICT.md)
  well before any ceiling rather than running to auto-compact.

## Environment

- Python venv (sympy 1.14, mpmath 1.3, numpy 2.5): `~/math/open-problems/.venv/bin/python`
- This project: `~/math/nonmonic-01/` (git-initialised; src/ and results/ exist)
- Everything is already on GitHub for the sibling project; THIS project is local
  until there's a result worth publishing.
