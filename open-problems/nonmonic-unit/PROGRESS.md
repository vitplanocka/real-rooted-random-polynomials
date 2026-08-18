# PROGRESS — non-monic cubic on [0,1]^4

*Single session, 2026-08-18. Every step below was executed in the order the brief
prescribes; nothing is claimed here that is not reproducible from `src/`.*

## Timeline

1. **Target number first** (`src/mc4d.py`, `results/mc4d.txt`).
   Raw 4-D Monte Carlo on the sign of Δ₄, N = 2×10⁹, seed 12345:
   **P = 0.0186035540 ± 3.0×10⁻⁶**. Recorded before any derivation.

2. **Reduction validated** — three parallel independent checks (subagents):
   - independent 4-D MC by *numerical root counting* (never forms Δ₄), N = 2×10⁹,
     different seed: 0.018601804 ± 3.0×10⁻⁶ (0.41σ from step 1); the same counter
     reproduces all three *known* cells (Thm 1, 2, 3) within 1.3σ;
   - all four face volumes by direct 3-D MC, N = 2×10⁹ each: F_a = F_d and
     F_b = F_c within 1.1σ, (F_a+F_b+F_c+F_d)/4 and 1/5760 + F_b/2 both agree with
     step 1 (0.19σ, 0.04σ);
   - the a=1 face by deterministic quadrature: **F_a = 1/2880 with residual
     exactly 0 at 30, 40 and 50 digits** — the decisive check that the cone
     slicing and face identification are set up correctly.
   The cone/slicing lemma and the reciprocal symmetry were also re-derived from
   scratch rather than taken from the brief (see `VERDICT.md`).

3. **Closed form derived** (`src/derive_S.py`): 12 exact sympy identities (band
   endpoints, the discriminant factorisation Δ₄ = −27a²(d−d_lo)(d−d_hi), L1, L2,
   branch continuity) all PASS, then the s-integral gives
   **S = 479/960 − (2/3)log 2** and **P = 719/2880 − log 2/3**.

4. **Verified** — nine independent routes, tabulated in `VERDICT.md`. Highlights:
   a second symbolic derivation in the *opposite integration order*
   (`src/derive_S_alt.py`) returning the identical closed form; a 40-digit mpmath
   quadrature with no s-substitution and no case analysis agreeing to 2.5×10⁻³⁹;
   blind `mp.identify`/`mp.pslq` recovering the constants unprompted; randomized
   Sobol' QMC of the *full* 4-D volume with no cone reduction at all
   (`src/qmc_P.py`, −0.50σ).

5. **Lean formalization complete** — `~/math/nonmonic-cubic-lean/nonmonic_cubic`,
   commit `fe55b53`, four new files (1268 lines), **zero `sorry`**, axioms
   `propext, Classical.choice, Quot.sound` only. `theorem4`,
   `theorem4_probability`, `theorem4_root_count`. See `VERDICT.md` for the file
   breakdown and for what was reused from Theorem 3 versus what is genuinely new.

6. **Novelty** — targeted search run for this project's constant (`LITERATURE.md`):
   no prior appearance found. Li (1988) is symmetric-intervals-only per the MR
   review recovered by the sibling project; marked UNVERIFIED there and here, since
   Li's paper itself is still unobtained.

7. **Lean warnings** — all four new files are warning-free (`show`-tactic lint,
   unused binders, deprecated `push_neg`, 100-char lines), full project builds clean.

## What is *not* done

- ~~No literature search of my own~~ — **done**, see `LITERATURE.md`. Nothing found
  for `719/2880`, `479/960`, `0.0186037` on MathOverflow, Math.StackExchange, OEIS,
  arXiv or the general web; the canonical Math.SE thread and the dxdy.ru thread are
  both purely symmetric-interval. Three limitations remain and are stated there:
  Li (1988) is still unread (publisher blocks fetching; abstract elided on Semantic
  Scholar; 0 citations), no full-text journal index was reachable, and the dxdy
  formulas are images so that thread was checked structurally rather than textually.
- **Not written up as a paper.** The sibling project's `paper/paper.tex` has three
  cells; adding the fourth is a mechanical extension but was out of scope here.
- The direct 3-D deterministic quadrature of the full 4-D volume
  (`src/direct_P_quad.py`) was started and killed: nested tanh-sinh with
  root-finding was too slow to finish. The randomized-Sobol' QMC in `src/qmc_P.py`
  supersedes it (2.2×10⁻⁷ empirical error bar), so nothing is lost, but the file is
  left in place and **its result is absent, not confirmed**.

## Files

| file | what |
|---|---|
| `src/mc4d.py` | step-1 raw 4-D Monte Carlo (the target number) |
| `src/mc4d_rootcount.py` | independent 4-D MC by root counting (no Δ₄) |
| `src/faces_mc.py`, `src/faces_quad_check.py` | all four face volumes, MC + quadrature |
| `src/face_a_check.py` | the a=1 face = 1/2880, MC + 50-digit quadrature + symbolic |
| `src/derive_S.py` | the derivation, with 12 exact identity checks |
| `src/derive_S_alt.py` | second symbolic derivation, opposite integration order |
| `src/verify_S.py` | independent 40-digit quadrature + blind PSLQ / identify |
| `src/qmc_P.py` | randomized-Sobol' QMC of the full 4-D volume |
| `src/lean_targets.py`, `src/lean_targets2.py` | exact constants for the Lean proof |
| `src/direct_P_quad.py` | abandoned slow nested quadrature (see above) |
| `results/` | recorded outputs of the above |
| `VERDICT.md` | the result, the proof sketch, the verification table, the Lean map |
