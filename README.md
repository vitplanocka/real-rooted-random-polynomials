# Real-Rooted Random Polynomials

**How likely is a random cubic polynomial to have three real roots?**

This repository contains the paper, code, and machine-checked Lean proofs for
four closed-form answers to that question.

> **Theorem 1.** For $(a,b,c)$ i.i.d.\ uniform on $[-1,1]$:
> $\mathbb{P}(x^3+ax^2+bx+c \text{ has 3 real roots}) = \dfrac{383}{4860}+\dfrac{\ln 3}{48} = 0.10169434\ldots$
>
> **Theorem 2.** For $(a,b,c)$ i.i.d.\ uniform on $[0,1]$:
> $\mathbb{P}(x^3+ax^2+bx+c \text{ has 3 real roots}) = \dfrac{1}{2880}$
>
> **Theorem 3.** For $(a,b,c,d)$ i.i.d.\ uniform on $[-1,1]$:
> $\mathbb{P}(ax^3+bx^2+cx+d \text{ has 3 real roots}) = \dfrac{641}{2430}-\dfrac{\ln 3}{24} = 0.21801050\ldots$
>
> **Theorem 4.** For $(a,b,c)$ i.i.d.\ **standard normal**:
> $\mathbb{P}(x^3+ax^2+bx+c \text{ has 3 real roots}) = \dfrac{1}{\pi}\displaystyle\int_0^\infty e^{-\frac{x^4(x^4+4x^2+9)}{2(x^4+4x^2+1)}}\dfrac{2(x^4+6x^2+3)}{\sqrt{x^4+4x^2+1}\,(x^4+4x^2+9)}\,dx = 0.16992938\ldots$

Theorems 1, 2 and 4 appear to be new — a literature sweep found no prior
publication of any of these values anywhere searchable. Theorem 3's *value* was
not new (it circulated unproved on a forum since June 2026); what's new is the
first proof and its independent verification.

**All four theorems are fully machine-checked in Lean 4 / Mathlib — zero
`sorry`, zero unexpected axioms.** The formalization produced two results of
independent interest: a from-scratch, calculus-free proof that a real cubic's
discriminant sign determines its real-root count (a classical fact apparently
missing from Mathlib until now), and a complete formalization of Theorem 4's
Kac–Rice argument — including Owen's $T$-function built from scratch — that
needs **no** general Rice's formula, coarea formula, or theory of stochastic
processes, none of which Mathlib has.

## Contents

| Folder | What's in it |
|---|---|
| [`paper/`](paper/) | The paper (`paper.tex`, `paper.pdf`) — full statements, proofs, novelty discussion, open problems |
| [`code/`](code/) | All Python source and results behind the paper (sympy exact proofs, high-precision quadrature, Monte Carlo) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization — **all four theorems fully machine-checked, zero `sorry`** (~7,700 lines, 23 files; `HANDOFF.md` and `REPORT.md` have the full account) |
| [`docs/`](docs/) | Extended write-ups: full proof derivations (`THEOREMS.md`), literature review (`LITERATURE.md`), and the complete investigation record for Theorem 3 (`VERDICT.md`, `PROGRESS.md`) |
| [`explainer/`](explainer/) | An interactive HTML visualization of the monic-cubic case (open `cusp-and-cube.html` in a browser — no build step, no dependencies) |
| [`open-problems/`](open-problems/) | Research on the follow-on questions. The Gaussian cubic is now **resolved** (Theorem 4); the uniform monic quartic remains open — see `PROGRESS.md` there for status |

## Quick start

**Read the paper**: [`paper/paper.pdf`](paper/paper.pdf).

**Reproduce a theorem**:
```
cd code && pip install -r requirements.txt
python src/closed_form.py   # Theorems 1 & 2, symbolic proof
python src/face_exact.py    # Theorem 3, symbolic proof
```

**Check the Lean proofs**:
```
cd lean
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake exe cache get   # pulls prebuilt Mathlib .olean files
lake build           # all three theorems compile with zero sorry, ~1 minute from a warm cache
```

## Status

The core project is done: three theorems, three closed forms, all fully
machine-checked. Active follow-on work is in `open-problems/` — two genuinely
open questions (a Gaussian-coefficient monic cubic, and the uniform monic
quartic) attacked with the same reduce/verify methodology; see
`open-problems/PROGRESS.md` for the latest state. See `docs/LITERATURE.md` for
the full ranked list of open problems, including the still-unsolved parent
problem — real eigenvalues of a random $n\times n$ matrix with uniform
entries, for $n\ge3$.

## License

MIT — see [`LICENSE`](LICENSE).
