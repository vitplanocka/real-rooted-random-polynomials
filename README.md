# Real-Rooted Random Polynomials

**How likely is a random cubic polynomial to have three real roots?**

This repository contains the paper, code, and machine-checked Lean proofs for
three closed-form answers to that question.

> **Theorem 1.** For $(a,b,c)$ i.i.d.\ uniform on $[-1,1]$:
> $\mathbb{P}(x^3+ax^2+bx+c \text{ has 3 real roots}) = \dfrac{383}{4860}+\dfrac{\ln 3}{48} = 0.10169434\ldots$
>
> **Theorem 2.** For $(a,b,c)$ i.i.d.\ uniform on $[0,1]$:
> $\mathbb{P}(x^3+ax^2+bx+c \text{ has 3 real roots}) = \dfrac{1}{2880}$
>
> **Theorem 3.** For $(a,b,c,d)$ i.i.d.\ uniform on $[-1,1]$:
> $\mathbb{P}(ax^3+bx^2+cx+d \text{ has 3 real roots}) = \dfrac{641}{2430}-\dfrac{\ln 3}{24} = 0.21801050\ldots$

Theorems 1 and 2 appear to be new — an eight-agent literature sweep found no
prior publication of either value anywhere searchable. Theorem 3's *value* was
not new (it circulated unproved on a forum since June 2026); what's new is the
first proof and its five-way independent verification.

## Contents

| Folder | What's in it |
|---|---|
| [`paper/`](paper/) | The paper (`paper.tex`, `paper.pdf`) — full statements, proofs, novelty discussion, open problems |
| [`code/`](code/) | All Python source and results behind the paper (sympy exact proofs, high-precision quadrature, Monte Carlo) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization — Theorems 1 & 2 are **fully machine-checked, zero `sorry`**; Theorem 3 is in progress |
| [`docs/`](docs/) | Extended write-ups: full proof derivations (`THEOREMS.md`), literature review (`LITERATURE.md`), and the complete investigation record for Theorem 3 (`VERDICT.md`, `PROGRESS.md`) |
| [`explainer/`](explainer/) | An interactive HTML visualization of the monic-cubic case (open `cusp-and-cube.html` in a browser — no build step, no dependencies) |

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
lake build           # Theorem1.lean and Theorem2.lean compile with zero sorry
```

## Status

This is an active project. Theorem 3's Lean formalization is ongoing; `lean/PROGRESS.md`
has the latest state, and the paper will be updated as it completes. See
`docs/LITERATURE.md` for the ranked list of open follow-on problems (the
monic quartic via the same divergence-theorem trick, Gaussian-coefficient
cubics, and the still-unsolved parent problem — real eigenvalues of a random
$n\times n$ matrix with uniform entries, for $n\ge3$).

## License

MIT — see [`LICENSE`](LICENSE).
