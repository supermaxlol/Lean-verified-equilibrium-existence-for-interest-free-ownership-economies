# Stage 256 — Debreu decomposition of excess demand

Lean 4.35 / Mathlib, 5 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: a price `p` and a vector `z` with `p · z = 0`. `proj p i` is the projection of the
unit vector of good `i` onto the hyperplane `p · x = 0`.

- `nsq_pos` — the squared norm of a strictly positive price is positive.
- `proj_walras` — each projected direction has zero value at `p`.
- `decomposition` — `z = ∑ i, (z i + lam * p i) • proj p i` for every `lam`.
- `exists_positive_coeff` — at a strictly positive price the coefficients can be made
  strictly positive.
- `positive_decomposition` — any Walrasian vector splits into one summand per good, each
  a positive multiple of that good's budget-feasible direction and each obeying Walras'
  law on its own.

Limits: this is the decomposition step of Sonnenschein–Mantel–Debreu only. That each
summand is the demand of a fixed preference relation is not proved; Mantel surjectivity
remains open.
