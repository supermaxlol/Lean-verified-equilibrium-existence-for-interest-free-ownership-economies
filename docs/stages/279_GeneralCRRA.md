# Stage 279 — Every constant-relative-risk-aversion utility

Lean 4.35 / Mathlib, 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-268 source is inlined.

Setting: exponent `p < 1`, `p ≠ 0` (relative risk aversion `1 - p`), felicity
`u c = 1 / p * c ^ p`, marginal utility `m y = y ^ (p - 1)`, `h w = w ^ (p - 1)`.

- `bernoulli_neg`, `bernoulli_neg_strict`, `bernoulli_pos` — Bernoulli inequalities for
  real powers.
- `crra_supergradient` — `1 / p * a ^ p ≤ 1 / p * b ^ p + b ^ (p - 1) * (a - b)` for
  positive `a`, `b`.
- `crra_strict_supergradient` — strict for `a ≠ b` when `p < 0`.
- `crra_homogeneous` — `(w * y) ^ (p - 1) = w ^ (p - 1) * y ^ (p - 1)`.
- `crra_ownership_equilibrium` — the stage-268 equilibrium for every such `p`: state
  prices `π s * Y s ^ (p - 1)`, each household holds a share of output and that share is
  optimal on its budget set.

Reading: the pure-ownership equilibrium is not special to log utility. With stage 266
(`p = 0`) it covers the whole CRRA class.

Limits: common risk aversion and common beliefs across households; one date. The strict
inequality for `0 < p < 1` is in stage 281.
