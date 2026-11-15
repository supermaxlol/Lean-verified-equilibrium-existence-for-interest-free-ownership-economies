# Stage 268 — Ownership implements the complete-markets equilibrium for homothetic utility

Lean 4.35 / Mathlib, 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`,
no errors, no warnings.

Setting: as in stage 266, but with any felicity `u` that has a marginal-utility function
`m` which is a supergradient (`u a ≤ u b + m b * (a - b)` for positive `a`, `b`), strictly
positive, and homogeneous (`m (w * y) = h w * m y` with `h w ≥ 0`). State prices are
`π s * m (Y s)`.

- `share_optimal` — the share bundle `w * Y s` maximises expected utility among strictly
  positive bundles costing at most `w` times the value of output.
- `ownership_equilibrium` — there are shares `w i > 0` summing to one such that each share
  bundle costs exactly the household's endowment, is optimal in its budget set, and every
  state market clears with equality.
- `log_supergradient`, `log_homogeneous` — log utility satisfies the hypotheses with
  `m y = 1 / y`.

Reading: the stage-266 result does not depend on log utility; it needs identical
homothetic preferences and common probabilities.

Limits: the hypotheses are verified for log utility only; power utility is not checked.
Identical preferences and common probabilities are assumed. One good per state, one date.
