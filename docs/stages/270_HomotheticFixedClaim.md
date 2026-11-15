# Stage 270 — Strict cost of a fixed claim for strictly concave homothetic utility

Lean 4.35 / Mathlib, 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: stage 268 with the supergradient inequality strict off the diagonal
(`u a < u b + m b * (a - b)` for `a ≠ b`), `π s > 0`.

- `share_strictly_optimal` — any affordable bundle that differs from the share bundle in
  some state gives strictly lower expected utility.
- `fixed_claim_strictly_worse` — a bundle `a * Y s - b` with `b ≠ 0`, when output
  differs across two states, is strictly worse than the share bundle of the same cost.
- `log_strict_supergradient` — log utility satisfies the strict hypothesis.

Limits: the hypotheses are verified for log utility only. Identical preferences and
common probabilities.
