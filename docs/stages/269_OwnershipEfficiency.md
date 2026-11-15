# Stage 269 — Every division of ownership is Pareto efficient (homothetic utility)

Lean 4.35 / Mathlib, 2 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: as in stage 268 — felicity `u` with a supergradient `m ≥ 0` that is homogeneous
(`m (v * y) = h v * m y`, `h v > 0`), probabilities `π ≥ 0`, output `Y > 0`, shares
`w i > 0` summing to one.

- `share_gap` — the utility gain of any bundle over the share bundle is at most `h w`
  times its extra cost at the prices `π s * m (Y s)`.
- `ownership_pareto` — no strictly positive allocation with `∑ i, x' i s ≤ Y s` makes
  every household at least as well off as under the share allocation and one strictly
  better off.

Reading: with stage 268, each division of ownership is an efficient allocation supported
by the same state prices.

Limits: identical homothetic preferences and common probabilities. The converse (every
efficient allocation is a division of ownership) is not proved here.
