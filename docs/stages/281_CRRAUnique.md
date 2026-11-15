# Stage 281 — With any CRRA utility, every interior equilibrium is a division of ownership

Lean 4.35 / Mathlib, 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-268, 270, 275, 279 and 280
sources are inlined.

Setting: exponent `p < 1`, `p ≠ 0`, felicity `1 / p * c ^ p` common to all households.

- `bernoulli_pos_strict` — `t ^ p < 1 + p * (t - 1)` for `0 < p < 1`, `t > 0`, `t ≠ 1`.
- `crra_strict_supergradient_all` — the strict supergradient inequality for every such
  `p` (stage 279 had it for `p < 0` only).
- `crra_equilibrium_is_ownership` — at any strictly positive prices, a strictly positive
  allocation that uses exactly output and is optimal for each household is a division of
  ownership: `x i s = w i * Y s` with `w i > 0`, `∑ w = 1`.

Limits: common exponent and common beliefs; the log case `p = 0` is not restated here
(stage 270 gives its strict inequality). Interior allocations, one date.
