# Stage 276 — The ownership state prices are the only supporting prices

Lean 4.35 / Mathlib, 2 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: states `S`, weights `π`, a felicity `u` differentiable on the positive reals
with derivative `m`, strictly positive prices `p`.

- `foc` — if a strictly positive bundle `x` is optimal among strictly positive bundles
  costing no more than itself, then `π s * m (x s) / p s` is the same in every state.
- `price_proportional` — if the optimal bundle is a share `w * Y s` of output and
  `m (w * y) = h w * m y` with `h w ≠ 0`, then
  `p s * (π t * m (Y t)) = p t * (π s * m (Y s))` for all states `s`, `t`.

Reading: in any equilibrium where a household holds a share of output, prices are
proportional to `π s * m (Y s)`, the prices of stages 266 and 268. Supporting prices are
unique up to scale.

Limits: differentiable felicity, interior bundle, one date, finitely many states.
