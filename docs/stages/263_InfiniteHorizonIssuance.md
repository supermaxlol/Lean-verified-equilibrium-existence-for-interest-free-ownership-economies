# Stage 263 — Issuance dynamics with infinite-horizon savers

Lean 4.35 / Mathlib, 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: every household consumes the fraction `1 - β` of wealth and holds the rest in
ownership units (the rule of stage 258, shown optimal in stage 264). `D` is total
dividends, `Q` the total value of units, `g` the growth rate of units, `σ` the fraction
of new units issued equally, `c` the equal share.

- `clearing_cap`, `cap_clears` — the market for units clears when `Q = β D / (1 - β)`.
- `equilibrium_return` — the gross return on ownership is then `1 / β`.
- `trade_preserves_share` — with a common saving rate each household's share of units
  bought equals its share of wealth.
- `consumption_share` — consumption shares equal wealth shares.
- `share_converges` — with `g > 0` and `0 < σ ≤ 1` every share converges to `c`.
- `pro_rata_preserves` — with `σ = 0` shares never move.

Limits: the saving rule is taken as given in this file. With equal issuance the rule is
not shown to remain optimal. Constant growth and issuance fractions; no uncertainty.
