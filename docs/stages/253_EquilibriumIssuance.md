# Stage 253 — Issuance dynamics as a trading equilibrium

Lean 4.35 / Mathlib, 11 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: the unit stock grows by `1 + g` each period; a fraction `σ` of new units is issued
equally, the rest pro rata; each unit pays dividend `d`; households then trade units at
price `q`. Each household is a two-period log saver.

- `saver_optimal` — the optimal plan spends `β/(1+β)` of wealth on units.
- `equilibrium_price` — market clearing pins the unit price at `β d / (1 + g)`.
- `post_trade_share`, `wealth_total`, `wealth_share` — after trade a household's unit share
  equals its wealth share, which is `eqNext` of its previous share.
- `eqNext_dev`, `eqShareAt_dev`, `eqRate_lt_one`, `eqRate_nonneg` — the distance from the
  equal share shrinks by the factor `eqRate` each period.
- `equal_issuance_equilibrium_converges` — with `σ > 0`, every share converges to the equal share.
- `pro_rata_equilibrium_preserves` — with `σ = 0`, shares never move.

Reading: the convergence result of stage 251 survives trade. Trade slows it (`eqRate` is
closer to one than the no-trade rate) but does not stop it.
Limits: identical log savers with a common savings rate, no labour income, two-period
horizon (stage 258 gives the infinite-horizon savings rule).
