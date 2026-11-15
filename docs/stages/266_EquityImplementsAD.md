# Stage 266 — With log utility the complete-markets equilibrium is pure ownership

Lean 4.35 / Mathlib, 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`,
no errors, no warnings.

Setting: finitely many states `S` with strictly positive probabilities `π` summing to one,
aggregate output `Y s > 0`, finitely many households `I` with strictly positive
state-contingent endowments summing to `Y`, expected log utility with common
probabilities. State prices are `π s / Y s`.

- `equity_budget` — the bundle `w * Y s` costs `w` at these prices.
- `equity_optimal` — the bundle `w * Y s` maximises expected log utility among strictly
  positive bundles costing at most `w`.
- `shares_sum` — the households' wealth levels at these prices sum to one.
- `equity_equilibrium` — there are shares `w i > 0` summing to one such that each share
  bundle `w i * Y s` costs exactly the household's endowment, is optimal in its budget
  set, and every state market clears with equality.

Reading: in this economy the Arrow–Debreu allocation is a fixed share of output in every
state for each household. No fixed claim is needed to reach it.

Limits: log utility, common probabilities, one good per state, one date. Uniqueness of the
equilibrium is not proved here.
