# Stage 254 — Production equilibrium with convex-valued demand and supply

Lean 4.35 / Mathlib + `GEOverlap`, 3 audited declarations, all
`[propext, Classical.choice, Quot.sound]`. The stage-242 source is inlined.

Setting: `CorrProductionEconomy` — a demand correspondence `Z` and a supply correspondence
`Y`, each non-empty, convex-valued, with closed graph and values in a compact convex set,
and Walras' law for every pair of selections at simplex prices.

- `SetValuedGND.setValued_gnd` — the set-valued Gale–Nikaido–Debreu theorem (re-audited).
- `CorrProductionEconomy.net_closed` — the difference correspondence `Z p - Y p` has a
  closed graph.
- `CorrProductionEconomy.equilibrium_exists` — some simplex price `p`, `x ∈ Z p` and
  `y ∈ Y p` satisfy `x s ≤ y s` in every good.

Limits: the correspondences and their properties are hypotheses here. Stage 260 derives
them from utilities, endowments and a production set.