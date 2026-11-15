# Stage 286 — Dynamic ownership equilibrium: a Lucas tree with log utility

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finitely many Markov states `S`, transition weights `π s s'` summing to one, output `Y s > 0`, discount `0 < β < 1`, log felicity. One asset, the claim to all future output, priced at `p s = β / (1 - β) * Y s`. Value function `V θ s = log θ / (1 - β) + v s`, where `v` solves `v s = log (Y s) + β * ∑ π s s' * v s'`.

- `tree_price_euler`: the price satisfies the Euler equation `p s / Y s = β * ∑ π s s' * (p s' + Y s') / Y s'`.
- `hold_bellman`: for any consumption and next-period share affordable from share `θ`, `log c + β/(1-β) * log θ' ≤ log θ / (1-β) + log (Y s)`.
- `hold_bellman_eq`: equality when the household consumes its share of output and keeps its share.
- `tree_bellman`: `V` satisfies the Bellman inequality against every affordable choice.
- `tree_bellman_eq`: holding the share forever attains it.
- `tree_clears`: constant shares summing to one consume exactly output.

Reading: in an infinite-horizon economy with Markov output, every household holding a constant share of the tree forever, and consuming that share of output each period, is an equilibrium, with the tree price in closed form. Ownership needs no debt in the dynamic setting either.

Limits: log utility only (no general CRRA); the value function `v` is assumed to solve its linear equation (existence follows from stage 258's contraction but is not re-derived here); optimality is shown through the Bellman inequality, and the step from the Bellman inequality to optimality against whole plans with a transversality condition is not re-proved in this file (see stages 264, 277 for the saver side); uniqueness of equilibrium is not claimed.
