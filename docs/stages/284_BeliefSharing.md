# Stage 284 — Heterogeneous beliefs under log utility

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finite states, output `Y s > 0`. Each household has log felicity and its own probabilities `π`; the market belief `P` is the wealth-weighted average of beliefs. Prices `P s / Y s`.

- `belief_optimal`: the bundle `w * π s / P s * Y s` (wealth share, scaled state by state by own belief over market belief) is optimal for a household with wealth share `w`.
- `belief_cost`: this bundle costs exactly the household's wealth.
- `belief_clears`: the bundles use exactly output in every state.
- `belief_common`: where a household's belief equals the market belief, it holds exactly its wealth share.

Reading: with disagreement, each household holds a share of output that tilts towards the states it finds more likely than the market does. Constant-share ownership returns exactly when beliefs agree.

Limits: log utility only; beliefs are exogenous; no learning or dynamics.
