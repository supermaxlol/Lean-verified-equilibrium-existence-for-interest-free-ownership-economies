# Stage 293: Lucas tree with many assets, short sales and zero consumption

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Finite Markov chain `π` on states `S`, discount `β ∈ (0,1)`, tree dividend `Y s > 0`, marginal utility `mu s > 0`. Any finite family of assets `J` with dividends `d j s`; the tree is one asset `j0` with `d j0 = Y`. Portfolios may be any reals (short sales and debt allowed), and they may depend on the whole history.

## Results
- `asset_price_exists`: every asset has a price solving the Euler equation `mu s · P s = β Σ π s s' · mu s' (P s' + d s')` (Blackwell contraction).
- `node_step`: one-period budget identity combined with the Euler equation.
- `gap_le`, `ugap_le`: for any plan, the n-period utility gap against holding the tree is bounded by minus a terminal wealth term.
- `hold_beats_every_plan`: holding the tree is weakly better than every finite-horizon plan up to the terminal term, and better than every plan whose terminal term vanishes (transversality).
- `power_plans`: for `c^p/p` with `0 < p < 1`, consumption may be zero.
- `power_sg_nonneg`, `log_sg`: the supergradient inequalities used.

## Reading
Debt and every other asset can be traded, but no plan beats holding the tree. Interest-bearing claims exist in the market, and they are simply not used at the optimum.

## Limits
- Transversality (terminal term → 0) is a hypothesis, not derived.
- Prices are those of a representative agent (the Euler equation at the tree allocation). This is the standard Lucas equilibrium, not an existence proof for heterogeneous agents.
- Log and `p ≤ 0` still need strictly positive consumption here; see stage 295 for the boundary.
