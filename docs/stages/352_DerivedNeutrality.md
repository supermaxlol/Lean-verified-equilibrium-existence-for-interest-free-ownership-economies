# Stage 352: ownership neutrality follows from utility maximisation

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Mathlib-only. The stage-250 definitions and the stage-252 lemmas are inlined.

Setting: households with labour income `L h`, ownership share `θ h` of profit `π` and positive wealth; common log (Cobb–Douglas) utility `∑ α s log (x s)` with `α s > 0`, `∑ α = 1`, prices `p s > 0`. A household's choice is any **best** bundle (`IsBest`): strictly positive, affordable, and at least as good as every strictly positive affordable bundle. No demand rule is assumed.

## Results
- `cd_isBest`: the Cobb–Douglas bundle `α s w / p s` is a best choice.
- `best_eq`: every best choice equals that bundle.
- `optimal_aggregate`: aggregate optimal demand is the Cobb–Douglas demand of total wealth `∑ L + π`.
- `optimal_demand_ownership_neutral`, `optimal_clearing_neutral`: aggregate optimal demand, and so every market-clearing price, is the same under any two ownership distributions.
- `optimal_consumption_share`: each household's optimal consumption is its wealth share of aggregate consumption.

Reading: stage 250's "the market passes the ownership distribution through unchanged" now rests on utility maximisation, not on a posited demand rule.

## Limits
- Common weights `α` across households; with heterogeneous weights prices do depend on the distribution.
- Wealth must be strictly positive for every household, and choices are over strictly positive bundles (log utility).
- Static, one firm; profit `π` is taken as given.
