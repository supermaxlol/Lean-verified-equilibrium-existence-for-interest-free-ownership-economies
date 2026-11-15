# Stage 299: Heterogeneous Lucas economy with debt

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Households `i` own tree shares `θ i > 0` with `∑ θ i = 1`. All have CRRA felicity `c ^ p / p`,
`0 < p < 1`. Besides the tree (asset `j0`, dividend `Y`), any number of other assets, including
one-period debt, trade in zero net supply. Asset prices satisfy the Euler equation at aggregate
consumption `Y`. Plans satisfy position limits (stage 297).

## Results
- `hold_beats_bounded_e`: stage 297 extended to a general reference portfolio `e` (not only the tree).
- `hetero_equilibrium`: markets clear (consumption `θ i * Y` sums to `Y`; endowment portfolios sum to one tree and zero of every other asset), and for every household and every bounded affordable plan the utility gap against holding its share is at most `β ^ n * K` at every horizon and eventually below every `ε > 0`.
- Plus the stage 297 lemmas: `Fv_bound`, `term_bound`, `hold_beats_bounded_plans`.

## Reading
This connects stages 293, 294 and 297. Wilson's result (294) says common CRRA households share
risk linearly, so each one's marginal utility is a fixed multiple of the aggregate. The aggregate
Euler prices are then each household's own Euler prices (the factor `θ i ^ (p-1)` scales out).
So nobody wants to trade debt: everyone holds their share, debt is in zero net supply and goes unused.
Interest-free ownership is an equilibrium, not an imposed restriction.

## Limits
- Common CRRA exponent `p ∈ (0,1)`. Heterogeneous risk aversion is not covered.
- Position limits (sufficient, not general no-Ponzi).
- Prices come from the Euler equation at the aggregate. Uniqueness of equilibrium is not proved.
