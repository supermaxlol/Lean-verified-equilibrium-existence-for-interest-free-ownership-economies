# Stage 298: CRRA optimum in closed form for every p < 1, p ≠ 0

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Finite states `s` with probabilities `π s > 0`, state prices `q s > 0`, wealth `W > 0`.
CRRA felicity `c ^ p / p`. Utility is extended-real valued: `⊥` off the positive orthant
(as in stage 295), which is the honest model for `p < 0` where `c ^ p / p → -∞` at 0.

## Results
- `copt_props`: the bundle `c s = W / (∑ t, q t * r t) * r s` with `r s = (π s / q s) ^ (1/(1-p))` is strictly positive, exhausts the budget, and satisfies the first-order condition `π s * c s ^ (p-1) = λ ^ (p-1) * q s`.
- `crra_optimum`: for `p < 1`, `p ≠ 0`, it is optimal in extended utility among all non-negative affordable bundles.
- `power_optimum`: for `0 < p < 1`, it is optimal in real-valued utility, with zero consumption allowed.
- Supporting (audited): `crra_supergradient`, `power_sg_nonneg`.

## Reading
Stage 295 showed the optimum is interior for log and for `p < 0`. This stage gives the optimum
itself, in closed form, using supergradient + first-order condition. No compactness argument is needed.

## Limits
- For `p < 0` the boundary is treated as `⊥` (extended utility). The real-valued statement covers `0 < p < 1`.
- Log (`p = 0`) is stage 295's `log_optimum`, not repeated here.
- Complete markets (one price per state).
