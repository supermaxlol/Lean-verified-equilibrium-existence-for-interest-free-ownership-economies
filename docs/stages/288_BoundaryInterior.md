# Stage 288 — Boundary allocations: non-negative optima are interior

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finite states, positive probabilities and prices. Bundles only need to be non-negative. Felicity `u` satisfies an Inada condition at zero (for every `K` there is `δ0 > 0` with `K * δ ≤ u δ - u 0` for `0 < δ ≤ δ0`) and is Lipschitz from above away from zero.

- `boundary_improvable`: a bundle with zero consumption in one state and positive consumption in another can be strictly improved at the same cost.
- `optimum_interior`: an optimum over non-negative bundles that consumes something somewhere is strictly positive in every state.
- `sqrt_inada`, `sqrt_lip`: the square-root felicity satisfies both conditions.
- `sqrt_optimum_interior`: the square-root instance.

Reading: under the Inada condition, the interior hypotheses of stages 275, 276 and 280 are consequences rather than assumptions: any optimum over the non-negative orthant is strictly positive, so those results apply to it.

Limits: felicities without the Inada condition (such as CARA or linear) can have corner optima, which are not covered. Log and general CRRA instances are not separately derived here (log is not defined at zero in the usual sense).
