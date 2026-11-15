# Stage 351: the benchmark ownership economy has a unique, globally stable equilibrium

Lean 4.35 + Mathlib. 15 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Mathlib-only. The stage-259 convergence proof is inlined and localised to a closed region.

Setting: households share Cobb–Douglas (log) weights `α s > 0` with `∑ α = 1` (the demand derived in stage 252, assumed in stage 250); the aggregate endowment is `ω s > 0`. Aggregate excess demand is `z q s = α s (∑ q ω) / q s − ω s`. Price adjustment is tâtonnement, `dp/dt = z p`.

## Results
- `cd_walras`: Walras' law at every price with nonzero coordinates.
- `cd_equilibrium`: `p* s = κ α s / ω s` clears every market, for every `κ > 0`.
- `lagrange`: the Lagrange identity behind Cauchy–Schwarz.
- `value_formula`, `cd_value_pos`: on the sphere through `p*`, at every positive price other than `p*`, the equilibrium price values excess demand strictly positively: `p*·z(q) = κ((∑ q ω)(∑ α²/(q ω)) − 1) > 0`.
- `ray_eq`, `cd_unique`: `p*` is the only positive equilibrium on its sphere.
- `norm_conserved_on`, `converges_on`: stage 259's convergence theorem, needing continuity and Walras' law only on the closed region where the path stays.
- `cd_stable` (capstone): every tâtonnement path that starts on the sphere through `p*` and keeps prices at least `δ > 0` converges to `p*`.

Reading: with common Cobb–Douglas preferences, the ownership economy's equilibrium is unique and globally stable under price adjustment, whatever the ownership distribution (ownership enters only through the aggregate endowment). The positivity used is the stage-255 value condition, proved directly from Cauchy–Schwarz rather than assumed.

## Limits
- Common weights `α` across households. With heterogeneous weights aggregate demand falls under Sonnenschein–Mantel–Debreu, where uniqueness and stability can fail.
- The price path is assumed to exist for all time and to stay above some `δ > 0`; existence of solutions and the floor are not proved.
- Pure exchange with the aggregate endowment fixed; production and dynamics are not included.
