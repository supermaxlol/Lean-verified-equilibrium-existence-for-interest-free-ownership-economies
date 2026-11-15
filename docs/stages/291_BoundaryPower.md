# Stage 291 — Boundary allocations: every power utility, and a corner without Inada

Lean 4.35 + Mathlib. 7 new audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file inlines stage 288.)

- `power_inada`, `crra_sg`, `power_lip`: `c ^ p` with `0 < p < 1` satisfies the Inada and Lipschitz hypotheses of stage 288.
- `power_optimum_interior`: for every such power, an optimum over non-negative bundles that consumes something is strictly positive in every state.
- `cara_not_inada`: exponential utility `-exp(-c)` fails the Inada condition.
- `cara_sg`: its supergradient inequality.
- `cara_corner_optimal`: two equally likely states, prices `1` and `2e`, wealth `1`: the bundle `(1, 0)` with nothing in the second state is optimal over non-negative bundles.

Reading: the interior hypotheses of stages 275, 276 and 280 are consequences for every power utility with `0 < p < 1`. For CRRA with `p ≤ 0` (including log) utility is minus infinity at zero, so optima are interior by definition. Without the Inada condition the result is false: exponential utility has corner optima.

Limits: the `p ≤ 0` and log cases rest on the extended-value convention and are not formalised (Lean assigns junk finite values at zero). The corner example is one explicit economy.
