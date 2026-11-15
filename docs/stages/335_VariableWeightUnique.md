# Stage 335: unique demand for Debreu's consumer with slowly varying weights

Lean 4.35 + Mathlib. 27 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `key_upper`: at the trade `dx w k p = w p·(e_k − p_k p)`, the affine Afriat piece attached to `q` lies at most `‖p − q‖²` above `−p_k`. This uses the stage-334 condition `4κ ≤ ε`.
- `arc`, `arc_unit`, `arc_dot_p`, `arc_dot_z`: explicit great-circle arcs leaving a unit price `p` in a tangent direction `z` (`p·z = 0`).
- `rich_open`: the open set of unit prices with all coordinates `> ε` contains these arcs for small `t`. So the richness condition below is not vacuous.
- `debreu_variable_unique`: assume the stage-334 hypotheses, and that `P` is *rich*, meaning that for every `p ∈ P` and tangent `z`, `arc p z t ∈ P` for all small `t > 0`. Then one continuous, concave, strictly monotone utility makes `dx w k p` the **unique** maximiser on the budget `{y | p·y ≤ 0}` for every `p ∈ P`.

## Proof idea
- A cheaper bundle (`p·y < 0`) is strictly dominated by strict monotonicity.
- For a budget-exhausting `y ≠ dx`, set `z = y − dx`. The affine piece at a nearby price `q` on the arc towards `−z` lies strictly below `u(dx)` at `y`. The `‖p − q‖²` error from `key_upper` is second order; the first-order gain is linear in `t`.

## Limits
- Uniqueness is shown only at relatively interior (rich) prices. Boundary prices of a closed `P` are not covered.
- It still needs the small relative Lipschitz constant `κ ≤ ε/4`. Debreu's weights `α_k = Z_k + A p_k` are not of this kind.
- Continuous Mantel/Debreu on `S_ε` is not proved.
