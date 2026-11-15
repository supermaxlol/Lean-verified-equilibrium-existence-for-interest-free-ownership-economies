# Stage 347: unique demand for the weight p_k

Lean 4.35 + Mathlib. 45 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file repeats stage 336 (the Afriat construction for slowly varying weights) and stage 339 (the explicit `L`, `F`) in full, and adds the results below.

## Results
- `nsq_neg`, `arc_neg`, `arc_zero`, `arc_diff`: facts about the great-circle arc `arc p z t` that leaves the unit price `p` in direction `z`. Reversing `z` is the same as reversing `t`, `arc p z 0 = p`, and the arc is differentiable in `t`.
- `afriat_arc_unique`: take a price `p` in a rich set `P`, so that `P` contains short arcs leaving `p` in every budget direction. If the Afriat objective `t ↦ V(arc) + λ(arc) · (arc · x p)` is differentiable at `0`, then every other budget-feasible bundle `y ≠ x p` with `p · y = 0` is **strictly** worse than `x p` under the Afriat infimum utility. The proof works like this. `t = 0` is a local minimum of a differentiable function, so its derivative is `0`. The slope is therefore small on `(0, t0)`, and the strict Afriat margin `ε` then gives a strict gap.
- `weight_pk_unique`: this is generic in `F`, `L`. If `β < 1`, `F` and `L` are differentiable on `[ε, β]` and `P` is rich, then the stage-336 utility is continuous, concave and strictly monotone. At every `p ∈ P`, Debreu's trade `p_k · dirk k p` is then its **unique** maximiser on the budget set `p · y ≤ 0`.
- `F_diff`, `L_diff`, `pk_unique_explicit`: the explicit `F`, `L` of stage 339 are differentiable. This gives unique demand for the weight `p_k` with `K σ ≥ 7`, `ℓ = (σ/2) e^{−Kπ/2}`, `Λ = 1`.

## Limits
- Richness is a hypothesis on `P`. It holds on open subsets of the sphere, and stage 348 uses this to reach the closed cap. It fails at boundary points of a closed `P`.
- This covers only the `p_k` weight, the stage-336 slowly-varying class. Uniqueness for Debreu's weight `A p_k + Z_k` (stage 346) is **not** assembled.
- The hypothesis `hσa` is assumed, as in stage 339.
