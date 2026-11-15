# Stage 341: unique demand at boundary prices via one-sided arcs

Lean 4.35 + Mathlib. 32 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file repeats stage 335 in full and adds the results below.

## Results
- `arc_dot_gen`: `q·z` along an arc in a direction `z'`, for any `z`.
- `debreu_directional_unique`: with **no richness assumption** on `P`, a budget trade `y ≠ dx p` is strictly worse than `dx p` when either
  - it lies strictly inside the budget, or
  - some tangent direction `z'` has `z'·(y − dx p) > 0` and its short arc stays in `P`.
  The separating arc no longer has to point along `y − dx p`.
- `inward_arc`: in the closed cap `{q unit, q ≥ ε}`, the arc in a tangent direction `z` stays in the cap for small `t` whenever `z s < 0` at every active coordinate (`p s = ε`).
- `arc_exits`: at an active coordinate, a nonzero direction with `z s ≥ 0` leaves the cap at once. So the inward condition is exactly what the arc method can use.
- `debreu_closed_cap_unique`: on the **closed** cap `S_ε`, under the stage-334 hypotheses, one continuous, concave, strictly monotone utility makes Debreu's trade
  - the unique maximiser at every price with all coordinates `> ε`, and
  - at a boundary price, strictly better than every budget trade `y` for which some strictly inward tangent `z'` has `z'·(y − dx p) > 0`.

## Limits
- At a boundary price, uniqueness is **not** settled against the trades `y` with `z'·(y − dx p) ≤ 0` for every inward `z'`. By Farkas' lemma (argued, not formalised), those `y − dx p` form the closed cone spanned by the tangent projections of the active `e_s`. Its dimension is the number of active coordinates: a ray when one coordinate is active, and a set of positive measure in the budget plane only when `n − 1` coordinates are active. It is unknown whether demand is unique there.
- Still needs the small relative Lipschitz constant `κ ≤ ε/4`.
