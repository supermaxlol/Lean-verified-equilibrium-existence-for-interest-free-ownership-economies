# Stage 257 — Maximum theorem; supply and demand correspondences

Lean 4.35 / Mathlib, 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`.
Mathlib-only.

Setting: `argmax f B p` is the set of maximisers of `f (p, ·)` over the constraint set `B p`.

- `argmax_closedGraph` — continuous objective, closed-graph and (sequentially) lower
  hemicontinuous constraint: the maximiser correspondence has a closed graph.
- `argmax_nonempty`, `argmax_convex` — non-empty on compact non-empty constraint sets;
  convex-valued for a quasi-concave objective on a convex constraint set.
- `supply_closedGraph`, `supply_nonempty`, `supply_convex` — profit-maximising supply over
  a closed / compact / convex production set.
- `budget_compact`, `budget_closedGraph`, `budget_lhc` — the box-bounded budget correspondence on the price simplex with strictly positive
  endowment. `budget_convex` and `budget_nonempty` are not printed separately; they are
  covered through `demand_convex` and `demand_nonempty`, which use them.
- `demand_closedGraph`, `demand_nonempty`, `demand_convex` — utility-maximising demand for
  a continuous quasi-concave utility.

Reading: demand and supply are derived as correspondences from primitives, with no strict
concavity. This is the input the set-valued Gale–Nikaido–Debreu theorem (stage 242) needs.

Limits: finite goods; consumption sets are boxes `[0, M]^S`; lower hemicontinuity is in
sequential form and rests on strictly positive endowments.
