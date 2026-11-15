# Stage 278 — Exact market clearing in the general Arrow–Debreu economy

Lean 4.35 / Mathlib, 1 audited declaration, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-261 source is inlined.

Setting: the stage-261 private-ownership economy (several firms, compact convex
production sets containing zero, strictly positive endowments, continuous quasi-concave
utilities, unbounded consumption sets), with at least one household.

- `exact_equilibrium` — if utilities are strictly monotone (and satisfy the stage-261
  strict-convexity condition), there are prices in the simplex with EVERY price strictly
  positive, profit-maximising production plans and utility-maximising consumption plans
  such that supply equals demand in every market.

Reading: stage 261 allowed excess supply of goods with zero price. With strictly monotone
utilities no price is zero, so the inequality becomes an equality.

Limits: strict monotonicity is assumed in every good for every household. Finitely many
goods, households and firms.
