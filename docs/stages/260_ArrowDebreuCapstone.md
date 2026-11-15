# Stage 260 — Arrow–Debreu existence with production, from primitives

Lean 4.35 / Mathlib + `GEOverlap`, 7 audited declarations, all
`[propext, Classical.choice, Quot.sound]`. The stage-242 and stage-257 sources are inlined.

Setting: `ArrowDebreu.Economy` — finitely many households and goods; each household has a
continuous quasi-concave utility, a strictly positive endowment and a non-negative profit
share, shares summing to one; one compact convex production set containing inaction;
consumption sets `[0, M]^S`.

- `retr_continuous` — a continuous retraction of price space onto the simplex.
- `profit_continuous` — maximal profit is continuous in prices.
- `budgetW_lhc` — the budget correspondence is lower hemicontinuous when wealth is
  continuous and strictly positive.
- `Economy.dem_closed` — household demand has a closed graph.
- `Economy.N_closed`, `Economy.N_walras` — the net excess-demand correspondence has a
  closed graph and satisfies Walras' law.
- `Economy.equilibrium_exists` — there are a simplex price `p`, a plan `y` maximising
  profit over the production set, and bundles `x i` maximising utility over each budget
  set (endowment value plus profit share), with
  `∑ i, x i s ≤ ∑ i, ω i s + y s` for every good `s`.

Reading: no strict concavity or strict convexity. Demand and supply are correspondences
obtained from the maximum theorem and cleared with the set-valued Gale–Nikaido–Debreu
theorem.

Limits: consumption is bounded by the box `[0, M]^S` and the bound is not removed; one
aggregate production set rather than one per firm; market clearing is with free disposal
(`≤`); finite goods.