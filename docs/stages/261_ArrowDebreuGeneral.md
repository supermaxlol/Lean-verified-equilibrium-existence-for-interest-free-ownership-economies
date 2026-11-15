# Stage 261 — Arrow–Debreu existence with several firms and unbounded consumption

Lean 4.35 / Mathlib + `GEOverlap`, 12 audited declarations, all
`[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-242 and
stage-257 sources and the generic part of stage 260 are inlined.

Setting: `ArrowDebreu.Economy I J S` — finitely many households `I`, firms `J`, goods `S`;
each household has a continuous quasi-concave utility, a strictly positive endowment and a
non-negative share `θ i j` in each firm, shares in each firm summing to one; each firm has
its own compact convex production set containing inaction.

- `Economy.N_closed`, `Economy.N_walras` — closed graph and Walras' law for the net
  excess-demand correspondence with several firms.
- `Economy.equilibrium_exists` — equilibrium with consumption sets `[0, M]^S`.
- `Economy.exists_bound` — a bound `M` exceeding everything attainable exists.
- `Economy.equilibrium_unbounded` — if `M` exceeds everything attainable and utility is
  semi-strictly quasi-concave, the equilibrium bundles are optimal in the budget sets with
  no upper bound on consumption.
- `budget_binds` — with semi-strict quasi-concavity and non-satiation an optimal bundle
  exhausts the budget.
- `Economy.competitive_equilibrium` — there are a simplex price `p`, profit-maximising
  plans `y j ∈ Y j`, and bundles `x i` optimal over
  `{x ≥ 0 | p · x ≤ p · ω i + ∑ j, θ i j * p · y j}`, with
  `∑ i, x i s ≤ ∑ i, ω i s + ∑ j, y j s` and
  `p s * (∑ i, ω i s + ∑ j, y j s - ∑ i, x i s) = 0` for every good `s`.
- `Economy.first_welfare` — at such an equilibrium no feasible allocation and production
  plan makes every household at least as well off and one strictly better off.
- `Economy.efficient_equilibrium` — a Pareto-efficient competitive equilibrium exists.
- `Economy.dividends_exhaust_profit`, `Economy.dividend_nonneg` — all profit is paid to
  owners and no dividend is negative.
- `semistrict_of_concave` — a concave utility is semi-strictly quasi-concave.

What changed from stage 260: one production set per firm with firm-specific shares; the
consumption box is removed from the final statement; goods in excess supply have zero
price.

Limits: exact equality of supply and demand is not proved (it would need free disposal in
production, which a compact production set excludes). The final theorems assume
semi-strict quasi-concavity and non-satiation in addition to the stage-260 hypotheses.
Production sets are compact. Finite goods.
