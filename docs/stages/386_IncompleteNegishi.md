# Stage 386: existence of equilibrium with incomplete markets and heterogeneous CRRA

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/IncompleteNegishi.lean`](../../formal/IncompleteNegishi.lean).

Stage 375 proved existence with many assets and heterogeneous CRRA only under COMPLETE markets;
stage 382 reduced the incomplete-markets case to a Negishi-type fixed point but left existence
open. This file closes that case for the one-period, one-good asset economy below, by the
Negishi method run on the marketed span.

Setup: households `i` with beliefs `π i s > 0`, marginal utility `c ^ (−γ i)` (`γ i > 0`) on
`c > 0`, endowment portfolios `e i` whose payoff is positive in every state; `J` assets with
arbitrary payoffs `d j s` (any number, possibly redundant, possibly incomplete). Consumption is
the portfolio payoff; budgets are `cost (qp ψ d) θ ≤ cost (qp ψ d) (e i)`.

* `planner_foc`, `common_projection`: at a weighted planner optimum on the marketed span, the
  weighted marginal utilities of all households have the same value against every marketed
  payoff.
* `equilibrium_of_planner`: a planner optimum with zero transfers is an equilibrium.
* `planner_exists`, `planner_unique`: for positive weights the planner optimum exists (a floor
  that the Inada property shows never binds, plus concavity) and is unique.
* `plan_floor`, `planner_continuous`: a uniform floor for weights in a band, and continuity of the
  planner allocation in the weights.
* `small_weight`: a household with small enough weight consumes below a given level in every
  state (compactness of marketed bundles plus the common projection).
* **`exists_equilibrium_incomplete`**: Brouwer on weights bounded away from zero gives zero
  transfers, hence positive state prices `ψ` and portfolios `θ` such that every asset market
  clears, each portfolio pays a positive amount in every state, is affordable, and is optimal
  among all affordable portfolios with positive payoff.

Limits: one period, one good, consumption equal to the portfolio payoff (no date-0 consumption),
CRRA-type marginal utility, positive endowment payoffs. Optimality is among portfolios with
strictly positive payoff in every state. With one good the incomplete-markets existence result is
classical (no rank-drop problem); this file is a machine-checked proof of it in this setting, not
a new theorem. Uniqueness of equilibrium, multi-good or multi-period economies, and nominal
assets are not covered.
