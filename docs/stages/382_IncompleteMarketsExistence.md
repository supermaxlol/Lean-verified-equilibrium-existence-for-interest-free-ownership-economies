# Stage 382: incomplete markets with one good per state: continuity of demand and the reduction of equilibrium to clearing of payoffs

Lean 4.35 + Mathlib. 13 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/IncompleteMarketsExistence.lean`](../../formal/IncompleteMarketsExistence.lean).

SCOPE: ONE GOOD PER STATE. Everything here is for a single consumption good in each state, so
asset payoffs are real and do not depend on spot prices. With several goods per state,
equilibrium in incomplete markets with real assets can fail to exist (Hart 1975); nothing in
this file applies to that case.

Setup: one date, finitely many states `s`, finitely many assets `j` with ANY real payoffs
`d j s` (incomplete or redundant allowed). Each household has probabilities `π s > 0`,
marginal utility `c ^ (−γ)` with its own `γ > 0`, and an endowment portfolio `e` whose payoff
is positive in every state (the endowment is spanned by the assets; asset supply is
`Σ_i e_i`). Asset prices are arbitrage-free, `q = qp ψ d` with state prices `ψ s > 0`.
Definitions and the household-optimum results are copied from stage 380
(`IncompleteMultiAsset.lean`, not modified).

Proved here:
* `opt_exists`, `opt_unique`: the optimal marketed payoff (`Opt`) exists and is unique at every
  strictly positive `ψ`.
* `opt_le`, `opt_floor`: UNIFORM bounds. On any price set `{ψ | ∀ s, lo ≤ ψ s, ψ·e ≤ B}` every
  optimal payoff lies in `[δ, B / lo]` in every state, with one `δ > 0` for the whole set
  (explicit Inada constants).
* `dem_continuousAt`: the demand map `ψ ↦ dem ψ` (the optimal payoff) is continuous at every
  strictly positive `ψ` (sequential compactness + the uniform bounds + uniqueness).
* `budget_binds`, `walras`: each household spends its whole budget, so aggregate excess payoff
  demand has value zero at every `ψ > 0`.
* `equilibrium_of_payoff_clearing`: if at some `ψ > 0` the optimal payoffs add up to the
  aggregate endowment payoff, there are portfolios `θ_i` with `Σ_i θ_i = Σ_i e_i` (asset markets
  clear exactly, even with redundant assets), each paying the optimal payoff, each affordable at
  `q = qp ψ d` and each optimal among ALL affordable portfolios with positive consumption.
  This is an equilibrium with no-arbitrage prices.

NOT proved (honest limit): EXISTENCE of a `ψ > 0` at which payoffs clear. The missing step is
the fixed point over state prices. A truncated simplex of `ψ` does not work directly because
demand depends on `ψ` only through its action on the marketed span, so demand need not blow up
as some `ψ s → 0`; the boundary argument has to be made in the space of asset prices (the
no-arbitrage cone), where the needed desirability bound near arbitrage prices is not proved
here. Also limited to: spanned endowments, one date, CRRA marginal utility.
