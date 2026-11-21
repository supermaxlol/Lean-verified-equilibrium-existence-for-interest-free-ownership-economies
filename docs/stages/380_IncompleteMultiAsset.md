# Stage 380: incomplete markets with many assets: the household optimum exists at every arbitrage-free price

Lean 4.35 + Mathlib. 10 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/IncompleteMultiAsset.lean`](../../formal/IncompleteMultiAsset.lean).

Stages 366, 371 and 375 left open the existence of equilibrium with many assets, incomplete
markets and heterogeneous risk aversion. Stages 371 and 375 named the missing ingredients:
existence of each household's optimal portfolio at arbitrary arbitrage-free prices, continuity
of portfolio demand in a multi-dimensional price, and a fixed point argument. This file proves
the first ingredient in full generality and its uniqueness; it does NOT prove existence of
equilibrium.

Setup: one date, finitely many states `s` with common probabilities `π s > 0`, finitely many
assets `j` with ANY payoffs `d j s` (any sign; markets may be incomplete, assets may be
redundant). Asset prices are arbitrage-free: `q j = qp ψ d j = Σ_s ψ s d j s` with strictly
positive state prices `ψ s`. A household has marginal utility `c ^ (−γ)` with any `γ > 0` (log
and every power utility) and an endowment portfolio `e` paying a positive amount in every state.

* `exists_optimum`: there is a portfolio `θ` that costs no more than the endowment portfolio,
  gives positive consumption in every state, and maximises expected utility among ALL portfolios
  that cost no more than the endowment portfolio and give positive consumption.
  Proof: in payoff space, the budget set intersected with the span of the payoffs and with
  `{x ≥ δ}` is compact (`K_compact`; the span is closed, `isClosed_Mset`), so expected utility
  has a maximiser there. If the maximiser touched the floor `δ` in some state, moving toward
  the endowment payoff would raise utility at rate at least `π_min δ ^ (−γ) m / 2 − A` (an Inada
  bound with explicit constants), which is positive for `δ` small (`small_delta`); so the
  maximiser is interior, the directional derivative toward every affordable positive payoff is
  nonpositive (`deriv_nonpos`), and concavity (`V_diff_le`) makes it a global maximiser.
* `optimum_payoff_unique`: any two optimal portfolios (for the same prices and budget) pay the
  same in every state (strict concavity, `mid_strict`).
* `portfolio_unique`: if no nonzero portfolio pays zero in every state, the optimal portfolio
  itself is unique.

Limits: this is a household-level result. Existence of a general equilibrium with many assets,
incomplete markets and heterogeneous CRRA coefficients remains NOT proved: continuity of the
optimal portfolio in the state prices (which needs a uniform interiority bound and a
closed-graph argument) and the fixed point over prices (which must handle state prices
approaching zero) are not in this file. One date, common beliefs, CRRA marginal utility only.
