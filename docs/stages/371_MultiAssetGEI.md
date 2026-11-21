# Stage 371: many assets, one date: optimal portfolios, state prices, and an equilibrium

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/MultiAssetGEI.lean`](../../formal/MultiAssetGEI.lean).

Stage 366 proved that the one-date economy with an equity and a bond has an equilibrium when
households differ in CRRA risk aversion. This file goes beyond two assets.

Setup: finitely many states `s` with probabilities `π s`, finitely many assets `j` with payoffs
`d j s` (any sign; no completeness assumed), asset prices `q j`. A portfolio `θ` pays
`pay d θ s = Σ_j θ j d j s` and costs `cost q θ = Σ_j q j θ j`. Households have marginal utility
`c ^ (−γ)` with `γ > 0` (log and every power utility). `mu θ j = Σ_s π s (pay θ s) ^ (−γ) d j s`
is the marginal value of asset `j` at portfolio `θ`.

The individual problem, for any number of assets:

* `euler_sufficient`: if a portfolio with positive consumption has marginal values proportional
  to prices (`mu θ j = λ q j`, `λ ≥ 0`), it is optimal among all portfolios that cost no more and
  give positive consumption (concavity through the mean value theorem, `concave_le`).
* `unique_optimum`: with positive probabilities and no redundant assets (no nonzero portfolio
  pays zero in every state), such an optimum is the only one.
* `euler_necessary`: conversely, at any optimal portfolio, marginal values are proportional to
  prices (`mu θ j · q k = mu θ k · q j` for every pair; the derivative along each zero-cost
  trade vanishes).
* `state_prices`: hence, if some asset with positive price pays nonnegative amounts and a
  positive amount in some state, an optimal portfolio exists only at prices that are given by
  strictly positive state prices, `q j = Σ_s ψ s d j s` (the prices admit no arbitrage).

Equilibrium:

* **`exists_equilibrium_common`**: with any number of assets, any payoffs, and any number of
  households who share one CRRA coefficient but hold different endowment portfolios (each
  giving positive consumption in every state), an equilibrium exists. Prices are the marginal
  values at the aggregate endowment, `q j = Σ_s π s Y s ^ (−γ) d j s`; each household sells its
  endowment and buys the share `a i` (its wealth over total wealth) of the market portfolio, which
  is optimal for it, and asset markets clear asset by asset. Households trade whenever their
  endowment portfolio is not a multiple of the aggregate one.

Limits: one date and common beliefs. The equilibrium theorem needs a common CRRA coefficient;
existence of equilibrium with many assets and heterogeneous risk aversion (stage 366 covers two
assets) is not proved here. For that one would also need existence of each household's optimum
at arbitrary no-arbitrage prices and continuity of demand in a multi-dimensional price, followed
by a fixed point argument; none of these is in this file. Uniqueness of the equilibrium and
multi-date economies are not covered.
