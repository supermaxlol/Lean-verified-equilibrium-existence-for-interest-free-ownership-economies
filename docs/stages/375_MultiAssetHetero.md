# Stage 375: equilibrium with many assets and heterogeneous CRRA (complete markets)

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/MultiAssetHetero.lean`](../../formal/MultiAssetHetero.lean).

Stage 366 proved existence with two assets (equity and a bond) and heterogeneous CRRA; stage 371
proved existence with any number of assets but a common CRRA coefficient. This file proves
existence with any number of assets and heterogeneous CRRA coefficients **when the assets span
every state-contingent payoff** (complete markets), by the Negishi method.

Setup: households `i` with endowment `e i s > 0` in each state, CRRA marginal utility
`c ^ (−γ i)` (`γ i > 0`), common probabilities `π s > 0`; aggregate output `agg e s`.

* `root_exists`, `F_lt`: for welfare weights `l ≥ 0`, not all zero, and output `y > 0`, the
  multiplier `m > 0` with `Σ i (l i / m) ^ (1 / γ i) = y` exists and is unique.
* `mu_continuous`: that multiplier depends continuously on the weights on the simplex.
* `walras`: the transfers `T i` (value of the weighted Pareto allocation `alloc` minus the value
  of the endowment, at state prices `ψ s = π s · m s`) sum to zero.
* `exists_weights`: Brouwer on the simplex gives weights at which every transfer is zero, and
  every weight is positive.
* **`exists_ad_equilibrium`**: an Arrow–Debreu equilibrium in state-contingent claims: positive
  state prices and positive consumption, each household's consumption affordable and optimal
  among all affordable positive consumption plans, and every state market clears.
* **`exists_equilibrium_complete`**: with `J` assets whose payoffs `d j s` span every payoff and
  are non-redundant, and endowment portfolios paying a positive amount in every state, there are
  arbitrage-free asset prices `q j = Σ s ψ s d j s` and portfolios such that each portfolio
  costs the endowment portfolio, gives positive consumption, is optimal among all affordable
  portfolios with positive consumption, and every asset market clears.

Limits: one date, common beliefs, CRRA marginal utility. The asset result needs COMPLETE markets
(the spanning hypothesis); with incomplete markets the Negishi allocation need not be
attainable and the many-asset heterogeneous-CRRA existence remains open (stage 366 covers two
assets, stage 371 a common coefficient). Existence of each household's optimum at arbitrary
arbitrage-free prices and continuity of portfolio demand in prices are not proved here.
Uniqueness of the equilibrium is not proved.
