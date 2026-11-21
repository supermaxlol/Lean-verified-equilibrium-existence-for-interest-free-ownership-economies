# Stage 377: a growing money supply, its welfare cost, and a money supply that responds to real balances

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/EndogenousMoney.lean`](../../formal/EndogenousMoney.lean).

Stage 369 treated a fixed stock of fiat money in the stationary overlapping-generations
economy. This file lets the money stock grow, `M (t + 1) = (1 + μ) M t` with `μ > −1`, the new
money being handed out lump-sum to the old, and then lets the growth rate respond to the state
of the economy through a rule `μ = f m`.

Setting (as in stage 369): generations of relative size `G > 0`, endowments `e1, e2 > 0`,
lifetime utility `u (c₁) + β u (c₂)` with `β > 0` and `u' c = c ^ (−γ)`, `γ > 0`. Write
`R = G / (1 + μ)` (`ret`) and `τ = μ R m` (`tr`). A young household takes the price path and the
transfer `τ` as given and chooses real balances `s`: it consumes `e1 − s` young and
`e2 + τ + R s` old.

* `price_return`, `young_balances`, `own_money`, `transfer_value`, `old_total`: along the
  stationary path `p t = M t / (N t m)` the money market clears, money returns `R`, the transfer
  is worth `τ` per old person, and an old person's total real wealth from money is `G m`.
* `cons_id`: `e2 + τ + R m = e2 + G m`, so the stationary allocation is feasible.
* **`eq_iff`**: `m` is a stationary monetary equilibrium (optimal choice among all feasible
  non-negative holdings, given `τ`) iff `0 < m < e1` and
  `(e1 − m) ^ (−γ) = β R (e2 + G m) ^ (−γ)`.
* **`exists_iff`**: one exists iff `e1 ^ (−γ) < β (G / (1 + μ)) e2 ^ (−γ)`; enough money
  growth (inflation) destroys the value of money.
* **`eq_unique`**: it is unique.
* **`balances_anti`**: real balances strictly fall as `μ` rises (the inflation tax).
* **`golden_rule`**: steady-state welfare `u (e1 − m) + β u (e2 + G m)` is highest at `μ = 0`:
  for every `μ`, welfare at the `μ`-equilibrium is at most welfare at the `μ = 0` equilibrium, and
  strictly below it when `μ ≠ 0`. So with lump-sum transfers to the old, neither inflation nor
  deflation (a Friedman-rule contraction) improves on a constant money stock in steady state.
* **`feedback_exists`**: let the growth rate respond to real balances, `μ = f m`, with `f`
  continuous on `[0, e1]` and `f > −1` there. If `e1 ^ (−γ) < β (G / (1 + f 0)) e2 ^ (−γ)`, there
  is a stationary equilibrium `m` with money growing at `f m`. **`feedback_unique`**: if `f` is
  non-decreasing (money grows faster when balances are higher), it is unique.

Reading: money that pays no interest and whose supply grows, at a fixed rate or by a rule
that responds to the economy, has a value pinned down by the Euler equation; growth of the
money supply works as a tax on money holders, and in steady state the best constant rule is
to keep the stock fixed.

Limits: stationary equilibria only (no transition paths, no stability). New money is paid
lump-sum to the old; other injection schemes (to the young, proportional to holdings, through
government spending or lending) are not treated. The welfare result compares steady states
for the newborn generations only and ignores the initial old. The feedback rule depends on
current real balances only; for `f` that falls with balances uniqueness is not proved. There
is no inside (bank) money, credit or interest, so this is not a model of money created by
lending.
