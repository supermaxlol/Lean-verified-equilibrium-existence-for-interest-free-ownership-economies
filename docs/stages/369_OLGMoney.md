# Stage 369: valued fiat money in a stationary overlapping-generations economy

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/OLGMoney.lean`](../../formal/OLGMoney.lean).

A first, narrowly scoped treatment of money inside the model. Each period a generation is born,
lives two periods, receives `e1 > 0` when young and `e2 > 0` when old, and has utility
`u c₁ + β u c₂` with `β > 0` and marginal utility `c ^ (−γ)`, `γ > 0` (log and every power
utility). Each generation is `G > 0` times as large as the one before. A fixed stock `M > 0` of
fiat money, which pays no interest, is the only asset. A young household that holds real
balances `s` consumes `e1 − s` young and `e2 + G s` old, because along a stationary path the
price level falls at the growth rate (`price_return`, `price_clears`), so money returns exactly
`G`.

* `E_anti`: the Euler expression `E s = −(e1 − s) ^ (−γ) + β G (e2 + G s) ^ (−γ)` is strictly
  decreasing in saving.
* `strict_opt`, `optimal`: a zero of `E` is the strict maximiser of lifetime utility over all
  affordable saving levels (mean value theorem).
* `root_unique`, `mon_eq_unique`: there is at most one zero, so at most one stationary monetary
  equilibrium.
* **`exists_iff`**: a stationary monetary equilibrium (positive real balances, chosen
  optimally among all non-negative money holdings) exists **if and only if** the Samuelson
  condition `e1 ^ (−γ) < β G e2 ^ (−γ)` holds: at autarky the young would like to save at the
  return `G`, that is, the autarky interest rate is below the growth rate.
* `welfare`: in that equilibrium every generation is strictly better off than in autarky, and
  the initial old consume `e2 + G m > e2`.

Reading: money that pays no interest can still have value and improve on autarky; its return
is the growth rate of the economy, not an interest payment. When `G = 1` the condition reads
`e1 ^ (−γ) < β e2 ^ (−γ)`.

Limits: stationary equilibria only. The non-stationary paths (including the well-known
continuum of paths converging to the non-monetary state) and the stability of the monetary
steady state are not studied. There is one good, one type per generation, no production, no
banks, credit or money creation, and the money stock is fixed. This is not a theory of
endogenous money supply.
