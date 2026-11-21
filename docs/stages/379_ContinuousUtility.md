# Stage 379: a continuous, monotone, quasi-concave utility for each Debreu consumer, for continuous excess demand

Lean 4.35 + Mathlib. 14 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ContinuousUtility.lean`](../../formal/ContinuousUtility.lean).

Stage 372 decomposed a continuous Walras excess demand into `n` trades `x_k` (the Debreu
decomposition) and stage 374 rationalised each trade by a monotone, quasi-concave utility
whose continuity was left open. This file closes that gap: the utility is continuous (indeed
Lipschitz in the bundle), for every continuous excess demand, not only Lipschitz ones.

Setup: prices are unit vectors `p · p = 1` with every coordinate at least `ε > 0` (`Peps ε`).
`z` is continuous on `Peps ε`, bounded by `M`, and satisfies Walras' law `p · z p = 0`.
With `A = M / ε + 1`, consumer `k`'s trade is `x_k(p) = w_k(p) (e_k − p_k p)` with weight
`w_k(p) = A p_k + z_k(p) ≥ ε`.

Construction: for a level `c`, a "piece" is any bundle within `(c − s) / K` in every coordinate
of the stage-374 upper set at an admissible level `s ≤ c`; `W_c` is the convex hull of the
pieces; `τ(y) = inf {c | y ∈ W_c}` capped at `2`; the utility is `u = −τ`, with
`K = 2 (n + 1) / ε`.

* `tau2_lip`, `util2_continuous`: `τ(y') ≤ τ(y) + K · dist y y'`, so `u` is continuous.
* `monotone_util2`: `u` is non-decreasing in every good.
* `quasiconcave2`: `u` is quasi-concave (each `W_c` is convex, `W_mono`).
* `W_below`, `tau2_trade`, `optimal2`: `u (x_k p) = −p_k` and `x_k(p)` maximises `u` on the
  budget `p · y ≤ 0`.
* `coord_ge2`, `unique2`: every other affordable bundle is strictly worse (uses only continuity
  of `x_k` at `p`).
* **`continuous_mantel_utility`**: `z = Σ_k x_k` on `Peps ε`, and each `x_k(p)` is the unique
  maximiser on `{p · y ≤ 0}` of a continuous, non-decreasing, quasi-concave utility.
* **`continuous_mantel_endowments`**: the same with endowments and non-negative consumption.
  Every consumer is endowed with `B = (M / ε + 1) + M` of every good and consumes
  `c_k(p) = B + x_k(p) ≥ 0` on `Peps ε`; then `z = Σ_k (c_k − B)` and `c_k(p)` is the unique
  maximiser of a continuous, non-decreasing, quasi-concave utility of consumption on the
  budget `p · y ≤ p · B`. This is the standard SMD set-up of individual demands from
  endowments, restricted to prices in `Peps ε` as in the textbook statement.

Honest limits (what this is NOT):
* Preferences are weakly, not strictly, monotone and not strictly convex; uniqueness of the
  maximiser holds at each `p` in `Peps ε` but comes from the construction, not from strict
  convexity of preferences.
* In `continuous_mantel_utility` bundles are net trades in `ℝ^n` with budget `p · y ≤ 0`.
  `continuous_mantel_endowments` adds endowments and shows consumption is non-negative at
  every price in `Peps ε`, but the utility is defined on all of `ℝ^n` and the maximum is over
  all of the budget set; it is in particular the maximum over non-negative bundles. The
  endowment `B` is common to all consumers and depends on `M` and `ε`.
* Prices are restricted to `Peps ε` (bounded away from the boundary); nothing is said about
  behaviour as prices approach the boundary.
* So this is a continuous-utility version of the Debreu decomposition with weak regularity, not
  the full Sonnenschein–Mantel–Debreu theorem with strictly monotone, strictly convex
  preferences. What is missing relative to that theorem is the strictness of preferences.
