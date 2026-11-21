# Stage 387: uniqueness of the horizon-two equilibrium path for every γ > 0

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/PathUniquenessH2.lean`](../../formal/PathUniquenessH2.lean).

Stage 383 (`PathUniquenessGS.lean`) proved path uniqueness for the stage 364 model only for
`0 < γ ≤ 1` (and, for larger `γ`, only between ordered paths). This file removes the
restriction on `γ` **at horizon `N = 2`**.

## What is proved

`unique_h2`: in the stage 364 model at horizon `N = 2` (definitions restated verbatim from
stage 364/383: `B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`), any two equilibria whose
returns `Q 0, Q 1` are positive have the same returns and the same wealth distributions at
dates 0, 1, 2. Assumptions: `γ > 0`, `b ≥ 0`, `x0 ≥ 0`, `g ≥ 0`, `amp g σ ≥ 0`,
`g σ c ≥ 0`. No ordering of the two paths and no band on `γ` is assumed.

## How

* In log returns `X = log Q0`, `Y = log Q1` the date-0 clearing condition is `Φ(X, Y) = 1`,
  with `Φ` strictly increasing in `X` (`1 + E·n > 0` for `E = (1-γ)/γ > -1`). Every `Y` has a
  clearing `X` (`curve_exists`, intermediate value theorem), giving a curve `X = p(Y)`.
* `curve_deriv`: `p` is differentiable with slope `-Φ_Y/Φ_X`, via Mathlib's bivariate
  implicit function theorem; the global curve agrees with the local implicit function by
  strict monotonicity.
* `slope_pos`: the date-1 clearing residual `e^Y Σ α_h (amp·w_h + gσc)` has positive
  derivative along the curve. The core is an algebraic inequality in the weighted moments
  `S1, S2, M, P, R2`, proved separately for `E ≥ 0` and `-1 < E < 0`.
* `resid_strictMono` then gives at most one `Y`, hence one `X`, hence one path.

## Limits (stated honestly)

* Horizon two only. Longer horizons (`N ≥ 3`) for `γ > 1` remain open here: the reduction
  to one unknown along a clearing curve does not carry over directly.
* Uniqueness only. Existence at `N = 2` is not proved in this file.
* Positive returns are assumed of both equilibria (`Q t > 0`), as in stage 383.
* Same model as stage 364: one good, log-linear savings rule `F`, the `T` transition.
  Nothing here is about the general multi-good economy.
* The monotonicity was first found by numerical exploration; the Lean proof does not
  depend on that search.
