# Stage 385: existence of two-cycles in the money economy, from the slope at `m*`

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/MoneyCycles.lean`](../../formal/MoneyCycles.lean).

Stage 384 found one explicit two-cycle (`γ = 3`, the path `1, 8, 1, 8, …`) but had no general
theorem. This file proves one. Definitions are copied from stage 384 (`MoneyDynamics.lean`, not
modified): `Av x = x (e1 − x) ^ (−γ)`, `Bv y = y (e2 + G y) ^ (−γ)`, `K = β G / (1 + μ)`, and a path
satisfies `Av (m t) = K · Bv (m (t+1))` with `0 < m t < e1`.

* `stat_unique` (any `γ > 0`): there is at most one stationary point `m*`.
* `Ai`, `hb`: the inverse of `Av` on `(0, e1)` and the backward map
  `hb y = Av⁻¹ (K · Bv y)`, defined for every `y > 0` and every `γ > 0`.
* `Ai_continuousAt`, `hb_continuousAt`: both are continuous (strict monotonicity + image
  a neighbourhood). `Ai_hasDeriv`: inverse-function derivative.
* `hb_hasDeriv`: the backward map is differentiable at `m*` with slope `D / N`, the reciprocal of
  the forward slope `N / D` of stage 384. This removes the stage-384 assumption that a
  differentiable local forward map exists: the backward map is constructed, not assumed.
* **`two_cycle_exists`**: if a stationary point `m*` exists and `N < −D` (backward slope below
  `−1`, i.e. forward slope in `(−1, 0)`), then there are `x ≠ y` with `m* < x < e1`,
  `0 < y < e1`, such that `x, y, x, y, …` is an equilibrium path. Proof: `φ(x) = hb (hb x) − x`
  has `φ(m*) = 0` and `φ'(m*) = (D / N)² − 1 > 0`, so `φ > 0` just right of `m*`; `φ(e1) < 0`
  because `hb` maps into `(0, e1)`; the intermediate value theorem gives a root `x`, and `x` is
  not stationary because `m*` is the only stationary point.
* `example_stat`, `example_flip`, `example_cycle`: the condition holds at
  `γ = 3, β = 343/32768, G = 1, μ = 0, e1 = 20, e2 = 5/16`, where `m* = 10/3`, `N = 8/5` and
  `−D = 61/35`.

Limits (honest):
* The condition `N < −D` is sufficient, not necessary; by stage 384 (`slope_flip_of_le_two`) it
  can only hold when `γ > 2`. When `D < 0` but `−D < N` (forward slope below `−1`), nothing is
  claimed about cycles.
* Existence only: no statement on the number of cycles, their stability, cycles of period
  above two, or sunspot equilibria.
* The theorem does not say the cycle found is the one of stage 384 (`1, 8`).
