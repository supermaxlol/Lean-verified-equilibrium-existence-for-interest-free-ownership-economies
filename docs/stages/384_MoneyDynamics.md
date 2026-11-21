# Stage 384: local dynamics, inflation along collapsing paths, and the case `γ > 1`

Lean 4.35 + Mathlib. 30 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/MoneyDynamics.lean`](../../formal/MoneyDynamics.lean).

This file continues stage 381 (`MoneyTransition`) for the overlapping-generations economy with
money growing at rate `μ > −1`. The definitions are copied from stage 381 so the file is
self-contained. Notation:

* young side `Av x = x (e1 − x) ^ (−γ)`, old side `Bv y = y (e2 + G y) ^ (−γ)`;
* `K = β G / (1 + μ)` (`Kc`); the forward map is `Av (m t) = K · Bv (m (t+1))`;
* inflation between two dates `infl x y = (1 + μ) x / (G y)` (the reciprocal of the gross
  return on money of stage 381); the stationary inflation factor is `(1 + μ) / G`.

## What is proved

**1. Existence of the next step.**
* `Bv_unbounded` (`γ < 1`): `Bv` takes arbitrarily large values.
* `fwd_existsUnique` (`γ < 1`): every `m t ∈ (0, e1)` has exactly one successor `m (t+1) > 0`;
  `fwd_function`: so the forward map is a genuine function on `(0, e1)`.
* `fwd_exists_one` (`γ = 1`): `Bv` is bounded by `1 / G`, and a successor exists iff
  `Av (m t) < K / G`; `fwd_exists_one_iff` restates this as `m t (1 + μ + β) < β e1`.

**2. Local instability of the stationary point `m*`.**
* `Av_hasDeriv`, `Bv_hasDeriv`: explicit derivatives (`HasDerivAt`) `dAv`, `dBv`.
* `Av_strictMono`: `Av` is strictly increasing on `(0, e1)` for every `γ > 0`.
* `slope_eq`: at `m*`, `Av'(m*) / (K Bv'(m*)) = N / D` with
  `N = 1 + γ m* / (e1 − m*)` (`Nn`) and `D = 1 − γ G m* / (e2 + G m*)` (`Dd`).
* `fwd_slope`: if `f` is any forward map near `m*` (i.e. `Av x = K Bv (f x)` for `x` near `m*`)
  with `f m* = m*` and `f` differentiable at `m*`, then `f'(m*) = N / D`.
* `slope_gt_one`: `D > 0 ⇒ N / D > 1`; `Dd_pos_of_le_one`: `D > 0` whenever `γ ≤ 1`;
  `fwd_slope_gt_one`: hence for `γ ≤ 1` the forward slope at `m*` exceeds `1`.
* `Dd_neg_iff`: `D < 0 ⇔ e2 + G m* < γ G m*` (only possible for `γ > 1`, `one_lt_of_Dd_neg`);
  `slope_neg`, `fwd_slope_neg`: then the slope is negative.
* `slope_flip_iff`: when `D < 0`, the slope is `< −1` iff `−D < N`, i.e.
  `γ G m* / (e2 + G m*) < 2 + γ m* / (e1 − m*)`; `slope_flip_of_le_two`: this always holds when
  `γ ≤ 2`. So a slope in `(−1, 0)` (a stable oscillatory forward map) requires `γ > 2`.

**3. Inflation along collapsing paths.**
* `infl_path`: along any path, `infl (m t) (m (t+1)) = β (e2 + G m (t+1)) ^ (−γ) / (e1 − m t) ^ (−γ)`.
* `infl_strictMono`: along any strictly decreasing path, inflation is strictly increasing.
* `infl_limit`: along any path converging to `0`, inflation converges to `β (e1 / e2) ^ γ`
  (the autarky marginal rate of substitution). NOTE: this is the correct limit; the conjectured
  formula `(1 + μ) / G · (e1 / e2) ^ γ / β` proposed in an earlier draft is not right.
* `infl_limit_gt`: if a stationary point exists, `(1 + μ) / G < β (e1 / e2) ^ γ`.
* `antitone_path_zero` (any `γ > 0`): a monotonically decreasing path starting below `m*` goes to `0`.
* `infl_below` (`γ ≤ 1`, `m 0 < m*`): inflation is strictly increasing, converges to
  `β (e1 / e2) ^ γ`, and this limit is strictly above the stationary inflation `(1 + μ) / G`.
  Both the monotone statement and the limit are proved.

**4. The case `γ > 1`.**
* `Av_surj`, `back_existsUnique` (any `γ > 0`): every `m (t+1) > 0` has exactly one
  predecessor `m t ∈ (0, e1)`; the backward map is well defined.
* `Bv_two_example`, `fwd_multivalued` (`γ = 2`, `G = e2 = 1`): `Bv (1/2) = Bv 2`, so for any
  `β, μ, e1` there is `m t ∈ (0, e1)` with two distinct successors `1/2` and `2`.
* `cycle_path`: an explicit **two-cycle equilibrium path**: with `γ = 3`, `β = 343/32768`,
  `G = 1`, `μ = 0`, `e1 = 20`, `e2 = 5/16`, the sequence `1, 8, 1, 8, …` is an equilibrium
  path. It is neither stationary nor convergent.

## Limits

* No general existence theorem for two-cycles: the flip argument (backward map `h`, slope of
  `h ∘ h` above `1` at `m*`, boundary behaviour, intermediate values) is not formalised. Only
  the explicit numerical example `cycle_path` is proved.
* `fwd_slope` assumes a differentiable local forward map through `m*`; its existence (an implicit
  function argument) is not proved. The slope formula, its sign, and the flip condition are
  proved as statements about `N / D`.
* No statement here on whether parameters with `D < 0` and a stationary point actually exist,
  other than `Dd_neg_iff`; no sunspot equilibria; no welfare comparisons.
* Monotonicity of inflation is proved along strictly decreasing paths; for `γ > 1` it is not
  shown which paths are decreasing.
