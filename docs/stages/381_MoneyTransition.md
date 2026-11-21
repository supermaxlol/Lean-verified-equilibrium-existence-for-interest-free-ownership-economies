# Stage 381: transition dynamics of the money-growth economy of stage 377

Lean 4.35 + Mathlib. 14 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/MoneyTransition.lean`](../../formal/MoneyTransition.lean).

Stage 377 studied stationary equilibria of the overlapping-generations economy with a money
stock growing at rate `μ > −1` (new money handed lump-sum to the old). This file studies the
non-stationary paths of the same economy.

Setting: generations of relative size `G > 0`, endowments `e1, e2 > 0`, lifetime utility
`u (c₁) + β u (c₂)` with `β > 0`, `u' c = c ^ (−γ)`, `γ > 0`. Let `m t` be real balances per
young person at date `t`. Money bought at `t` returns `R (t+1) = G m (t+1) / ((1 + μ) m t)`
(`ret`), and an old person at `t + 1` consumes `e2 + G m (t+1)` (transfer plus own money, as in
stage 377 `cons_id`). The young household's Euler equation
`(e1 − m t) ^ (−γ) = β R (t+1) (e2 + G m (t+1)) ^ (−γ)` is, after multiplying by `m t`,
the forward map

  `Av (m t) = K · Bv (m (t+1))`, where `Av x = x (e1 − x) ^ (−γ)`,
  `Bv y = y (e2 + G y) ^ (−γ)`, `K = β G / (1 + μ)` (`Kc`).

An equilibrium path (`IsPath`) is a sequence with `0 < m t < e1` satisfying this at every date;
a stationary point (`IsStat`) is a constant one, which by `stat_iff` is exactly the stationary
Euler equation of stage 377.

## What is proved

* `path_euler`: the forward map is equivalent to the household Euler equation with return `ret`.
* `stat_iff`, `stat_unique`: the stationary point is the stage 377 equilibrium; it is unique.
* `sign_below`, `sign_above`: `Av < K Bv` strictly below the stationary point, `Av > K Bv`
  strictly above it (no restriction on `γ`).
* **Well-posedness** (assuming `γ ≤ 1`):
  - `Bv_strictMono`: `y ↦ y (e2 + G y) ^ (−γ)` is strictly increasing on `(0, ∞)`;
  - `next_unique`: each `m t` admits at most one `m (t+1) > 0`;
  - `next_exists_iff`: one exists iff `Av (m t) ≤ K · Bv Y` for some `Y > 0`, i.e. iff
    `Av (m t) / K` lies in the range of `Bv` (this direction needs no restriction on `γ`).
* **Phase portrait** (`γ ≤ 1`, stationary point `m*`):
  - `path_below`: if `m 0 < m*`, the path is strictly decreasing, stays below `m*`, and
    converges to `0` (the value of money vanishes asymptotically);
  - `path_ret_below`: along such a path the return on money is below the stationary return
    `G / (1 + μ)` at every date, i.e. inflation exceeds the stationary inflation rate;
  - `no_path_above`: no equilibrium path starts above `m*` (the path would be strictly
    increasing, stay bounded away from `e1` by the budget, converge, and its limit would be a
    second stationary point).
* **Indeterminacy** (`γ ≤ 1`):
  - `path_classify`: every equilibrium path is either the constant path `m*` or converges to `0`;
  - `path_exists`: every `m 0 ∈ (0, m*]` starts an equilibrium path (which is antitone).
* **Comparative dynamics** `next_mono_mu`: for a given `m t`, a higher money growth rate `μ`
  requires a strictly higher `m (t+1)` (`γ ≤ 1`).

## Limits

* The monotonicity hypothesis `γ ≤ 1` is used for uniqueness of the forward step and for the
  whole phase portrait. For `γ > 1`, `Bv` is not monotone, the forward map can be multi-valued,
  and cycles or sunspot paths are not excluded; nothing here covers that case.
* Existence of the next step is characterised through the range of `Bv`; the explicit fact that
  `Bv` is unbounded when `γ < 1` (so a step always exists) is not proved here.
* The stationary point `m*` is taken as a hypothesis; its existence condition is stage 377
  `exists_iff`.
* Inflation along a decreasing path is shown to exceed the stationary rate at every date; it is
  NOT shown to rise monotonically over time.
* Local instability of `m*` as a derivative statement (slope of the forward map above 1) is not
  proved; only the global statement that paths starting off `m*` move away from it.
* The money growth rate is constant along the path; no feedback rules, no welfare comparison of
  paths, no initial-old allocation question.
