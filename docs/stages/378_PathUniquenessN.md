# Stage 378: a unique path at every finite horizon, heterogeneous patience, `γ` near one

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/PathUniquenessN.lean`](../../formal/PathUniquenessN.lean).

Stage 373 proved uniqueness of the stage 364 equilibrium path with heterogeneous patience and
`γ ≠ 1` for horizon two. This file proves it for every finite horizon `N`, under a band on `γ`
that narrows with `N`. The stage 364 definitions are restated unchanged (`B`, `amp`, `T`, `F`,
`ex`, `rr`, `savN`, `IsEqN`).

The argument is a ratio contraction, not the date-by-date comparison of stage 373. Let `L ≥ 1`
be the largest ratio `max (Q' t / Q t) (Q t / Q' t)` between two equilibria over the dates
`t < N`, and let `e ≥ |ex γ| = |1 / γ − 1|`, `ε = e N`.

* `F_ratio`, `sav_ratio`: returns within a factor `L` move every saving rate by at most `L ^ ε`
  (the annuity sum `F` changes by at most `(L ^ e) ^ (N − t)`, and `F / (1 + F)` by no more).
* `date_step`: if the date-`t` holdings of the two paths are within `β`, then date-`t`
  clearing puts the returns within `L ^ ε β` and the date-`t + 1` holdings within
  `(L ^ ε β) ^ 2`.
* `propagate`: holdings at date `t` are within `L ^ ((2 ^ (t + 1) − 2) ε)`, so returns at date
  `t < N` are within `L ^ ((2 ^ N − 1) ε)`.
* **`unique_N`**: two equilibria with positive returns at every date `t < N` have equal returns
  at those dates and equal distributions at every date `t ≤ N`, if
  `(2 ^ N − 1) e N < 1` for some `e ≥ |ex γ|`, with `b ≥ 0`, `x0 ≥ 0`, `g ≥ 0`, `amp ≥ 0`,
  `g σ c ≥ 0`. (The largest ratio `L` is then at most `L ^ κ` with `κ < 1`, so `L = 1`.)
* **`unique_N_band`**: the same with `γ > 0` and `|1 / γ − 1| N (2 ^ N − 1) < 1`.
* `unique_three_period`: horizon three under `|1 / γ − 1| < 1 / 21`.

Limits. The band is a sufficient condition from crude bounds, not a sharp one. It shrinks
roughly like `2 ^ (−N) / N`, so it gives no uniform statement in `N` and none for the
infinite horizon, which is not covered. At horizon two it (`|1 / γ − 1| < 1 / 6`) is narrower
than the stage 373 band `1 / 2 < γ ^ 2 < 2`; this file does not supersede stage 373 there.
Outside the band uniqueness is neither proved nor refuted, and no example of two distinct
equilibrium paths is given. Uniqueness is among equilibria with positive returns at every
date `t < N`; existence is not addressed here.
