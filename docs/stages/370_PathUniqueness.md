# Stage 370: when the transition path is unique

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/PathUniqueness.lean`](../../formal/PathUniqueness.lean).

Stage 364 proved that a finite-horizon perfect-foresight equilibrium path exists for every
`γ > 0` (Brouwer), but not that it is unique. This file gives sufficient conditions for
uniqueness. The definitions of stage 364 are restated (`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`,
`IsEqN`), unchanged.

* `qs_eq`, `e_anti`: a household's saving rate times the return, `Q · F / (1 + F)` with
  `F = b Q ^ ((1 − γ) / γ) (1 + G)`, equals `1 / (1 / Q + 1 / (b (1 + G) Q ^ (1 / γ)))`, which is
  strictly increasing in `Q` for every `γ > 0`. So at a single date, with the distribution and the
  households' continuation plans `G` held fixed, at most one return clears the market.
* `date_unique`: that date-by-date statement for heterogeneous patience and non-negative
  ownership shares.
* **`unique_log`** (`γ = 1`, any heterogeneous patience): saving rates do not depend on returns,
  so the distribution path and the return path are pinned down date by date. Two equilibria over
  the same horizon from the same start agree at every date.
* **`unique_common`** (any `γ > 0`, common patience `b h = β₀`): every household saves at the
  same rate, so the distribution path does not depend on returns; returns are then pinned down
  by backward induction from the last date using `date_unique_common`. Two equilibria with
  positive return paths agree at every date.
* **`unique_one_period`** (any `γ > 0`, heterogeneous patience, horizon one): the equilibrium is
  unique.
* `date_unique_path`: for any horizon and heterogeneous patience, if two equilibria have the same
  distribution at date `t` and every household has the same continuation plan, they have the
  same return at `t`.

Limits: these are sufficient conditions. Uniqueness for heterogeneous patience with `γ ≠ 1` and
horizon above one is NOT proved: the distribution path then depends on returns and returns on
future distributions, and no contraction or monotonicity bound for that coupled system is given
here. No example of two distinct equilibrium paths is given either, so whether uniqueness can
fail there is open. Uniqueness is among equilibria with positive returns (`unique_common`,
`unique_one_period`); returns after the horizon play no role in the equilibrium conditions and
are not compared. The infinite-horizon path of stage 364 is not covered.
