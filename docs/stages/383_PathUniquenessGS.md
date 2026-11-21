# Stage 383: gross substitutes and the equilibrium path at every finite horizon

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/PathUniquenessGS.lean`](../../formal/PathUniquenessGS.lean).

Stages 370, 373 and 378 proved uniqueness of the stage 364 equilibrium path in special cases:
log utility, common patience, horizon one, horizon two under a band on `γ`, and every finite
horizon under a band that narrows with the horizon. This file uses the sign of the saving
response for `0 < γ ≤ 1` instead of a band. The stage 364 definitions are restated unchanged
(`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`).

* `F_mono`, `savN_mono`: for `0 < γ ≤ 1` (so `ex γ ≥ 0`) and `b ≥ 0`, a household's saving
  rate at any date is non-decreasing in the returns of that date and of every later date
  (gross substitutes across dates). `ex_nonneg` records `0 ≤ ex γ` for `0 < γ ≤ 1`.
* `date_eq`: at a date where the two paths have the same nonnegative holdings, where the
  returns are ordered `Q t ≤ Q' t` and every saving rate is ordered the same way, clearing
  forces equal returns and equal holdings at the next date.
* **`ordered_unique`**: for `0 < γ ≤ 1`, every horizon `N`, heterogeneous patience `b ≥ 0`,
  `x0 ≥ 0`, `g ≥ 0`, `amp ≥ 0`, `g σ c ≥ 0`: two equilibria whose returns are positive and
  ordered (`Q t ≤ Q' t` for every `t < N`) have the same returns at every `t < N` and the same
  distributions at every `t ≤ N`. No band condition is needed.
* **`no_higher_path`**: equivalently, no equilibrium path has returns weakly above another's at
  every date and strictly above at some date.
* **`unique_log`**: for `γ = 1` (log utility) two equilibria coincide at every horizon with no
  further condition: saving rates do not depend on returns, so the path is determined forward.

Limits. The full statement aimed at, that any two equilibria with positive returns coincide
for `0 < γ ≤ 1` with no ordering assumption, is not proved here. The order argument compares
the two paths at one date at a time and needs the returns of one path to lie weakly above the
other's at every date. A max-ratio argument across dates was considered and not completed:
when returns rise at some dates and fall at others, the change in saving rates and the induced
redistribution of holdings have no sign that the argument can use. So for unordered pairs of
equilibria with `γ ≠ 1`, uniqueness at horizon above one rests on the band conditions of
stages 373 and 378. The case `γ > 1` (`ex γ < 0`, saving falling in returns) is not covered by
any result in this file. Uniqueness is among equilibria with positive returns at every date
`t < N`; existence is not addressed. The infinite horizon is not covered.
