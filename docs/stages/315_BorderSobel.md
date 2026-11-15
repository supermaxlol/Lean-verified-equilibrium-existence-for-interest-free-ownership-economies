# Stage 315: The Border–Sobel optimal audit schedule

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/BorderSobel.lean`.

## Setting
Finite states `S`. Output `y`, repayment schedule `R ≤ y`. Reporting `m` triggers an audit with probability `a m`.
A detected lie forfeits all output (the maximal penalty, as in Border–Sobel 1987 and stage 308).
Truth-telling: `IC y R a :  ∀ s m, (1 − a m)(y s − R m) ≤ y s − R s`.

Define `g s m = (R s − R m)/(y s − R m)` when `R m < R s`, else `0`, and `astar m = max_s g s m`.

## Results
* `ic_iff`: an audit schedule with values in [0,1] is IC **iff** `astar ≤ a` pointwise.
* `astar_ic`: `astar` is itself IC, so it is the least IC schedule.
* `cost_min`: `astar` minimizes expected audit cost `Σ π m · c · a m` over all IC schedules.
* `top_no_audit`: the report with the highest repayment is never audited.
* `astar_antitone`: lower reported repayments are audited more (Border–Sobel monotonicity).
* `astar_lt_one`: if `R < y`, no report is audited with certainty. Random audits strictly beat
  deterministic (Townsend/Gale–Hellwig) verification.
* Helpers: `g_nonneg`, `g_le_one`, `pair_iff`, `astar_nonneg`, `astar_le_one`.

## Honest limits
The audit schedule is optimal **for a given repayment schedule `R`**. The joint optimization over `R`
under the lender's break-even constraint (the full Border–Sobel program, including their result that
the optimal `R` is weakly increasing) is **not** proved. Commitment to audit and a collectable maximal
penalty are assumed. With a bounded penalty, see stage 313.
