# Stage 277 — The saving rule is optimal with no tail condition

Lean 4.35 / Mathlib, 2 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-264 source is inlined.

Setting: stage 264 — log saver, discount `0 < β < 1`, gross return `R > 0`, wealth
`W (t + 1) = R * (W t - c t)`, consumption `0 < c t < W t`.

- `step_bound` — `S (T + 1) - β * S T ≤ (1 - β) * (saverValue (W 0) - β ^ T * valueConst)`,
  where `S T` is discounted utility up to `T`.
- `rule_optimal_all` — if the discounted utility of a feasible plan converges to `U`,
  then `U ≤ saverValue β R (W 0)`.

Reading: stage 264 assumed that the tail term `β ^ T * saverValue (W T)` has a
non-negative limit. That hypothesis is gone. Since `c t < W t`, the tail is bounded
below by the next term of the utility series, which tends to zero.

Limits: log utility, constant return, no labour income. Convergence of the plan's
discounted utility is still assumed; plans whose utility diverges to minus infinity are
trivially worse but are not covered by the statement.
