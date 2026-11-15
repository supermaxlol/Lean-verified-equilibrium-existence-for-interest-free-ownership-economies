# Stage 264 — The log saver's rule is optimal against whole plans

Lean 4.35 / Mathlib, 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`,
no errors, no warnings. The stage-258 source (Bellman contraction and the closed-form
saver value) is inlined.

Setting: discount factor `0 < β < 1`, gross return `R > 0`, log felicity. A plan is a
consumption path `c` and a wealth path `W` with `W (t+1) = R * (W t - c t)` and
`0 < c t < W t`. `saverValue β R W` is the closed-form value function of stage 258.

- `truncated_le` — for every horizon `T`, discounted utility up to `T` plus
  `β ^ T * saverValue (W T)` is at most `saverValue (W 0)`.
- `truncated_eq` — the rule "consume the fraction `1 - β` of wealth" gives equality at
  every horizon.
- `rule_tail` — along the rule the tail term `β ^ T * saverValue (W T)` tends to zero.
- `rule_value` — along the rule discounted utility converges to `saverValue (W 0)`.
- `rule_optimal` — any plan whose discounted utility converges and whose tail term has a
  non-negative limit has discounted utility at most `saverValue (W 0)`.

Reading: the saving rule assumed in stage 263 is optimal among all plans that satisfy the
tail condition, not only against one-step deviations.

Limits: the tail condition is a hypothesis; it is not shown to hold for every feasible
plan, and plans whose discounted utility does not converge are not covered. Constant
return `R`. Log utility only.
