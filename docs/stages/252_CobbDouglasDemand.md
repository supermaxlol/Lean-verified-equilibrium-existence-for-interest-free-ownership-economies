# Stage 252 — Cobb–Douglas demand derived from utility maximisation

Lean 4.35 / Mathlib, 5 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: weights `α s > 0` summing to one, prices `p s > 0`, wealth `w > 0`, utility
`∑ α s * log (x s)`.

- `demand_budget` — the bundle `α s * w / p s` spends exactly `w`.
- `demand_optimal` — it gives at least the utility of every strictly positive affordable bundle.
- `demand_unique` — every other such bundle gives strictly less.
- `term_le`, `term_lt` — the per-good inequality behind both.

Reading: the demand rule that stage 250 assumed is the unique utility-maximising choice, so
the ownership-neutrality results of stage 250 now rest on preferences, not on a posited rule.
Limits: strictly positive bundles only (log utility); identical weights across households
are still an assumption of stage 250.
