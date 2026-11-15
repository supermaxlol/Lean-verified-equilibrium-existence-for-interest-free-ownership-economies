# Stage 287 — Mantel utilities: monotone and quasi-concave

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file inlines stage 262; only the new declarations are audited here.)

Setting: the utilities `Mantel.util i` constructed in stage 262, which rationalise any Walras-law excess demand on strictly positive prices as one maximising agent per good.

- `level_nonneg`, `afford_anti`, `afford_mix`: supporting lemmas (a larger trade is affordable at fewer prices; a mixture is affordable only where one of its parts is).
- `util_monotone`: more of every good is never worse.
- `util_quasiconcave`: a mixture is at least as good as the worse of its two parts.
- `util_nonpos`: utilities are bounded above by zero.
- `cutil_monotone`, `cutil_quasiconcave`: the same on consumption bundles, with `cutil i ω x = util i (x - ω)` for endowment `ω`.
- `consumption_convex`: the consumption set `x ≥ 0` is convex.

Reading: the Mantel agents of stage 262 have monotone, quasi-concave preferences, defined on a convex consumption set.

Limits: continuity of the utilities is NOT proved (the utility is a supremum over a price set that varies with the bundle). Strict monotonicity and strict quasi-concavity are not claimed. So this is not yet the full classical Mantel theorem.
