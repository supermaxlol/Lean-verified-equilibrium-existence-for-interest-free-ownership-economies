# Stage 328: The Mantel utility is not lower semicontinuous on any compact price set, including `S_ε`

Lean 4.35 + Mathlib. 34 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file reproduces stages 316 and 324 in full and adds 6 declarations.)

## Results
- `K_sub_one`: every normalised price has `k`-th coordinate at most `1`, so the level-`1` set already contains every chosen trade, and every level set lies inside it.
- `uu_gap`: the utility never takes a value strictly between `-2` and `-1`. A bundle either lies in the level-`1` set (utility at least `-1`) or in no level set (utility exactly `-2`).
- `not_lsc_compact`: on any compact price set the utility is not lower semicontinuous. It is upper semicontinuous (stage 316), so lower semicontinuity would make it continuous. A continuous function on the connected space `ℝ^S` reaching `-2` and a value of at least `-1` would take the value `-3/2`, which the gap rules out.
- `mantel_not_lsc_compact`, `mantel_debreu_not_lsc`, `mantel_debreu_not_continuous`: the utilities of stages 306, 307 and 316 are not lower semicontinuous, hence not continuous, on any compact set of nonnegative normalised prices. That includes Debreu's domain `S_ε`.

## Reading
This removes the limit stated in stage 324, which covered finite price sets only. Upper semicontinuity (stage 316) is the best the convex-hull construction can give on any compact domain, finite or continuous. The obstruction is the jump between "reached at some level" and "never reached". A continuous utility on a continuum of prices therefore needs a different construction (see stage 330).

## Limits
- This is a negative result about one construction. It does not say continuous rationalising preferences fail to exist.
