# Stage 324: The Mantel utility is not lower semicontinuous on a finite price set

Lean 4.35 + Mathlib. 28 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file reproduces stage 316 in full and adds 8 declarations.)

## Results
- `inf_mem_T`, `uu_range_finite`: if the price set `P` is finite, the infimum level of every bundle is `0`, `2` or the `k`-th coordinate of some price in `P`. So the utility takes finitely many values.
- `uu_at_choice`: the trade chosen at a price `p ∈ P` has utility at least `-1`.
- `uu_far`: a bundle below every chosen trade has utility `-2`.
- `not_lsc`: hence the utility is not lower semicontinuous. It is upper semicontinuous (stage 316), so lower semicontinuity would make it continuous. A continuous function on the connected space `ℝ^S` that reaches both `-2` and a value of at least `-1` must take infinitely many values.
- `mantel_not_lsc`, `mantel_not_continuous`: the same holds for the utilities built in stages 306, 307 and 316 whenever the price set is finite and non-empty.

## Reading
Stage 316 showed the convex-hull utility is upper semicontinuous. This stage shows that is the best possible for that construction: on finite price sets it is a step function and fails lower semicontinuity. For finite price sets, continuous (Afriat) utilities are already available from stage 296. On a continuum of prices, a continuous utility needs a different construction (Mantel 1974, Debreu 1974), and that is not formalised here.

## Limits
- Only finite price sets are covered. For an infinite `P` (for example Debreu's `S_ε`), whether this utility is lower semicontinuous is not settled here.
- This is a negative result about one construction. It does not say continuous rationalising preferences fail to exist.
