# Stage 360: productive capacity and the distribution of ownership

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/CapacityDistribution.lean`](../../formal/CapacityDistribution.lean).

Household `h` saves the fraction `β h` of wealth (stage 356) and owns the share `x h`. Saved
wealth becomes next period's productive capacity, which returns the gross factor `R`, so
capacity grows by `R * B x`, where `B x = ∑ h, β h * x h` is the aggregate saving rate.

* `capacity_path`: with a constant saving rate, `K n = (R B) ^ n K 0`.
* `saving_bounds`: if every `β h ∈ [lo, hi]`, then `lo ≤ B x ≤ hi`.
* `common_patience_neutral`: with a common `β`, `B x = β` for every distribution: the issuance
  rule then costs no growth at all.
* `saving_diff`: for two distributions, `B x − B x' = ∑ (β h − m) (x h − x' h)` for any `m`.
* `growth_cost_bound`: `|B x − B x'| ≤ (hi − lo) / 2 · ∑ |x h − x' h|`: changing the
  distribution changes capacity growth by at most half the spread of patience times the total
  share moved.
* `growth_cost_floor`: hence an issuance rule that moves a total share `T` costs at most
  `R (hi − lo) T / 2` of growth per period.

Reading: when people are equally patient, distribution and growth are independent. When they
differ, the growth cost of spreading ownership is bounded by the spread of patience and the
share moved, and can be weighed against the welfare gain of stage 362.
