# Stage 292 — The Mantel utilities of stage 262 are not continuous

Lean 4.35 + Mathlib. 3 new audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file inlines stages 256, 262 and 287.)

- `util_unaffordable`: a net trade that is non-negative and positive somewhere is affordable at no strictly positive price, so its utility is `0`, the top value.
- `util_zero_neg`: the zero trade has strictly negative utility.
- `util_not_continuous`: each Mantel utility is discontinuous at the zero trade (the trades `ε eᵢ` tend to zero but keep utility `0`).

Reading: this settles the continuity question for the construction used in stages 262 and 287. The answer is negative: those utilities are monotone and quasi-concave but cannot be continuous. The classical Sonnenschein–Mantel–Debreu theorem with continuous, monotone, convex preferences therefore needs a different construction (Mantel 1974, Debreu 1974), which is not formalised here.

Limits: the discontinuity is shown at the zero trade; the classical continuous version remains open in this program.
