# Stage 294: Wilson aggregation for n households

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Any index type `I` of households with linear sharing rules `c_i = b_i Y + k_i` that are efficient (common marginal-utility ratio) over an open set `U` of aggregate outcomes.

## Results
- `wilson_converse_all`: every pair of households has equal risk tolerance at its share on `U`.
- `common_cautiousness`: there is a common cautiousness `C` for all households.
- `wilson_hara_all`: every pair has the same HARA cautiousness parameter.
- `tolerance_sum` (finite `I`, `Σ b_i = 1`): aggregate risk tolerance is the sum of the individual tolerances, which is the representative-agent identity.

## Reading
This is the n-household form of stage 290: linear sharing implies HARA with a common cautiousness, which is exactly when a representative agent exists.

## Limits
Smoothness and strict concavity are assumed as in stage 290. The result is local to `U`.
