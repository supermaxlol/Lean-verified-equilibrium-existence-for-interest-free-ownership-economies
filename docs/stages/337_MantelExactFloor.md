# Stage 337: consumer-specific endowment floors

Lean 4.35 + Mathlib. 44 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `mantel_exact_floor`: the endowments only need to satisfy the consumer-specific floors `e_i s ≥ −mx_i(p_k) s` for every price `k`. Under these floors, the given `Z` (scale `1`) is the aggregate excess demand. The rest is as in stage 333:
  - continuous, concave, strictly monotone utilities;
  - unique maximisers;
  - nonnegative consumption;
  - binding budgets.
- `floor_of_Mbd`: the uniform stage-333 floor `Mbd p Z` implies these floors. So stage 337 strictly extends stage 333.
- `floor_sum_ge`: summed over consumers, the floors still imply the necessary aggregate condition `−Z k s ≤ ∑_i e_i s`.

## Reading
The gap left open in stage 333 narrows from "per-consumer `Mbd` versus aggregate `−Z`" to this: per good, `∑_i max_k(−mx_i(p_k) s)` versus `max_k(−Z k s)`. For example, an aggregate endowment `E` split in fixed shares `θ_i` works whenever `θ_i E s ≥ −mx_i(p_k) s` for all `i, k, s`.

## Limits
The remaining gap belongs to Debreu's one-consumer-per-good decomposition `mx`. No claim is made that another decomposition reaches the aggregate floor, or that it cannot. Finitely many prices only.
