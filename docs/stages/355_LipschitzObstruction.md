# Stage 355: why a uniform Lipschitz bound cannot close continuous Mantel

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `lipschitz_of_tendsto`, `lipschitz_of_eventually`: a pointwise limit of (eventually) `L`-Lipschitz functions is `L`-Lipschitz.
- `unbounded_constants`: so if `z` is not Lipschitz, **every** Lipschitz approximating sequence has constants that are not eventually bounded by any `L`.
- `sqrt_not_lipschitz`: `√` on `[0, 1]` is continuous and not Lipschitz, so such `z` exist.
- `afriat_scale_vanishes`: along `L_m → ∞`, the stage-353 condition `L_m ≤ c A_m` forces `A_m → ∞` and the Afriat multiplier bound `1/(A_m(1 − δ0)) → 0`. The constructed utilities flatten in the limit.

## Reading
The "uniform Lipschitz bound" route to continuous Mantel (tier item 7) is **closed**. A uniform bound exists only when `z` is already Lipschitz, and that case is stage 353. For merely continuous `z`, the stage-353 construction degenerates along any approximation.

## Limits
- This is an obstruction to **one route**. It does not show that continuous Mantel fails, and it does not rule out other constructions (for example, Afriat numbers driven by a modulus of continuity, or a non-Afriat construction).
- `afriat_scale_vanishes` shows that the upper bound on the multipliers vanishes. It does not show that every possible limit utility is degenerate.
