# Stage 350: the shape of debt and the interest on it are separable

Lean 4.35 + Mathlib. 13 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Mathlib-only.

Setting: finite states, probabilities `π`, output `y`. Debt with face `D` repays `min (y s) D`; the state is verified at cost `c ≥ 0` exactly in default (`y s < D`). The lender's outside option is cash at zero return. `D0` is a face that returns the principal `I` (`I ≤ lender D0`), and `D ≥ D0` is any face that carries a premium.

## Results
- `surplus_split`: the lender's net receipts plus the borrower's residual equal total surplus (expected output less expected verification cost). A contract only divides surplus.
- `vprob_mono`, `vprob_strict`: a larger face never lowers the default probability, and it strictly raises it when it adds a default state of positive probability.
- `surplus_anti`, `surplus_strict`: a premium never raises total surplus. It strictly lowers it when `c > 0` and it adds such a default state.
- `resid_anti`: a premium never raises the borrower's residual.
- `step_mono`, `resid_diff`, `gain_anti`: under first-order stochastic dominance of high effort over low effort, a premium never raises the borrower's gain from effort.
- `premium_transfer`, `lender_gain_le_loss`: the lender's gain from a premium equals the borrower's loss less the extra verification cost, so it is at most that loss.
- `zero_premium_dominates` (capstone): the zero-premium face weakly dominates every larger face on surplus, residual and effort incentive, and the premium is a transfer less deadweight cost.

Reading: the information results (stages 303, 309, 321, 327) justify the debt *shape*. This stage shows that, holding the shape fixed, a premium above the break-even face buys no surplus and no incentive. Shape and interest are separable.

## Limits
- When the project can default, `D0` exceeds `I`: the excess is compensation for default losses and verification at zero time value, not a time premium. The stage does not call that excess interest, and it does not compute `D0`.
- The existence of a break-even face `D0` is a hypothesis, not proved here.
- First-order stochastic dominance is assumed (as an inequality on monotone payoffs), not derived from MLRP.
- The optimality of the debt shape itself is stage 327 (Innes) and is not re-proved here.
- The lender's outside option is fixed at zero return. If the lender has a positive-return alternative, that return is a real opportunity cost and is outside this model.
