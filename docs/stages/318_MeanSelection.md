# Stage 318: Selection on the mean under profit sharing

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/MeanSelection.lean`. Completes stage 314 (risk selection removed, mean selection remains).

## Setting
Project size I, borrower contribution k ≤ I, lender share θ = (I − k)/μ̄ priced at the pool mean μ̄. A type with mean μ.

## Results
* `subsidy_eq`: the type overpays θμ − (I − k) = (I − k)(μ − μ̄)/μ̄.
* `subsidy_pos_iff`: above-average types overpay and below-average types are subsidized. This is adverse selection on the mean (Myers–Majluf style).
* `subsidy_abs`, `subsidy_anti`, `full_contribution`: the mispricing is (I − k)|μ − μ̄|/μ̄. It falls with the borrower's contribution and is zero at k = I.
* `stays_iff`: with an outside source costing (1 + φ)(I − k), a type stays iff μ ≤ (1 + φ)μ̄.
* `lender_return`: if applicants' true mean μa differs from the priced μ̄, the lender's loss is at most (I − k)|μa − μ̄|/μ̄.
* `gain`, `gain_diff`, `contribution_screens`: raising the required contribution lowers below-average types' net gain and raises above-average types'. Contribution screens on the mean.

## Honest limits
The lender knows only the pool mean. The re-pricing fixed point (unravelling) is not solved. The borrower's capacity to contribute is assumed. Debt avoids mean selection only among borrowers who never default.
