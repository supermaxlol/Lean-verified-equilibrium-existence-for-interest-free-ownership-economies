# Stage 356: the issuance equilibrium with different patience and unequal access

Lean 4.35 + Mathlib. 25 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Stage 263 assumed that every household has the same patience, the same saving rate and the same
access to new units. This stage drops all three inside the same equilibrium. Household `h` saves
the fraction `s t h` of its wealth in period `t`; only households in an access set `A` take part in
the pro rata part of issuance; a fraction `σ` of new units is issued equally (`c = 1/N` each) to every
household.

## Results
- **Equilibrium** (`aggregate_demand`, `clearing_unique`, `clearing_exists`, `equilibrium_return`):
  the units market clears exactly at `Q = B D / (1 − B)`, where `B = ∑ s h x h` is the wealth-weighted
  saving rate, and the gross return on ownership is `1 / B`. `B` lies between the lowest and highest
  saving rates (`B_ge`, `B_le`).
- **Shares come from clearing** (`units_share`): household `h` ends the period with unit share
  `s h x h / B`. Its consumption share equals its wealth share exactly when its saving rate equals
  the aggregate one (`consumption_share_iff`).
- **Consistency** (`reduces_to_common`): with a common saving rate and full access, the step is
  exactly stage 263's issuance rule.
- **Well defined** (`step_sum`, `path_pos_sum`): shares stay positive and sum to one.
- **Floor** (`floor_every_step`): every household, with or without access, holds at least
  `g σ c / (1 + g)` after every period.
- **Patience concentrates** (`pro_rata_closed`, `ratio_bound`, `ratio_vanishes`,
  `most_patient_takes_all`): under pro rata issuance with full access, shares are
  `P_n(h) x0 h / ∑ P_n(k) x0 k` with `P_n(h) = ∏ s t h`. If every other household's saving rate stays
  below a fixed fraction `ρ k < 1` of household `h`'s, then `h`'s share tends to one.
- **For log utility** (`log_takes_all`, saving rate `β h`) and **CRRA with a common `γ`**
  (`crra_ratio`, `crra_takes_all`, saving-rate ratio `(β k / β h)^(1/γ)` at every return), the most
  patient household takes everything along any positive return path.
- **Exclusion dilutes** (`excluded_step`, `excluded_dilution`): a household outside `A` receives only
  the equal part. With `σ = 0` its share is at most `(κ / (1 + g))^n` of its start, where its saving rate
  is at most `κ` times the lowest rate.
- **Equal issuance protects the excluded** (`excluded_floor`, `excluded_floor_eventually`,
  `common_rate_level`): with `σ > 0`, an excluded household's share eventually exceeds any level below
  `g σ c / (1 + g − lo/hi)`; with a common saving rate that level is `σ c = σ / N`.

## Reading
Concentration in this model comes from exactly the differences that stage 263 assumed away.
Different patience under pro rata issuance concentrates ownership on the most patient household,
and exclusion from new units dilutes a household towards zero. A universal equal part of issuance
gives every household a floor in every period.

## Limits
- Saving rates are taken as given paths. For log utility `s = β` is the optimal rule (stages 258, 264);
  for CRRA the stationary rate is used, not the full transition-path optimum.
- Access is a fixed set `A`; why some households lack access is not modelled.
- Patience and access are exogenous. Welfare, control and growth effects of the issuance rule are not
  part of this release.
