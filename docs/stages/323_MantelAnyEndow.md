# Stage 323: Mantel for any endowments bounded away from zero

Lean 4.35 + Mathlib. 16 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/MantelAnyEndow.lean`. Stage 312's development plus a new section.

## Result
`mantel_any_endow`: fix any floor η > 0, however small. Then for every continuous Z satisfying Walras's law on a compact price set bounded away from the boundary, there is λ > 0 with the following property. For every endowment profile with all entries ≥ η, λZ is the aggregate excess demand of an economy in which:
* consumption is nonnegative;
* every consumer exhausts the budget p·c = p·e_k;
* every consumer's demand is the unique maximizer of a utility on the budget set.

## What changed from stage 312
Stage 312 needed endowments above a bound M that depended on Z. This stage takes the endowments as given and rescales Z instead. Rescaling by λ > 0 keeps the zeros of Z, so the equilibrium prices are exactly the same. The result is: any equilibrium set, with any strictly positive endowments.

## Honest limits
The realized excess demand is λZ, not Z itself. For a fixed small η, λ = η/(M + 1) can be small. Endowments must be bounded away from zero. Utilities are upper semicontinuous (stage 316); they are not shown to be continuous.
