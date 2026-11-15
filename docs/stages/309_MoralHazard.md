# Stage 309: Moral hazard, profit sharing and interest-free debt

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Effort (high/low) shifts the output distribution (`πH`, `πL`); high effort costs `κ`. Under repayment `R` the entrepreneur keeps `y − R`; effort is chosen iff `κ ≤ E_H[y−R] − E_L[y−R]`.

## Results
- `ps_gain`: under profit sharing `R = θy` the effort gain is `(1−θ)·ΔY`.
- `ps_ic_iff`: effort holds iff `θ ≤ 1 − κ/ΔY`.
- `ps_financeable_iff`: an incentive-compatible profit-sharing contract that returns `I` exists iff `I ≤ E_H y·(1 − κ/ΔY)`.
- `ps_gap`, `ps_gap_strict`: that bound is below the first-best `E_H y − κ`, strictly when low-effort output and κ are positive. This is the moral-hazard cost of profit sharing (Innes 1990 direction).
- `qard_gain`, `qard_gain_default`, `qard_ic_iff`: an interest-free loan of face `I` keeps the full gain `ΔY` if it never defaults, or if default occurs only in states whose probability effort does not change.

## Reading
The dilution objection applies to profit sharing, not to interest-free finance as such. A zero-markup loan has debt's incentive properties. Together with 301/308, the trade-off is: debt has strong incentives but needs costly verification or collateral; profit sharing has cheaper risk sharing but weaker effort incentives.

## Honest limits
Two effort levels only. The default-state condition in `qard_gain_default` is an assumption, not derived. This is not Innes's general optimal-contract theorem (monotone contracts, limited liability on both sides).
