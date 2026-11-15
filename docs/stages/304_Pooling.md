# Stage 304: Pooling (takaful) for interest-free lending

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
There are `N` borrowers on a finite probability space. `L i ω` is borrower `i`'s shortfall, the amount an interest-free lender loses on it. A mutual fund collects a per-member contribution and pays the average shortfall.

## Results
- `E_avg`, `mean_floor`: a fund that covers losses in every positive-probability state must collect at least the expected average loss. Pooling never removes the mean.
- `var_sum`, `var_avg`: the variance of the average is `(1/N²) ∑ᵢ ∑ⱼ Cov(i, j)`.
- `cov_sum_equi`, `var_avg_equi`: with equal variance `v` and common correlation `ρ`, the variance of the average is exactly `ρ v + (1 − ρ) v / N`.
- `var_floor`: for `0 ≤ ρ ≤ 1`, no pool size brings the variance below `ρ v`.
- `chebyshev`, `reserve`: collecting `mean + k` per member, the fund falls short with probability at most `(ρ v + (1 − ρ) v / N) / k²`.

## Reading
This answers "who pays for default risk if not interest?"
- The **expected** loss has to be paid by someone: members' contributions (takaful), a guarantor, or charity. Pooling cannot make it disappear.
- What pooling removes is the **reserve** above the mean. Under independence (`ρ = 0`) the reserve needed for a given safety level shrinks like `1/√N`. With correlated defaults (recessions, harvest failure) a floor `ρ v` remains however large the pool. That residual is the systemic part, and it needs an outside backstop (stage 305) or capital.

So an interest-free lending system needs two layers:
1. member contributions priced at the expected loss;
2. a backstop for the correlated part.

## Limits
- Chebyshev is a crude bound. Sharper tail bounds (Hoeffding, CLT) would give smaller reserves but are not formalised.
- Equicorrelation (one common `ρ`) is a modelling choice. The general covariance formula `var_avg` holds without it.
- Contributions are flat per member. No risk-based pricing and no adverse selection into the pool.
