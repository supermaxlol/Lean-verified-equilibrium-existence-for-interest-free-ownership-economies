# Stage 322: Pooling a finite number of correlated risks

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/CorrelatedPooling.lean`. The finite-N companion to stage 310.

## Results
* `var_tot`: the variance of the pool total is the sum of all pairwise covariances.
* `var_equi`, `avg_formula`: with variance v and pairwise covariance c, Var(total) = Nv + N(N − 1)c. Per member that is c + (v − c)/N.
* `corr_lower`: c ≥ −v/(N − 1).
* `chebyshev`, `pool_tail_avg`: P(pool loss deviates by ≥ b per member) ≤ (c + (v − c)/N)/b².
* `floor_le`, `avg_antitone`, `n_needed`: the bound falls with N but never below c/b². N ≥ (v − c)/δ members bring it within δ/b² of that floor.

## Honest limits
Equicorrelation is assumed. The bounds are Chebyshev bounds; the independent case has exponential bounds (stage 317). The floor here is on variance and on this bound. The common-factor tail floor itself is stage 310's.
