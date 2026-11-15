# Stage 317: Exponential tail bounds for the intermediation buffer

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/TailBound.lean`. Sharpens stage 311 (Chebyshev).

## Results
* `chernoff`: P(X ≥ t) ≤ e^{−λt} E[e^{λX}] for all λ ≥ 0 (finite probability space).
* `exp_le_chord`, `mgf_le`: a loss in [0,1] with mean m has E[e^{λX}] ≤ exp(m(e^λ − 1)), from convexity of exp. No variance is needed.
* `mgf_indep`: under independence (product weights) the moment generating function of the pool total factorizes.
* `pool_tail`: N independent losses in [0,1] with means ≤ m: P(total ≥ t) ≤ exp(−λt + N m (e^λ − 1)).
* `buffer_size`: a buffer B ≥ (N m (e^λ − 1) + log(1/ε))/λ fails with probability ≤ ε.

## What this changes
Stage 311's Chebyshev buffer grows like 1/√ε in the target failure probability. This one grows like log(1/ε).
For ε = 10⁻⁶ that is the difference between a factor of 1000 and a factor of about 14.

## Honest limits
Losses are normalized to [0,1] and independent. The common-factor (correlated) case of stage 310 is not covered: a common shock puts a floor under pooled risk that no exponential bound removes. λ is free and not optimized (the Bennett-optimal λ is not derived).
