# Stage 331: unique demand on a continuum for Debreu's constant-weight consumer

Lean 4.35 + Mathlib. 35 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `debreu_constant_weight_unique`: take Debreu's consumer `x q = c(e_k − q_k q)` with a constant weight `c > 0`, on any non-empty set `P` of unit prices whose coordinates are at least `ε`. There is a continuous, concave, strictly monotone utility `u` such that, for every `p ∈ P`, `x p` is the **unique** maximiser of `u` on `{y | p·y ≤ 0}`.
- The construction is `u = U + δ·W`:
  - `U` is the stage-330 Afriat infimum;
  - `W` is a continuous concave correction built from tangent quadratics. It is maximal exactly at the observed trade, along each budget hyperplane;
  - `δ = ε'²/4`.
- Supporting lemmas:
  - `cont_of_lip`: a Lipschitz function in the ℓ¹ sense is continuous;
  - `U_mono_sum`: the quantitative monotonicity of `U`;
  - `T_eq`, `T_lip`, `W_lip`, `W_continuous`, `W_concave`, `W_mono`, `W_at`, `le_W`.

## Reading
This closes the gap that stage 330 left open for the constant-weight case. There, each `x p` was a maximiser but not shown to be unique. Here demand is single-valued on the whole continuum `P`, not just at finitely many prices.

## Limits
- One consumer, with a fixed weight `c` and a fixed good `k`. Price-dependent weights are treated in stage 334. That stage shows unique demand fails wherever pieces with different weights touch.
- Continuous Mantel/Debreu on `S_ε` (a sum of such consumers whose weights vary continuously with `p`) is not proved here.
