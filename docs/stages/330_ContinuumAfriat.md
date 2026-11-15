# Stage 330: Afriat's construction on a continuum of prices

Lean 4.35 + Mathlib. 16 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `continuum_afriat`: let `P` be any non-empty set of prices, possibly infinite, with coordinates in `[ε, 1]`, and let `x q` be the trade chosen at `q`. Suppose there are levels `V q` and weights `λ q ∈ [ε, Λ]` satisfying the continuum Afriat inequalities `V p ≤ V q + λ q (q·x p − q·x q)` for all `p, q ∈ P`. Then `U y = inf_{q∈P} (V q + λ q (q·y − q·x q))` has these properties:
  - it is finite and Lipschitz (`U_lip`), hence continuous;
  - it is concave and strictly monotone on all of `ℝ^S`;
  - `U(x p) = V p`;
  - `x p` maximizes `U` on `{y | p·y ≤ p·x p}`.
- `debreu_constant_weight`: Debreu's consumer `x q = c(e_k − q_k q)` with a constant weight `c > 0` satisfies these inequalities with `V q = −q_k` and `λ q = 1/c`, on any set of unit prices bounded away from zero. So that consumer is rationalised by a continuous, concave, strictly monotone utility on a whole continuum of prices.

## Reading
This is the first step on the remaining open problem in the Mantel arc: continuous preferences for a whole continuous excess-demand function on `S_ε`. It reduces the problem to finding functions `V` and `λ` that satisfy the continuum Afriat inequalities for Debreu's consumers. The constant-weight case shows the construction works on a continuum. Stage 328 shows the earlier convex-hull construction cannot be repaired.

## Limits
- The general case is NOT proved. In Debreu's decomposition the weight `α_k(p) = Z_k(p) + A p_k` varies with `p`. Then `V q = −q_k` does not satisfy the inequalities, and suitable `V` and `λ` have not been found here. Continuous Mantel/Debreu on a continuum remains open in this programme.
- The utility is concave but not strictly concave, so demand is optimal but not shown to be unique.
