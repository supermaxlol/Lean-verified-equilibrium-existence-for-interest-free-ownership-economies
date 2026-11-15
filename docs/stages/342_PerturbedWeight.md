# Stage 342: perturbing a weight that has Afriat numbers with a margin

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `perturb_afriat`: suppose `V, λ₀` are Afriat numbers for the base weight `w₀` with a margin `m(p,q)`, i.e. `V p − V q + m ≤ λ₀ q · w₀ p · c(p,q)`, where `c(p,q) = q_k − p_k (q·p)`. Suppose also that `|δ p − δ q| · λ₀ q · w₀ p · |c| ≤ m (1 + δ q)`. Then `V, λ₀/(1 + δ)` are Afriat numbers for the perturbed weight `w₀ (1 + δ)`.
- `perturb_afriat_lip`: with a margin `μ · d(p,q) · λ₀ w₀ |c|`, the condition holds whenever `|δ| ≤ δ₀ < 1`, `δ` is `κ`-Lipschitz for `d`, and `κ ≤ μ(1 − δ₀)`.
- `lam_bounds`: the new multipliers stay in `[ℓ/(1 + δ₀), Λ/(1 − δ₀)]`, the uniform bounds that stage 330 needs.
- `debreu_delta`: Debreu's weight is `Z_k + A p_k = A p_k (1 + δ)` with `δ = Z_k/(A p_k)`. On `S_ε`, if `|Z_k| ≤ M` and `Z_k` is `L_Z`-Lipschitz, then `|δ| ≤ M/(Aε)` and `δ` is `(L_Z/(Aε) + M/(Aε²))`-Lipschitz. Both tend to zero as `A → ∞`.

## Meaning
**Conditional on a uniform margin `μ > 0` for the pure weight `p_k`**, Debreu's weights `Z_k + A p_k` with Lipschitz `Z` are rationalised on `S_ε` for all large `A`.

## Limits
- **The margin is not proved.** Stage 339 proves the inequality with margin `≥ 0` only. Numerics at `K = 7/σ` (`n = 3, 4`, `ε = 0.2, 0.3`, 1500 random prices) show margin/(‖p − q‖·|R|) ≥ 0.72 on the samples. That is evidence only: near the diagonal both sides are tiny, and floating-point noise appears at larger `K`.
- It needs `Z` Lipschitz, not merely continuous.
- Rationalisation only, not unique demand.
