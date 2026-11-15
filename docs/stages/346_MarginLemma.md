# Stage 346: a quantitative margin for the weight p_k, and Debreu's weight A p_k + Z_k

Lean 4.35 + Mathlib. 29 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file repeats stage 339 (the explicit `L`, `F`) and stage 342 (perturbation with a margin) in full, and adds the results below.

## Results
- `scalar_margin` / `margin_ab`: the one-variable inequality of stage 336 holds with a **quadratic margin** `μ σ L(a) b (1 − C)`, where `C = ab + √((1−a²)(1−b²))`. The hypotheses are `K σ ≥ 14` and `μ ≤ 1/40`, where `σ` is a lower bound for `sin 2α` on `[ε, β]`.
- `cs_bound`, `dist2_sq`, `coord_le_dist2`: Cauchy–Schwarz off coordinate `k`, `‖p − q‖² = 2 − 2 q·p`, and `|p_k − q_k| ≤ ‖p − q‖`.
- `margin_nd`: in `n` goods, the stage-336 Afriat inequality for the weight `p_k` holds with the margin `ν ‖p − q‖ · L(q_k) p_k |q_k − p_k (q·p)|`, when `ν ≤ μσ/2` and `3ν ≤ ε`.
- `pk_perturbed_afriat`: every perturbation `p_k (1 + δ p)` with `|δ| ≤ δ0 < 1` and Lipschitz constant `κ ≤ ν (1 − δ0)` (in the Euclidean distance) is still rationalised by Afriat numbers with `λ q = L(q_k)/(1 + δ q)`.
- `debreu_weight_afriat`: **Debreu's weight `A p_k + Z_k`** satisfies the Afriat inequalities on the continuum, with `V q = F(q_k)` and `λ q = L(q_k) / (A (1 + Z_k q/(A q_k)))`, provided `|Z_k| ≤ M`, `Z_k` is `Lz`-Lipschitz, `M/(A ε) ≤ δ0 < 1` and `Lz/(A ε) + M/(A ε²) ≤ ν (1 − δ0)`. All of these hold for `A` large enough.

## Limits
- This gives the Afriat **inequalities**, with Afriat numbers that are bounded on `P` (since `L` and `F` are continuous on `[ε, β]`). The step from these to a continuous, concave, strictly monotone utility (the stage-330 infimum construction) is **not** re-assembled here for this weight.
- Uniqueness of demand for this weight is **not** proved here.
- `K` must satisfy `K σ ≥ 14`, so `ℓ ≈ e^{−Kπ/2}` is very small for small `ε`. The constants are explicit but not sharp.
- The hypothesis `hσa` (`σ² ≤ 4a²(1−a²)` on `[ε, β]`) is assumed, not derived from `ε, β`.
