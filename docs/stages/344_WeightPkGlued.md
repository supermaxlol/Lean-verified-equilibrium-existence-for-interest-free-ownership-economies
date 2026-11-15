# Stage 344: Debreu's consumer with weight `p_k`, rationalised with explicit Afriat numbers

Lean 4.35 + Mathlib. 31 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file contains stages 336 and 339 verbatim, plus the combination below.

## Result
- `weight_pk_explicit`: let `P` be a nonempty set of unit prices with coordinates in `[ε, β]` and `β² ≤ 1 − ε²`. Then the trade `p_k (e_k − p_k p)` is a maximiser on every budget `{y | p·y ≤ 0}`, `p ∈ P`, of one continuous, concave, strictly monotone utility. The Afriat numbers are explicit:
  - `V q = F(q_k)` and `λ q = L(q_k)`, with `L a = a√(1 − a²) e^{−K arccos a}` and `F a = ∫₀^{arccos a} (sin t cos t)² e^{−Kt} dt`;
  - `K = 7/σ` with `σ = 2ε√(1 − ε²)`;
  - `σ/2 · e^{−Kπ/2} ≤ λ ≤ 1`.

## Meaning
This settles the pure weight `A p_k` on `S_ε`, the case that the stage-334 Lipschitz route cannot reach (its relative Lipschitz constant is `≈ 1/p_k`).

## Limits
- Maximiser, not shown unique.
- Only the pure weight; Debreu's `Z_k + A p_k` needs the margin of stage 342, which is not proved.
- The constants are far from sharp.
