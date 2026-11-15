# Stage 353: Debreu's decomposition and the weight A p_k + Z_k, assembled

Lean 4.35 + Mathlib. 15 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file repeats stage 346 in full and the stage-330/336 infimum construction (`continuum_afriat`) and Debreu's direction `e_k − p_k p` (`dirk`), and adds the results below.

## Results
- `debreu_decomp`: for unit `p` with `p · z = 0` and any `A`, `z = Σ_k (A p_k + z_k)(e_k − p_k p)`. This is Debreu's decomposition of a Walras excess demand into `n` one-direction trades.
- `trade_budget`, `trade_value`: each trade `x_k(p) = (A p_k + Z_k(p))(e_k − p_k p)` costs nothing at `p`, and its value at `q` is `(A p_k + Z_k(p))(q_k − p_k (q·p))`.
- `debreu_consumer`: on the cap `P` (unit prices with every coordinate in `[ε, β]`), if `|Z_k| ≤ M`, `Z_k` is `Lz`-Lipschitz in the Euclidean distance, `M/(Aε) ≤ δ0 < 1` and `Lz/(Aε) + M/(Aε²) ≤ ν(1 − δ0)`, then `x_k(p)` maximises a **continuous, concave, strictly monotone** utility on every budget `p · y ≤ 0`, `p ∈ P`. The Afriat numbers come from stage 346; their bounds `ℓ/(A(1+δ0)) ≤ λ ≤ 1/(A(1−δ0))` come from `L_bounds` and `lam_bounds`; the utility is the stage-330 infimum.
- `debreu_assembly`: hence **a Walras excess demand `z` that is bounded and Lipschitz on the cap is, at every price of the cap, the sum of `n` rational consumers' optimal trades.**
- `debreu_assembly_cap`: the same on the symmetric range `β² ≤ 1 − ε²`, with `σ = 2ε√(1 − ε²)` (the hypothesis `hσa` is then derived, not assumed).
- `large_A_exists`: for any `M ≥ 0`, `Lz ≥ 0`, `0 < δ0 < 1`, `ν > 0`, a suitable `A > 0` exists.

## Limits
- `z` must be **Lipschitz** and bounded on the cap. Debreu's theorem needs only continuity. Closing that gap is the uniform-Lipschitz / grid route (stages 349 and on), which is not done here.
- Each consumer's trade is **a** maximiser, not the unique one. Uniqueness for this weight is not proved here.
- Utilities are defined on all of `ℝⁿ` (trades), are concave and strictly monotone; endowments are implicit (the trade is the excess demand). No boundary behaviour is claimed.
- Constants (`K σ ≥ 14`, `μ ≤ 1/40`, `ν ≤ μσ/2`, `3ν ≤ ε`) are explicit but not sharp; `ℓ ≈ e^{−Kπ/2}` is very small for small `ε`.
- The result is on the cap `S_ε`, not the whole simplex.
