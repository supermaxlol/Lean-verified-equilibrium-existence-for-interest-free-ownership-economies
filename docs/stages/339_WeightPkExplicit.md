# Stage 339: the one-variable inequality for the weight `p_k`, with explicit `K`

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Definitions
- `g K t = (sin t cos t)² e^{−K t}`, `G K α = ∫₀^α g K`, `ℓ K α = sin α cos α e^{−K α}`.
- `F K a = G K (arccos a)` and `L K a = ℓ K (arccos a) = a √(1 − a²) e^{−K arccos a}`.

## Results
- `G_hasDerivAt`: `G' = g` (fundamental theorem of calculus).
- `phi_deriv`, `phi_self`: for fixed `θ`, the gap `φ(α) = ℓ(α) sin θ cos θ sin(θ − α) − G θ + G α` vanishes at `α = θ`. Its derivative is `e^{−Kα}/4 · (s_α² − s_θ (s_α cos d + (K s_α − 2 c_α) sin d))`, with `s = sin 2·`, `c = cos 2·` and `d = θ − α`.
- `core_pos`, `core_neg`: if `σ ≤ sin 2α`, `σ ≤ sin 2θ` and `K σ ≥ 7`, this derivative has the sign that makes `φ ≥ 0` on both sides of `θ`.
- `scalar_angle`, `scalar_ab`: the stage-336 hypothesis
  `F b − F a ≤ L a · b · (a − b (a b + √((1 − a²)(1 − b²))))`
  holds for all `a, b ∈ [ε, β]`, provided `σ² ≤ 4a²(1 − a²)` on `[ε, β]` and `K σ ≥ 7`.
- `sigma_symmetric`: for `β = √(1 − ε²)` one may take `σ = 2ε√(1 − ε²)`, so `K = 7/(2ε√(1 − ε²))` (about 70 at `ε = 0.05`).
- `L_bounds`: `σ/2 · e^{−Kπ/2} ≤ L ≤ 1`, the uniform Afriat bounds that stage 330 needs.

## Meaning
Combined with stage 336 (`weight_pk_rationalised`), this gives explicit Afriat numbers for Debreu's consumer with weight `p_k` on any `P ⊆ S_ε`.

## Limits
- `K = 7/σ` is not sharp: numerics suggest about 20 suffices at `ε = 0.05`, against 70 here.
- The lower bound `ℓ` decays like `e^{−Kπ/2}`. That is uniform for fixed `ε`, but very small.
- Only the pure weight `p_k`. Debreu's `Z_k + A p_k` is not covered.
