# Stage 334: Debreu's consumer with price-dependent weights (exploratory)

Lean 4.35 + Mathlib. 24 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `debreu_variable_weight`: Debreu's consumer `x q = w q·(e_k − q_k q)` is rationalised on the whole continuum `P` by a continuous, concave, strictly monotone utility under these conditions:
  - prices are unit vectors whose coordinates are at least `ε`;
  - the weight satisfies `w ∈ [cmin, cmax]`;
  - the weight is relatively Lipschitz with a small constant: `|w p − w q| ≤ κ·w q·‖p − q‖` with `4κ ≤ ε`.

  Each `x p` is a maximiser. Uniqueness is not shown.
- `debreu_piecewise`: the special case of weights that are constant on pieces with these properties:
  - the pieces are separated by `η` in Euclidean distance;
  - the piece values differ by at most `κ·c_j·η`.
- `revealed_sign_invariant` and `debreu_warp`: revealed preference between Debreu trades does not depend on the weights. The sign of `q·x p` is the sign of `q_k − p_k(q·p)`. WARP holds for every positive weight function: if each trade is affordable at the other's price, the prices are equal.
- `limit_optimal`: under a continuous utility, a limit of optimal trades is optimal at the limit price.
- `no_unique_of_jump` and `debreu_jump` (the obstruction): suppose prices `q_n ∈ P` with weight `c'` converge to `p ∈ P`, with `w p ≠ c'` and `e_k − p_k p ≠ 0`. Then no continuous utility rationalises the consumer on `P` with a unique maximiser at `p`.

## Reading
The weights never affect revealed preference. So any obstruction to a continuous rationalisation is quantitative (uniform bounds on Afriat numbers), not a revealed-preference failure.
Weights can depend on price if they change slowly enough relative to how far apart prices are. When the weight jumps between pieces that touch, unique demand is impossible for any continuous utility. So the separation hypothesis in `debreu_piecewise` cannot be dropped if demand is to be unique.

## Limits
- The relative Lipschitz constant must be small (`κ ≤ ε/4`). Debreu's weights `α_k(p) = Z_k(p) + A·p_k` have a relative Lipschitz constant of order at least `1` (the `A·p_k` part alone gives about `1/p_k`). So this theorem, with `V q = −q_k` and `λ = 1/w`, does not cover them.
- Continuous Mantel/Debreu on `S_ε` is not proved. See `essays/CONTINUOUS_MANTEL_OBSTRUCTION.md` for an honest account of where the construction stops.
