# Stage 258 — Blackwell contraction and the Bellman equation

Lean 4.35 / Mathlib, 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`.
Mathlib-only.

Setting: operators on value functions `X → ℝ` over a finite state space `X`.

- `blackwell` — monotonicity plus discounting with factor `β` gives a `β`-contraction in
  the sup metric.
- `blackwell_fixed_point` — for `0 ≤ β < 1` such an operator has a unique fixed point, and
  iteration from any starting function converges to it.
- `bellmanOp_mono`, `bellmanOp_disc` — the Bellman operator of a finite Markov decision
  problem satisfies both conditions.
- `mdp_bellman` — unique value function, convergence of value iteration, dominance over
  every action, and existence of a greedy policy attaining it.
- `log_split`, `saver_gap`, `saver_bellman_le`, `saver_bellman_eq` — for the
  infinite-horizon log saver with gross return `R`, the function
  `valueConst β R + log W / (1 - β)` satisfies the Bellman equation, and consuming the
  fraction `1 - β` of wealth attains the maximum.

Limits: uniqueness and convergence are proved for finite state spaces only. The log-saver
value function is verified to solve its Bellman equation on continuous wealth; it is not
shown to be the unique solution or the supremum over all consumption plans.
