# Stage 255 — Stability of price adjustment under the weak axiom

Lean 4.35 / Mathlib, 6 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: excess demand `z` with Walras' law and the weak axiom (the form used by
`equilibrium_unique_of_warp`), an equilibrium `pstar`, and any price path with `dp/dt = z p`.

- `warp_value_pos`, `warp_value_nonneg` — the equilibrium price values excess demand
  positively away from equilibrium.
- `lyapunov_deriv`, `lyapunov_value` — the squared distance to `pstar` has derivative
  `-2 * pstar · z (p t)`.
- `distance_deriv_neg` — that derivative is strictly negative off equilibrium.
- `tatonnement_distance_antitone` — the distance to equilibrium never increases.

Limits: monotone (Lyapunov) stability only; convergence is stage 259. Conditional on the
weak axiom: stability without such a condition is false.
