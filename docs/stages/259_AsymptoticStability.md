# Stage 259 — Convergence of price adjustment under the weak axiom

Lean 4.35 / Mathlib, 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`.
Mathlib-only. The stage-255 source is inlined.

Setting: continuous excess demand `z` with Walras' law, an equilibrium `pstar`, and a price
path with `dp/dt = z p`.

- `norm_conserved` — Walras' law keeps `∑ s, p s ^ 2` constant along the path.
- `shell_compact` — closed shells around `pstar` inside a closed set are compact.
- `tatonnement_converges` — if the path stays in a closed set on which `pstar` values
  excess demand strictly positively away from `pstar`, then `p t → pstar`.
- `tatonnement_converges_warp` — under the weak axiom, if `pstar` is the only equilibrium
  on its sphere and the path starts on that sphere, then `p t → pstar`.
- `tatonnement_distance_antitone` — re-audited from stage 255.

Limits: continuity of `z` and uniqueness of the equilibrium on the sphere are hypotheses.
The path is assumed to exist for all time; existence of solutions is not proved.
Conditional on the weak axiom: convergence without such a condition is false.
