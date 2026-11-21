# Stage 367: uniqueness of the rest point and convergence to it, when the update is a contraction

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/RestConvergence.lean`](../../formal/RestConvergence.lean).

Stage 365 proved that the ownership dynamics have a rest point for every continuous
wealth-dependent patience or access rule, and gave a continuous rule with two rest points, so
existence alone says nothing about uniqueness or convergence. This file isolates a condition
under which both hold, and checks it in the basic economic case.

* `contraction_rest`: if a self-map `f` of a closed nonempty subset `s` of a complete metric space
  satisfies `dist (f x) (f y) ≤ K · dist x y` on `s` with `0 ≤ K < 1`, then it has exactly one
  rest point `x⋆` in `s`, and from every starting point in `s` the path `f^[n] x` converges to
  `x⋆` with `dist (f^[n] x) x⋆ ≤ K ^ n · dist x x⋆` (Banach fixed point theorem, used through
  Mathlib's `ContractingWith`; the rate is proved directly).
* `affine_rest`: the affine update `x' h = ρ h · x h + a h` with retention `0 ≤ ρ h ≤ K < 1`
  (sup distance on `H → ℝ`) is such a contraction on all of `H → ℝ`; its unique rest point is
  `a h / (1 − ρ h)` and every path converges to it at rate `K ^ n`.
* `step_common`: with common saving rate `s₀ > 0` and full access, the stage 356/365 issuance step
  restricted to the simplex is exactly the affine update with common retention
  `ρ = (1 + g (1 − σ)) / (1 + g)` and intercept `g σ c / (1 + g)`.
* **`common_patience_converges`**: in that case, for `g > 0`, `0 < σ ≤ 1` and `H · c = 1`, the
  equal distribution `x h = c` is the only rest point on the simplex, and from every initial
  distribution the ownership path converges to it, with
  `dist (x_n) c ≤ ((1 + g (1 − σ)) / (1 + g)) ^ n · dist (x_0) c`.

Reading: when everyone saves at the same rate and has the same access, issuance of new claims
pulls every distribution geometrically to equal ownership, at a speed set by the issuance rate
`g` and the issued share `σ`.

Limits: the economic sufficient condition is only the common-saving, full-access case (and the
affine update with fixed household retention rates). For wealth-dependent saving or access the
contraction hypothesis is not verified here, and by stage 365 it can fail (two rest points).
Discontinuous threshold rules are not covered.
