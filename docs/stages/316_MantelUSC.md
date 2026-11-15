# Stage 316: The Mantel utility is upper semicontinuous

Lean 4.35 + Mathlib. 20 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/MantelUSC.lean`. It contains all of stage 307 plus the new results.

## New results
* `wsimp_compact`: the weight simplex on `Fin n` is compact.
* `hull_compact`: **the convex hull of a compact set in a finite-dimensional real normed space is compact.**
  Proof by Carathéodory (`eq_pos_convex_span_of_mem_convexHull`, `card_le_finrank_succ`): pad to
  `finrank + 1` points by `Function.extend`, then the hull is the continuous image of
  simplex × sⁿ. Mathlib only had this for finite sets.
* `Aset_compact`, `K_closed`: the upper-contour sets `K σ` (hull plus free disposal) are closed when `P`
  is compact and the coefficient `a` is continuous on `P`.
* `lev_iff`: `sInf lev ≤ τ  ⟺  ∀ δ > 0, τ + δ ∈ lev`.
* `lev_closed`, then **`uu_usc`**: the constructed utility `uu` is upper semicontinuous.
* **`mantel_usc`**: the utilities in the Mantel construction of stages 306/307 are upper semicontinuous.

## Honest limits
This proves **upper** semicontinuity only, not full continuity. Lower semicontinuity needs `K σ` to vary
continuously (lower hemicontinuously) in the level `σ`. That can fail at the levels where the
`q k ≤ σ` cut jumps, and it is **not** proved. So item 8 is partly closed: the utilities are monotone,
quasiconcave and USC, which is enough for maxima to exist on compact budget sets, but this is not
the full continuous-preferences Debreu–Mantel statement.
