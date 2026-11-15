# Stage 274 — Power utility with relative risk aversion 2 and 1/2

Lean 4.35 / Mathlib, 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-268 source is inlined.

Setting: stage 268 (homothetic ownership equilibrium), which asks for a felicity `u`, a
positive marginal utility `m` with the supergradient inequality, and a homogeneity
function `h`.

- `inv_supergradient`, `inv_strict_supergradient`, `inv_homogeneous` — `u c = -(1 / c)`,
  `m y = 1 / y ^ 2`, `h w = 1 / w ^ 2` (relative risk aversion 2).
- `sqrt_supergradient`, `sqrt_homogeneous` — the square-root felicity (relative risk
  aversion 1/2).
- `crra2_ownership_equilibrium` — the stage-268 ownership equilibrium with
  `u c = -(1 / c)`: state prices `π s / Y s ^ 2`, every household holds a share of output.

Limits: two exponents only; the general case is stage 279. One date, finitely many states.
