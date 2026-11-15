# Stage 275 — Every efficient interior allocation is a division of ownership

Lean 4.35 / Mathlib, 1 audited declaration, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-268 and stage-270 sources are
inlined.

Setting: states `S`, probabilities `π s > 0`, output `Y s > 0`, a common felicity `u` with
positive marginal utility `m`, the strict supergradient inequality
`u a < u b + m b * (a - b)` for `a ≠ b`, and homogeneity `m (w * y) = h w * m y`.

- `efficient_is_ownership` — if a strictly positive allocation `x` uses exactly output
  and no strictly positive feasible allocation makes everyone at least as well off and
  someone strictly better off, then there are shares `w i > 0` summing to one with
  `x i s = w i * Y s` in every state.

Reading: converse of stage 269. With stage 269, the efficient interior allocations are
exactly the divisions of ownership. No efficient arrangement has a household holding a
fixed claim.

Limits: common homothetic felicity and common beliefs; interior allocations; one date,
finitely many states. With different beliefs or different risk attitudes efficient
allocations are not proportional to output.
