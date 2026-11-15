# Stage 280 — Every interior equilibrium is a division of ownership

Lean 4.35 / Mathlib, 1 audited declaration, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-268, 270 and 275 sources are
inlined.

Setting: stage 275 (common felicity with positive homogeneous marginal utility and the
strict supergradient inequality), with ANY strictly positive prices `p`.

- `equilibrium_is_ownership` — if a strictly positive allocation `x` uses exactly
  output and each `x i` is optimal among strictly positive bundles costing no more than
  itself at `p`, then there are shares `w i > 0` summing to one with
  `x i s = w i * Y s`.

Reading: stage 268 exhibited one equilibrium in which households hold shares. This shows
there is no other kind: with stage 276 the allocation is a division of ownership and the
prices are the ownership prices up to scale.

Limits: common felicity and common beliefs (see stage 282 for what fails otherwise);
interior allocations; one date, finitely many states.
