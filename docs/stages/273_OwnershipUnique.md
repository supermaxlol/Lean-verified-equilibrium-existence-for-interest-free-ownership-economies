# Stage 273 — At the ownership prices every optimal bundle is a share of output

Lean 4.35 / Mathlib, 1 audited declaration, `[propext, Classical.choice, Quot.sound]`, no
errors, no warnings. The stage-270 source is inlined.

- `optimal_is_share` — under the strict hypotheses of stage 270, if a strictly positive
  bundle is optimal in the budget set of an endowment `ω` at prices `π s * m (Y s)`, it
  equals `w * Y s` in every state, `w` being the value of `ω` relative to the value of
  output.

Reading: at these prices the equilibrium allocation is unique and is a division of
ownership.

Limits: uniqueness of the allocation at the given prices only. Uniqueness of the
equilibrium prices is not proved here.
