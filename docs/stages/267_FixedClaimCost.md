# Stage 267 — A fixed claim layered on ownership is strictly costly (log utility)

Lean 4.35 / Mathlib, 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: as in stage 266 — probabilities `π s > 0`, output `Y s > 0`, state prices
`π s / Y s`, a household of wealth `w` with expected log utility.

- `equity_strictly_optimal` — any affordable bundle that differs from `w * Y s` in some
  state gives strictly lower expected utility.
- `fixed_claim_differs` — if output differs across two states, a bundle `a * Y s - b`
  with `b ≠ 0` is not the ownership bundle.
- `fixed_claim_strictly_worse` — such a bundle, if affordable, is strictly worse than the
  ownership bundle, for the payer (`b > 0`) and the receiver (`b < 0`) alike.

Limits: log utility and common probabilities. The comparison is at the ownership state
prices; it does not say a fixed claim is harmful when beliefs or preferences differ.
