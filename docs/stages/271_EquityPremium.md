# Stage 271 — The shadow riskless return is below the expected return on ownership

Lean 4.35 / Mathlib, 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: stage 266 — probabilities `π s > 0` summing to one, output `Y s > 0`, state
prices `π s / Y s`. The claim to all output costs one, so its expected gross return is
`∑ s, π s * Y s`. A claim paying one unit in every state costs `∑ s, π s / Y s`.

- `inv_tangent`, `inv_tangent_strict` — tangent-line bound for `1 / y`.
- `riskless_price_ge` — the sure claim costs at least `1 / ∑ s, π s * Y s`.
- `premium_nonneg` — `1 / ∑ s, π s / Y s ≤ ∑ s, π s * Y s`.
- `premium_pos` — the inequality is strict when output differs across two states.

Limits: log utility, one date. The riskless return is a shadow price; no sure claim is
traded in the stage-266 equilibrium. No magnitude is derived.
