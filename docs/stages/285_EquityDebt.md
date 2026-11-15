# Stage 285 — Incomplete markets with only equity and debt

Lean 4.35 + Mathlib. 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finite states, output `Y s > 0`. Only two assets trade: a share of output and a bond paying one in every state. A household endowed with share `e` chooses share `θ` and bond position `b` and consumes `θ * Y s + b`. Asset prices are those implied by ownership state prices `π s * m (Y s)`. Felicity has supergradient `m` with `m (e * y) = h e * m y` (the homothetic class, including all CRRA).

- `equity_debt_optimal`: keeping the endowed share and holding no bond is optimal among all affordable `(θ, b)` with positive consumption.
- `debt_zero_unique`: under the strict supergradient inequality, and if output differs between two states, this is the only optimum: `θ = e` and `b = 0`.
- `equity_debt_clears`: shares sum to one, consumption equals output, and no bond is outstanding.

Reading: even when a fixed claim is available, no household wants to issue or hold one in equilibrium under a common homothetic felicity and common beliefs. The fixed claim is redundant.

Limits: the prices are taken from the ownership equilibrium and shown consistent with the portfolio optimum; existence and uniqueness of equilibrium in the incomplete-market economy itself are not proved separately. With heterogeneous risk attitudes (stage 282) bond trade can be non-zero.
