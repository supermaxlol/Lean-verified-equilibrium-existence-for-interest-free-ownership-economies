# Stage 283 — Heterogeneous risk tolerance under exponential (CARA) utility

Lean 4.35 + Mathlib. 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finite states, common beliefs `π`, output `Y s`. Household felicity `-τ * exp (-c / τ)` with its own risk tolerance `τ > 0`; total tolerance `T`. Prices `π s * exp (-(Y s) / T)`.

- `cara_supergradient`: the exponential felicity lies below its tangent lines.
- `cara_optimal`: the bundle `τ / T * Y s + k` (share of output equal to the household's share of total risk tolerance, plus a constant) is optimal at these prices.
- `cara_clears`: with constants summing to zero and tolerance shares summing to one, the bundles use exactly output.

Reading: with different risk tolerances, households still hold a share of output, set by relative risk tolerance, plus a riskless transfer; the transfers net to zero.

Limits: CARA only; constants `k` are taken as given rather than solved from budgets; consumption may be negative under CARA, as usual for this felicity.
