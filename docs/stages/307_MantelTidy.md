# Stage 307: Mantel/Debreu with unique demand from compactness and continuity alone

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Statement (`MantelTidy.mantel_compact`)

Let `P` be a compact set of prices on the unit sphere with every coordinate `≥ ε > 0`. Let `Z` be
continuous on `P` and satisfy Walras' law `p·Z(p) = 0`.

Then there is a constant `A` such that, at every `p ∈ P`, `Z(p)` is the sum of `|S|` budget-balanced
trades `x_k(p) = (Z_k(p) + A p_k)(e_k − p_k p)`. Each trade is the **unique** maximizer of a fixed
monotone, quasiconcave utility `u_k` on the budget `{y | p·y ≤ 0}`.

Compared with stage 306, the two extra hypotheses are now derived:

* **Bound** (`bound_of_compact`): a continuous `Z` on a compact `P` is bounded.
* **Trade-map continuity** (`xd_continuousOn`, `sq_dist_sphere`, `coord_close`, `trade_cont`):
  - on the unit sphere, `|q − p|² = 2 − 2 p·q`, so `p·q > 1 − δ²/4` forces every coordinate within `δ`;
  - continuity of `Z` then gives the `ℓ¹` closeness of `x_k(q)` to `x_k(p)` that stage 306 assumed.

## Limits

* Continuity of the utility `u_k` itself is **not** proved. The `u_k` are monotone and quasiconcave and
  have unique maximizers, but they are built from an infimum over convex hulls and may jump. Debreu's
  theorem asks for continuous preferences, so that part of the classical statement stays open.
* `P` is any compact subset of `S_ε` (the full `S_ε` is compact, but that fact is not formalised here).
* The economy is stated in excess-demand (trade) form, without explicit endowments.

## Debreu's exact domain
- `Seps_compact`: `S_ε = {p | Σp² = 1, p ≥ ε}` is compact (closed and bounded).
- `mantel_debreu`: every continuous Z with Walras' law on S_ε itself is the aggregate of |S| trades, each the unique maximizer of a monotone quasiconcave utility on its budget, at every price in S_ε.
