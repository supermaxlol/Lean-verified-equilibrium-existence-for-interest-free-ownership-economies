# Stage 289 — Lucas tree with general CRRA: price derived, optimality against all plans

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finitely many Markov states, transition weights `π s s'` (non-negative, rows sum to one), output `Y s > 0`, discount `0 ≤ β < 1`, felicity `c ^ p / p` with `p < 1`, `p ≠ 0` (any constant relative risk aversion `1 - p > 0` other than log, which is stage 286).

- `lin_fixed`: the equation `w = Y ^ p + β Π w` has exactly one solution (contraction, stage 258 inlined). `lin_fixed_pos`: it is strictly positive.
- `price_euler`: the tree price `P s = Y s (w s / Y s ^ p - 1)` satisfies the Euler equation `Y s^(p-1) P s = β ∑ π s s' Y s'^(p-1) (Y s' + P s')`.
- `price_unique`: it is the only price satisfying the Euler equation.
- `crra_bellman`, `crra_bellman_eq`: `V θ s = θ ^ p w s / p` satisfies the Bellman inequality against every affordable consumption and next share, with equality when the household consumes `θ Y s` and keeps `θ`.
- `plan_le`: for every history-dependent plan (consumption and shares positive, functions of the whole history, next share not contingent on next period's state, budget met at the tree price at every node), utility over `n` periods plus discounted continuation value is at most `V`.
- `plan_optimal`: if that continuation value tends to zero (transversality) and utility converges, total utility is at most `V`.
- `hold_attains`: holding the share forever attains `V` (its continuation term tends to zero, proved).

Reading: in the infinite-horizon Lucas economy with any CRRA felicity, the tree price is derived (not assumed), unique, and holding a constant share forever is optimal against every history-dependent plan satisfying transversality. Ownership needs no debt.

Limits: finite Markov state space; shares and consumption strictly positive (short sales and zero consumption excluded); only the tree trades (no other assets); transversality is a hypothesis on the competing plan; uniqueness of the optimal plan is not claimed.
