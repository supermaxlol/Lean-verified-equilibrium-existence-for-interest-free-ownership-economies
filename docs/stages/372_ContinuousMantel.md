# Stage 372: Debreu's decomposition for continuous excess demand, with revealed-preference rationalisation of each consumer

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ContinuousMantel.lean`](../../formal/ContinuousMantel.lean).

Stage 353 writes a Walras excess demand `z` on unit prices as a sum of `n` consumers' trades
`x_k(p) = (A p_k + z_k(p)) (e_k − p_k p)` and shows that each consumer maximises a continuous,
concave, strictly monotone utility, when `z` is bounded and Lipschitz. Stage 355 shows that the
Lipschitz bound cannot be removed by approximation. Reading stage 353 again, the Lipschitz
hypothesis enters at exactly one place: the continuum Afriat inequalities (`debreu_delta`,
`debreu_weight_afriat`), which build the *utility*. The decomposition itself
(`debreu_decomp`) is algebra and needs nothing.

This file separates the two steps and proves the first in full for continuous `z`, and the
second in a weaker form.

* `dot_le_one`, `dot_eq_one`: for unit vectors, `p · q ≤ 1`, with equality only if `p = q`.
* `decomp`: for unit `p` with `p · z(p) = 0`, `z(p) = Σ_k x_k(p)` (any weights `A p_k + z_k`).
* `budget`: each consumer's trade is affordable and exhausts the budget, `p · x_k(p) = 0`.
* `trade_continuousOn`: if `z` is continuous on the price set, so is each `x_k`.
* `step_lt`: if `x_k(q)` is affordable at `p ≠ q` (that is, `p · x_k(q) ≤ 0`), then
  `p_k < q_k`. This holds for every positive weight, with no continuity at all.
* `warp`: each consumer satisfies the weak axiom of revealed preference.
* `trade_injOn`: different prices give different trades.
* `no_cycle`: each consumer satisfies the strong axiom: the transitive closure of strict
  revealed preference has no cycle (`p_k` strictly rises along any chain).
* **`rationalised`**: for each `k` there is a complete, transitive, antisymmetric preference
  (a linear order on bundles) for which, at every price in the set, `x_k(p)` is the unique best
  bundle in the budget `p · y ≤ 0`. This is Richter's route: the revealed-preference partial
  order is extended by the Szpilrajn theorem (Mathlib's `extend_partialOrder`).
* `positive_weight`: if `|z_k| ≤ M` and `p_k ≥ ε > 0`, then `A = M / ε + 1` makes every weight
  `A p_k + z_k` positive.
* **`continuous_decomposition`**: so a continuous (or merely bounded) Walras `z` on the
  `ε`-interior unit price set is the sum of `n` continuous trades, each exhausting its budget,
  satisfying the weak and strong axioms, and each the unique best choice for a complete,
  transitive preference.

Reading: the part of Debreu's theorem that is about *choice* (each piece is the demand of a
consistent chooser) holds for continuous excess demand with no Lipschitz bound. What stage 353
adds, and what is still open for continuous `z`, is the *regularity* of the preference.

Limits: the preference in `rationalised` is not shown to be continuous, monotone or convex, and
is not shown to be represented by a utility function. Debreu's and Mantel's theorems give
continuous, monotone, strictly convex preferences; for continuous, non-Lipschitz `z` that
stronger statement is not proved here and remains open in this program. Trades are on the
unit sphere with positive coordinates, the budget is `p · y ≤ 0`, and consumption is not
required to be non-negative (as in stage 353).
