# Stage 302: Mantel/Debreu on a continuum of prices (weak-preference form)

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Goods form a finite set `S`. Prices range over a set `P` of unit vectors (`∑ p_s² = 1`) whose
coordinates are all at least `ε > 0`. This is Debreu's `S_ε`, a continuum of prices, not a
finite list. `Z` is any function on `P` that is bounded (`|Z p s| ≤ B`) and satisfies Walras' law
(`p · Z p = 0`). There is one consumer per good.

## Results
- `decomposition`, `xd_budget`, `alpha_pos`, `alpha_continuousOn`: with `α k p = Z p k + A p_k` and `A = B/ε + 1`, every weight is positive and continuous wherever `Z` is. Each trade `x k p = α k p (e_k − p_k p)` is budget-balanced at `p`, and the trades add up to `Z p` at every `p ∈ P` (Debreu 1974).
- `dot_lt_one`, `revealed_strict`: if consumer `k`'s choice at `p` is affordable at another price `q ∈ P`, then good `k` is strictly cheaper at `q`.
- `strong_axiom`: any chain of revealed preference (transitive closure) strictly lowers `p_k`, so revealed preference has no cycle of any length.
- `rationalize`, `u_mono`, `u_quasiconcave`: the utility `u_k(y) = −sup{q_k : q ∈ P, q·y ≤ 0}` is weakly monotone and quasiconcave on all of `ℝ^S`. At every `p ∈ P`, `x k p` reaches the highest utility on the budget `{y : p·y ≤ 0}`, which is `−p_k`.
- `mantel_full`: every bounded `Z` with Walras' law on `S_ε` is the sum of `|S|` budget-balanced trades, each optimal for a monotone quasiconcave utility at every price in the continuum.

## Reading
This is the Sonnenschein–Mantel–Debreu negative result on a continuum of prices: Walras' law (plus continuity and boundedness) is the only restriction aggregate excess demand inherits from individual rationality. Stages 296 and 300 proved it for finitely many prices. This stage covers the whole compact price set, with the same number of consumers as goods.

## Limits
- **Weak form.** Each `x k p` is *a* maximizer of a monotone quasiconcave utility, not *the unique* maximizer. The utility is constant along the ray through `x k p`, so the demand correspondence contains the decomposition but is not single-valued. Debreu's full theorem has strictly convex preferences with demand exactly `x k p`. That uniqueness step (pinning the scale `α`) is not formalised here and is the remaining gap.
- Weak monotonicity only, not strict. No consumption-set (non-negativity) constraint on `endowment + trade`.
- Boundedness of `Z` is assumed. On a compact `P` it follows from continuity, but that corollary is not stated.
- Continuity of `u` is not proved.
