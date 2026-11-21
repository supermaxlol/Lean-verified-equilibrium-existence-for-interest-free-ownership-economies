# Stage 374: a monotone, quasi-concave utility for each Debreu consumer, for continuous excess demand

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ContinuousRationalisation.lean`](../../formal/ContinuousRationalisation.lean).

Stage 372 splits a continuous Walras excess demand `z` on unit prices into `n` trades
`x_k(p) = (A p_k + z_k(p)) (e_k − p_k p)` and shows each is the unique best choice for some
complete, transitive preference (a linear order), with no regularity. This file replaces the
linear order by a real-valued utility function with two of the regularity properties of the
classical statement, still with no Lipschitz bound on `z`.

The construction is an explicit family of upper contour sets. Write `P` for the price set,
`w` for the weight and `x(q) = w(q) (e_k − q_k q)` for the trade. For a level `t` let

  `m_t(ν) = inf {ν · x(q) : q ∈ P, q_k ≤ t}`  and  `C_t = {y : ν · y ≥ m_t(ν) for all ν ≥ 0}`,

the smallest closed convex upward-closed set containing every trade chosen at a price with
`q_k ≤ t` and described by non-negative normals. The utility is `u(y) = −τ(y)`, where `τ(y)` is
the least level `t` with `y ∈ C_t` (and `2` if there is none).

* `Up_convex`, `Up_mono`: each `C_t` is convex, and the family grows with `t`.
* `not_mem_below`: if `p · y ≤ 0` then `y ∉ C_t` for every `t < p_k`. This is the only place the
  shape of the trades enters: for `q_k ≤ t < p_k`, `p · x(q) = w(q)(p_k − q_k p·q) ≥ w_min (p_k − t)`.
* `tau_trade`: `τ(x(p)) = p_k`, so `u(x(p)) = −p_k`.
* **`optimal`**: `x(p)` maximises `u` on the budget `{y : p · y ≤ 0}`.
* **`unique`**: if `x` is continuous (within `P`) at `p`, then `x(p)` is the *only* maximiser:
  every other affordable bundle has strictly lower utility. The proof tilts the normal `p` to
  `p ± η e_j` and uses only the modulus of continuity of `x` at `p` and the quadratic gap
  `1 − p·q ≥ dist(p,q)² / 2`; no Lipschitz constant appears.
* **`monotone_util`**: `u` is non-decreasing in every good.
* **`quasiconcave`**: `u` is quasi-concave (its upper level sets are convex), so the preference
  is convex.
* **`continuous_mantel_utility`**: for a Walras `z` that is continuous and bounded on the prices
  with every coordinate at least `ε` (`Peps`), `z` is the sum of the `n` trades, and each trade
  is, at every such price, the unique maximiser on its budget of a real-valued, non-decreasing,
  quasi-concave utility.

Reading: with only continuity of `z`, each Debreu consumer is represented by a utility function
that is monotone and gives convex preferences, and demand is the unique maximiser. Compared with
stage 372, the linear order is replaced by a utility with these two regularity properties.

Limits: the utility is **not shown to be continuous**, and in general this particular
construction is not: `C_t` is the smallest admissible upper contour set, and when
`t ↦ m_t(ν)` is flat for some normal `ν` (which can happen for a non-smooth weight) the family
does not grow there and `u` jumps. The preference is convex but not shown to be strictly
convex, and `u` is non-decreasing but not shown to be strictly increasing; utility values lie
in `[−2, 0]`. Debreu's and Mantel's theorems give continuous, strictly monotone, strictly convex
preferences; for continuous, non-Lipschitz `z` that full statement is still not proved in this
program, and the remaining step is continuity of the utility. Trades are on the unit sphere,
the budget is `p · y ≤ 0`, and consumption is not required to be non-negative (as in stages 353
and 372).
