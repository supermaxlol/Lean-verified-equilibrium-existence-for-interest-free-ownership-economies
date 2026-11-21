# Stage 364: an equilibrium path with forward-looking saving, finite and infinite horizon

Lean 4.35 + Mathlib. 14 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/FiniteHorizonPath.lean`](../../formal/FiniteHorizonPath.lean).

Continues stages 357 and 363 (definitions restated). Households have CRRA utility with curvature
`γ > 0` and patience factor `b h = β h ^ (1 / γ)`. A household that saves at date `t` earns the
gross return `Q t` on saved ownership, and the return is set by the issuance step: `Q t = 1 / B`,
with `B = ∑ s h x h` the aggregate saving rate weighted by ownership (as in stage 357).

* **The saving rule** (`F`, `savN`, `euler`, `terminal`): with `k` dates left, the ratio of planned
  future to present consumption is `F (k + 1) t = b r t (1 + F k (t + 1))`, `F 0 = 0`, where
  `r t = Q t ^ ((1 − γ) / γ)`; the saving rate is `F / (1 + F)`. `euler` proves that this rule
  meets the budget constraint and the CRRA Euler equation `c (t + 1) = (β Q t) ^ (1 / γ) c t`
  exactly, and `terminal` that the household consumes everything at the last date.
* **Finite horizon** (`exists_finite_equilibrium`, `finite_equilibrium`): for every `γ > 0`, every
  positive patience profile, every positive starting distribution and every horizon `N`, a
  perfect-foresight equilibrium path exists. The proof applies Brouwer's fixed-point theorem
  (`FixedPointTheorems.brouwer`) to the return path in a box `[1, M] ^ N`. Every equilibrium
  return lies in `[1, M]`, with `M` independent of `N`.
* **Infinite horizon** (`FInf`, `FInf_rec`, `IsEqInf`, `infinite_equilibrium_of`): with
  infinitely many dates the rule becomes the convergent series
  `FInf t = ∑ j, ∏ i ≤ j, b r (t + i)`, which satisfies the same recursion
  `FInf t = b r t (1 + FInf (t + 1))`. `infinite_equilibrium_of` shows that a cluster point of the
  finite-horizon equilibria (in the compact product `[0, 1] ^ ℕ × [1, M] ^ ℕ`) is an
  infinite-horizon equilibrium, whenever `b h q ^ ((1 − γ) / γ) ≤ bmax < 1` on `[1, M]`.
  * `infinite_equilibrium`: `γ ≥ 1` (log utility included) and every `b h < 1`.
  * `infinite_equilibrium_low`: `γ ≤ 1`, under the explicit condition
    `b h ((1 + bmin) / bmin) ^ ((1 − γ) / γ) < 1`, i.e. the plan has finite value even at the
    highest return the economy can produce.

Limits: uniqueness of the path is not proved (finite or infinite horizon); for `γ < 1` the
infinite-horizon result needs the stated condition, and it is not shown to be necessary; the
Euler equation and budget constraint are proved, but optimality of the rule (sufficiency of these
conditions, including a transversality condition) is not formalized; convergence of the path to
the long-run distribution is not proved; the return is `1 / B` as in stage 357; patience and
access remain exogenous.
