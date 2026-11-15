# Stage 262 — Sonnenschein–Mantel–Debreu in revealed-preference form

Lean 4.35 / Mathlib, 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The stage-256 source (Debreu
decomposition) is inlined.

Setting: finitely many goods `S` (at least two), one agent per good. Agent `i` has the
fixed utility `util i w = - sSup (level i '' afford w)` on net trades, where
`level i q = q i ^ 2 / ∑ s, q s ^ 2` and `afford w` is the set of strictly positive prices
at which `w` costs at most zero.

- `rp_level`, `exists_higher` — the two revealed-preference inequalities behind the
  construction.
- `util_demand`, `util_le`, `util_lt` — the agent's own net trade attains the maximum
  of `util i` on the budget set, and anything costing strictly less is strictly worse.
- `decompose_rational` — one price at a time.
- `mantel_rationalizable` — for ANY function `z` with `p · z p = 0` on strictly positive
  prices there are net-trade functions `f i` with `∑ i, f i p = z p`, each on the budget
  hyperplane, each maximising the fixed `util i` over `{w | p · w ≤ 0}`, and each strictly
  preferred to every net trade costing strictly less.

Reading: individual utility maximisation with non-satiation puts no restriction on
aggregate excess demand beyond Walras' law.

Limits: this is the revealed-preference form. The utilities are defined on net trades,
and are not shown to be continuous, monotone or quasi-concave, nor to come from a
consumption set with endowments. `z` need not be continuous or homogeneous, and the
maximiser is not shown to be unique. The classical theorem with well-behaved preferences
is not proved.
