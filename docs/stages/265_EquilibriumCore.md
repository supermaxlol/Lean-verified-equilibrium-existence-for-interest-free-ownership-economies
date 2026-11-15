# Stage 265 — A competitive equilibrium allocation lies in the core

Lean 4.35 / Mathlib, 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: exchange economy with finitely many households and goods, prices `p ≥ 0`, each
`x i` optimal in `{x ≥ 0 | p · x ≤ p · ω i}`. Utilities are semi-strictly quasi-concave
and non-satiated.

- `cost_strict` — a strictly preferred bundle costs strictly more than the endowment.
- `cost_weak` — a weakly preferred bundle costs at least the endowment.
- `not_blocked` — no coalition can reallocate its own endowments so that every member is
  at least as well off and one member strictly better off.
- `pareto_efficient` — the grand-coalition case.

Limits: exchange only; coalitions have no production. The converse (core convergence in
large economies) is not proved.
