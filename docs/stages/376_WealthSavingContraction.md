# Stage 376: wealth-dependent saving that still gives a unique, globally stable rest point

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/WealthSavingContraction.lean`](../../formal/WealthSavingContraction.lean).

Stage 365 proved that the ownership dynamics have a rest point for any continuous rule that makes
saving depend on wealth, and gave such a rule with two rest points. Stage 367 proved uniqueness
and geometric convergence when everyone saves at the same rate. This file covers the case in
between: saving that depends on the household's own wealth share, with an explicit condition
on how strongly it may depend on it.

Setting (full access, as in stage 365 with `α = 1`): household `h` with share `x h` saves at
rate `φ (x h)`; its post-saving share is `p h = φ (x h) x h / Σ φ (x k) x k`, and issuance gives
`x' h = ((1 + g (1 − σ)) p h + g σ c) / (1 + g)` (`T`; `step_eq` checks that this is the
stage 365 step). Assume on `[0, 1]`: `A ≤ φ ≤ A + δ` with `A > 0`, and `φ` is `L`-Lipschitz.
Distances are measured by `d1 x y = Σ |x h − y h|`.

* `post_lip`: the saving-reweighting map `x ↦ p` is Lipschitz on the simplex with constant
  `1 + 2 (δ + L) / A` (for constant saving, `δ = L = 0`, the constant is `1`).
* `T_lip`: the whole update is Lipschitz with constant
  `K = (1 + g (1 − σ)) / (1 + g) · (1 + 2 (δ + L) / A)`.
* **`wealth_saving_contraction`**: if `K < 1`, there is exactly one rest point on the simplex,
  and from every initial distribution the ownership path converges to it, with
  `d1 (x_n) x⋆ ≤ K ^ n · d1 (x_0) x⋆`. (Existence comes from the Banach fixed point theorem in
  Mathlib's `ℓ¹` space `PiLp 1`; uniqueness, the rate and the convergence are proved directly.)
* `example_converges`: the condition is not empty: saving `φ z = 1/2 + z/20`, rising with
  wealth, with `g = 1` and `σ = 3/5` gives `K = 49/50 < 1`.
* `no_contraction_of_two_rest`, `stage365_rule_fails`: if the update has two different rest
  points, no choice of `A, δ, L` meets the condition; in particular the stage 365 rule with two
  rest points fails it for every choice of constants, as it must.

Reading: saving may rise with wealth and the long-run distribution is still unique and reached
from every starting point, provided the dispersion of saving rates `δ` and their sensitivity to
wealth `L` are small relative to the lowest saving rate `A` and the issued share `σ` is large
enough. The condition `K < 1` is sufficient, not necessary.

Limits: full access only (no access rule); saving depends on the household's own share only;
the condition is sufficient and is likely conservative (the constant `2` in `post_lip` comes from
a crude bound); between the condition and the stage 365 two-rest-point example, uniqueness is
not settled; threshold rules are not covered.
