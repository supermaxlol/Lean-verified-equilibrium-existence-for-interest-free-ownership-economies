# Stage 365: a long-run distribution with wealth-dependent patience and access

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/EndogenousRest.lean`](../../formal/EndogenousRest.lean).

Continues stages 356, 363 and 364 (definitions restated). Ownership shares `x` lie in the simplex.
Each period a household keeps the saved part of its ownership, `post h = s h x h / B` with
`B = ∑ s k x k`, and new units are issued at rate `g`: a fraction `σ` equally (`c` each,
`N c = 1`), the rest pro rata among households with access, weighted by an access intensity
`a h ∈ [0, 1]` (stage 356 with weights in place of a set):

`step h = (post h + g (σ c + (1 − σ) a h post h / W)) / (1 + g)`,  `W = ∑ a k post k`.

Here both the saving rate `s` and the access intensity `a` are functions of the whole current
distribution `x` (`Ψ`). This covers patience that depends on a household's own wealth (stage 363,
`s h = φ (x h)`), on its rank, or on the distribution as a whole, and access that depends on
wealth through any continuous rule.

* **Existence** (`exists_rest`): if the saving rule and the access rule are continuous on the
  simplex, saving rates are positive, access intensities are non-negative and some household with
  saved ownership has access (`W > 0`), then a long-run distribution exists: a point of the
  simplex mapped to itself. Every household holds at least `g σ c / (1 + g)` in it. The proof
  applies Brouwer's fixed-point theorem (`FixedPointTheorems.brouwer`) to the simplex.
* `exists_rest_patience`: full access, patience `φ (x h)` for any continuous positive `φ`.
* `exists_rest_access`: access intensities bounded below by some `α0 > 0`.
* **Forward-looking saving** (`exists_stationary_forward`): patience `β x h` may depend on the
  distribution; at a constant return `Q` the infinite-horizon rule of stage 364 saves the
  fraction `b Q ^ ((1 − γ) / γ)` (`stationary_rule`). A distribution together with the return
  `Q = (∑ β x k x k) ^ (−γ)` exists at which this saving rate is used, the return is the one the
  issuance step produces (`Q = 1 / B`), and the distribution reproduces itself.
* **No uniqueness** (`two_rest_continuous`): with a continuous, increasing patience rule
  (`φc`, linear between `1/5` and `4/5` and flat outside) both the equal distribution and
  `(1/5, 4/5)` are long-run distributions. Continuity alone does not restore uniqueness.

Limits: existence only; neither uniqueness nor convergence to a long-run distribution is proved
(the example rules out uniqueness in general). Discontinuous rules (the threshold patience of
stage 363, the all-or-nothing access sets of stage 356) are not covered. In
`exists_stationary_forward` the saving rate equals the stationary infinite-horizon rule only when
`b Q ^ ((1 − γ) / γ) < 1`, which is not checked by the theorem; optimality and the transition path
to the stationary state are not proved.
