# Stage 357: the long-run distribution, wealth-dependent access, growth, and forward-looking saving

Lean 4.35 + Mathlib. 27 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/LongRunOwnership.lean`](../../formal/LongRunOwnership.lean).

Builds on the stage-356 issuance equilibrium (definitions restated here so the file stands alone).

* Long-run distribution (`stationary_exists`, `stationary_fixed`, `stationary_unique`,
  `fixed_form`): with full access and any `σ > 0`, there is exactly one long-run distribution.
  It has the closed form `x h = g σ c / (1 + g − l s h)`, where `l` solves `∑ x h = 1`.
* Its properties: every share is at least `g σ c / (1 + g)` (`stationary_floor`); more patient
  households hold strictly more (`stationary_monotone`, `stationary_l_pos`); with a common saving
  rate it is the equal distribution (`common_stationary`); the return is `l / (1 + g (1 − σ))`
  (`stationary_return`).
* Wealth-dependent access (`above`, `pathA`): only households holding at least `θ` take part in
  the pro rata part. `trapped`: below the threshold, a household whose saving rate is at most `κ`
  times the lowest stays below forever when `κ θ + g σ c ≤ (1 + g) θ`; `trapped_decay`: with no
  equal part it is diluted geometrically. `escape`: when `θ < g σ c / (1 + g − lo/hi)`, every
  household eventually holds more than `θ` for good. `common_dichotomy`: with a common saving rate
  the line is exactly `σ c` against `θ`.
* Growth (`growth_gap`, `growth_gap_lower`, `common_no_cost`, `pro_rata_growth_limit`): the
  aggregate saving rate falls short of the highest by at most the spread of patience times the
  share not held by the most patient, and by at least the gap to the second-highest times that
  share. Under pro rata issuance it tends to the highest rate; with equal patience the issuance
  rule costs no growth.
* Forward-looking CRRA saving (`fut`, `fsave`, `fut_recursion`, `recursion_unique`,
  `fut_compare`, `save_ratio`, `forward_takes_all`): the Euler-and-budget recursion
  `u t = b r t (1 + u (t + 1))` (with `b = β ^ (1/γ)`, `r t = R (t+1) ^ ((1−γ)/γ)`) has exactly
  one bounded solution, the discounted sum `fut`. A less patient household's sum is at most
  `b k / b h` times the more patient one's, at every date and along any bounded return path, so
  its saving rate is at most a fixed fraction `ρ < 1` of the other's. Under pro rata issuance the
  most patient household therefore takes everything, along any return path with
  `0 < r t ≤ rhi`, `b h rhi < 1`, including an equilibrium one.

Limits: saving is characterised by the Euler equation and budget, not derived from a utility
maximisation proof; existence of a perfect-foresight equilibrium path with forward-looking saving
is not proved (the result holds on any such path); convergence to the long-run distribution is
not proved; access and patience are exogenous.
