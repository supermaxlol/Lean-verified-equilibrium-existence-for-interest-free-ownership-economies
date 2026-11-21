# Stage 363: convergence, equilibrium paths, and wealth-dependent patience

Lean 4.35 + Mathlib. 19 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/OwnershipDynamics.lean`](../../formal/OwnershipDynamics.lean).

Continues stage 357 (definitions restated so the file stands alone). With full access, the
equilibrium issuance step is `T x h = (amp · s h x h / B s x + g σ c) / (1 + g)` (stage 357,
`step_full`), where `B s x = ∑ s k x k` and `amp = 1 + g (1 − σ)`.

* **Convergence** (`contract_step`, `converges`, `converges_tendsto`, `fixed_unique`): with
  constant saving rates, `σ > 0` and `g > 0`, every positive starting distribution converges to
  the long-run distribution `y`, geometrically: `|x n h − y h| ≤ λ ^ n (K0 − 1)` with the explicit
  factor `λ = 1 − g σ c / (1 + g) < 1`, where `K0` bounds the initial spread of the ratios
  `x h / y h`. The proof is a contraction of that spread: each step maps the ratio
  `x h / y h` to a convex combination of `(x h / y h) / ρ` and `1`.
* **Equilibrium with forward-looking saving**:
  - log utility (`γ = 1`, `log_equilibrium`, `log_equilibrium_unique`, `log_equilibrium_converges`):
    for every positive starting distribution a perfect-foresight equilibrium path exists, it is
    unique, and it converges to the long-run distribution;
  - CRRA steady state (`steady_equilibrium`): for any curvature `γ ≠ 0`, the long-run
    distribution with the constant return `R = B ^ (−γ)` is a perfect-foresight equilibrium, under
    `b h B ^ (γ − 1) < 1` (automatic when `γ ≥ 1`, `steady_condition`). The long-run
    distribution does not depend on `γ` except through the patience factors `b`.
* **Wealth-dependent patience** (`Tp`, `rank_preserved`, `threshold_equalizes`, `ex_equal_rest`,
  `ex_unequal_rest`): if patience rises with wealth, the step never reverses the ranking. With a
  threshold `θ` (patience `hi` at or above it), if `(1 + g) θ ≤ g σ c` every household is above the
  threshold after one step and the economy converges to equal shares. Without that, identical
  households can stay unequal forever: an explicit two-household economy has both the equal
  distribution and `(1/5, 4/5)` as rest points.

Limits: convergence is proved for constant saving rates (exogenous, or the log-utility
equilibrium); a transitional equilibrium path with forward-looking saving and `γ ≠ 1` is not
proved to exist (only its steady state); the return on saved ownership is `1 / B` as in stage 357;
the threshold result is a sufficient condition, and existence of a long-run distribution with
general wealth-dependent patience is not proved.
