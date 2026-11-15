# Stage 290 — Wilson's converse: linear sharing forces common cautiousness

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: two households with differentiable marginal utilities `gi`, `gj` (derivatives `hi`, `hj`, `hi` never zero) share output by affine rules `bi Y + ki` and `bj Y + kj` (`bi, bj ≠ 0`) satisfying the efficiency conditions `λi gi(bi Y + ki) = μ Y = λj gj(bj Y + kj)` for all `Y` in an open set `U`. Risk tolerance `T` is defined by `T x · g'(x) = -g(x)` and is differentiable with derivative `T'` (cautiousness).

- `foc_deriv`: differentiating the efficiency condition.
- `tolerance_share`: `Ti(ci Y) · μ'(Y) = -bi · μ(Y)`: each household's risk tolerance is its slope times the aggregate tolerance (Wilson's identity, affine case).
- `wilson_converse`: `Ti'(bi Y + ki) = Tj'(bj Y + kj)` for all `Y` in `U`: cautiousness agrees along the rules.
- `wilson_hara`: for HARA households (`T` affine with slope `ρ`), affine efficient sharing requires `ρi = ρj`.

Reading: together with stage 282 (common slope gives affine sharing), this is Wilson's (1968) characterisation in the two-household case: affine sharing rules are efficient exactly when households share a common cautiousness, and within HARA exactly when the slope is common.

Limits: two households (the n-household case follows pairwise but is not stated); differentiability of marginal utility and risk tolerance is assumed; the forward direction for general HARA is stage 282's shift class.
