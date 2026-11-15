# Stage 348: unique demand up to the boundary of the closed cap

Lean 4.35 + Mathlib. 47 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file is stage 347 in full, with the two results below added.

## Results
- `rich_band`: the open band `{q unit, ε' < q_s < β'}` is rich. For every budget direction `z` at a point `p` of the band, the arc `arc p z t` stays in the band for small `t > 0`. The proof uses continuity of the arc in `t` and `arc p z 0 = p`.
- `pk_unique_closed_cap`: choose `0 < ε' < ε ≤ β < β' < 1` and rationalise the weight-`p_k` consumer on the open band `(ε', β')` with stage 347. The resulting continuous, concave, strictly monotone utility has Debreu's trade as its **unique** maximiser at **every** unit price whose coordinates lie in the closed range `[ε, β]`, boundary prices included.

## Numerics (before the proof)
`num_boundary.py`: on the closed cap itself, the rationalising gap at boundary prices is exactly `0` (tight). On the enlarged band, the gap is strictly negative: `−2e-10` at `μ = 1e-2` and `−6e-9` at `μ = 5e-2`. The `0` at `μ = 1e-3` is a grid-resolution limit, not a counterexample.

## Limits
- The `σ`-hypothesis `hσa` must hold on the larger interval `[ε', β']`, and this is assumed.
- This is the `p_k` weight only.
