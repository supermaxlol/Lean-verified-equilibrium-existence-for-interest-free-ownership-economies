# Stage 297: Transversality derived from position limits

Lean 4.35 + Mathlib. 3 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Same Lucas economy as stage 293 (finite states, Markov kernel `π` with rows summing to 1,
discount `0 ≤ β < 1`, many assets with prices `P` and dividends `d`, supergradient `mu`).
Plans are history-dependent portfolios `x s h`. The new hypothesis is a position limit:
`|x s h j| ≤ B` for every node and asset.

## Results
- `Fv_bound`: the one-period value of any portfolio bounded by `B` is bounded by an explicit `K`.
- `term_bound`: the terminal term at horizon `n` is at most `β ^ n * K` in absolute value (induction over the event tree).
- `hold_beats_bounded_plans`: for every bounded plan the utility gap against holding the tree is at most `β ^ n * K` at every horizon, is eventually below every `ε > 0`, the terminal term tends to 0, and any limit of the gap is `≤ 0`.

## Reading
Stage 293 assumed the transversality term vanishes. Here it is derived. Position limits rule out
Ponzi debt rollover, and discounting at `β < 1` then forces the terminal term to zero. The bound
`β ^ n * K` holds at every horizon, so no convergence of the gap itself is needed.

## Limits
- Uniform position bounds are a sufficient condition. They are not the general no-Ponzi condition (e.g. debt growing slower than `β^{-n}`), which is not proved here.
- Finite state space, finitely many assets.
