# Stage 343: optimal trades are stable under locally uniform limits (the grid route)

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `uniform_limit_optimal`: let utilities `u_n` converge locally uniformly to a continuous `U`, let `x_n` be optimal for `u_n` on the budget at price `q_n`, and let `q_n → p > 0` and `x_n → z`. Then `z` is on the budget at `p` and optimal for `U`.
- `aggregate_limit`: if the consumers' trades add up to `Z(q_n)` at every grid price and `Z` is continuous, the limit trades add up to `Z(p)` exactly.
- `grid_limit`: the two combined, for finitely many consumers.

## Meaning
This is the estimate-free half of the grid route. Rationalise `Z` exactly on finer and finer finite grids (finite Mantel), extract limits, and the aggregate stays exact while each limit trade stays optimal.

## Limits (what a grid theorem still needs)
1. **Grid-independent bounds** on the finite Afriat numbers, so that the grid utilities are uniformly Lipschitz and the trades bounded. Not proved; the finite bounds of stages 323–333 are not shown to be uniform in the grid.
2. **A compactness step** (Arzelà–Ascoli and a diagonal argument) to obtain the convergent subsequences. Standard, but not formalised here.
3. **Uniqueness is lost in the limit.** The result can only give a *selection* from each consumer's demand correspondence, never unique demand (compare `no_unique_of_jump`, stage 334).
