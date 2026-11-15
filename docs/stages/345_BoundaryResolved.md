# Stage 345: the boundary of a closed cap, resolved

Lean 4.35 + Mathlib. 32 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. The file repeats stage 335 in full and adds the results below.

## Results
- `uc_afriat`: the constant-weight consumer (`V q = −q_k`, `λ = 1`, trade `e_k − q_k q`) satisfies the continuum Afriat hypotheses on any set of unit prices with coordinates `≥ ε` (`ε ≤ 1`). Its canonical utility is `uc P k y = inf_{q ∈ P} q·(y − e_k)`.
- `boundary_nonunique`: let `p ∈ P` be a boundary price, i.e. `p_{s₀} = ε` for some `s₀`, with `0 < ε < 1`. For every `μ > 0`, the trade `dirk k p + μ (e_{s₀} − ε p)`
  - is on the budget,
  - differs from Debreu's trade, and
  - has the same utility, which is the maximum on the budget.

  The utility is continuous, concave and strictly monotone (proved in the same theorem). So the canonical Afriat utility of a closed cap has **non-unique demand at every boundary price**. The outward-cone gap left by stage 341 is therefore genuine for this construction.
- `closed_cap_unique_by_enlarging`: the cure. Suppose the weight satisfies the stage-334 conditions (bounds, relative Lipschitz `κ` with `4κ ≤ ε'`) on the open cap `{q unit, q > ε'}` for some `0 < ε' < ε`. Then one continuous, concave, strictly monotone utility has Debreu's trade as its **unique** maximiser at every unit price with all coordinates `≥ ε`, boundary prices included. The proof applies stage 335 to the open cap, which is rich by `rich_open`.

## Limits
- (a) concerns the canonical infimum utility only. It does not show that *every* utility rationalising the trades on `P` fails uniqueness.
- (b) needs the weight, and hence `Z` in Debreu's application, to be defined and well behaved slightly beyond `S_ε`. For Debreu's `Z` on `S_ε`, this requires an extension of `Z` that keeps Walras' law (not formalised). It also needs `4κ ≤ ε'`, which is slightly stronger than `4κ ≤ ε`.
- As before, the weight must be slowly varying (`κ ≤ ε'/4`). Debreu's `Z_k + A p_k` is not of that kind; see stage 342.
