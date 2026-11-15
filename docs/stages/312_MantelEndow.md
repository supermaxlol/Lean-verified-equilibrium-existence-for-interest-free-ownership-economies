# Stage 312: Mantel with endowments

Lean 4.35 + Mathlib. 14 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

`mantel_endow`: let `Z` be continuous on a compact `P ⊆ S_ε` and satisfy Walras' law. Then there are `A` and an explicit `M = 2(B_Z + |A|) ≥ 0` such that for every endowment profile with all `e_k,i ≥ M` and every `p ∈ P`:
- consumption `c_k(p) = e_k + x_k(p)` aggregates to excess demand: `Σ_k (c_k − e_k) = Z(p)`;
- consumption is nonnegative;
- the budget binds: `p·c_k = p·e_k`;
- `c_k(p)` is the unique maximizer of `U_k(c) = u_k(c − e_k)` (monotone, quasiconcave) on `{c | p·c ≤ p·e_k}`.

`xd_abs`: trades are bounded by `2(B_Z + |A|)`, which gives the positivity condition.

Honest limits:
- Endowments must be large enough (≥ M), not arbitrary.
- Continuity of utility is not proved.
- Preferences depend on the price domain P (constructed, as in Mantel).
