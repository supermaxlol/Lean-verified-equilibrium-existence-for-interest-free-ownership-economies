# Stage 295: boundary allocations for log and CRRA with p < 0

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Lean's `Real.log 0` and `0 ^ p` are finite junk values. Utility is therefore extended into `EReal`: `ext u π c = Σ π s u(c s)` if every `c s > 0`, and `⊥` otherwise.

## Results
- `log_blowup`: for every `M`, `log c < -M` once `c < exp(-M)`.
- `crra_neg_blowup`: for `p < 0` and every `M`, `c^p/p < -M` once `c ≤ K^(1/p)`.
- `ext_optimum_interior`: for any felicity, an optimum of the extended utility over non-negative affordable bundles is strictly positive in every state.
- `log_optimum`: with log felicity the optimum exists and equals `c s = π s W / q s`.

## Reading
"Utility at zero is −∞" is now a formal statement: `⊥` is the value, and the blow-up lemmas show it is the limit of the real felicity. Boundary bundles are never optimal, so earlier interior results cover every optimum.

## Limits
- Existence of the optimum is proved in closed form for log only. For `p < 0` the stage shows interiority of any optimum; existence in closed form is stage 298.
- The blow-up lemmas justify `⊥` but do not prove continuity of `ext` in EReal's topology.
