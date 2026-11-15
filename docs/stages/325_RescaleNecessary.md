# Stage 325: The rescaling in stage 323 is necessary

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `excess_lower`: if every consumer's consumption is nonnegative, aggregate excess demand in good `i` is at least `-(∑ₖ eₖᵢ)`, minus the total endowment of `i`.
- `not_realizable`: an excess-demand vector below that bound in some good is not the aggregate excess demand of any nonnegative allocation.
- `scale_bound`: if `λ z` is realized and `zᵢ < 0`, then `λ ≤ (∑ₖ eₖᵢ) / (-zᵢ)`.
- `zbad` and its lemmas (`zbad_walras`, `zbad_homogeneous`, `zbad_continuousOn`): the field "sell `M` of good `i`, buy its value in good `j`" satisfies Walras' law at every positive price, is homogeneous of degree zero, and is continuous on the positive orthant.
- `rescale_necessary`: for every endowment profile and any two distinct goods, there is a continuous, degree-zero homogeneous field satisfying Walras' law that no nonnegative allocation realizes exactly at any price.
- `scale_forced`: for that field with size `M > 0`, any scale at which it is realized is at most `(∑ₖ eₖᵢ) / M`.

## Reading
Stage 323 realizes a positive multiple of an arbitrary Walras-law field from arbitrary endowments. This stage shows the multiple cannot be dropped. The obstruction is elementary: with nonnegative consumption, households can sell at most what they own. So a field asking for more net sales of a good than the economy's total endowment cannot be met, and the admissible scale shrinks in proportion.

## Limits
- The counterexample field is unbounded in `M`. For a bounded field, a fixed scale works whenever its bound sits below the endowments. That is the rescaling in stage 323 read in reverse, and it is not restated here.
- Nonnegative consumption is the only constraint used. Other consumption sets give other bounds.
