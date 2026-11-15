# Stages 332–333: an explicit endowment bound, and when no rescaling is needed

Lean 4.35 + Mathlib. 41 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- **332: explicit bound.**
  - `Mbd p Z = 1 + ∑ₖ∑ᵢ |Z k i| / p k i + ∑ₖ∑ᵢ |Z k i|` is computed from the excess demands `Z` and the prices `p` alone.
  - `mx_bound`: every coordinate of every consumer's net trade has absolute value at most `Mbd p Z`.
  - `mantel_explicit_endow`: this is stage 329 with the constant made explicit. For any scale `λ > 0` and any endowments whose coordinates are all at least `λ·Mbd p Z`:
    - consumers have continuous, concave, strictly monotone utilities with unique demands;
    - consumption is nonnegative and budgets bind;
    - aggregate excess demand is `λ Z`.
- **333: the scale-1 case.**
  - `mantel_unscaled` (sufficient): if every endowment coordinate is at least `Mbd p Z`, then the given `Z` itself (`λ = 1`) is the aggregate excess demand of unique utility maximisers.
  - `excess_lower` and `unscaled_impossible` (necessary): if `Z k s < −∑ᵢ eᵢ s` for some price `k` and good `s`, then no nonnegative allocation has aggregate excess demand `Z k`.

## Reading
Stage 325 showed that rescaling is sometimes necessary. Stage 333 gives the matching positive statement: with large enough endowments, no rescaling is needed, and "large enough" is a concrete number.

## Limits
- The two conditions in 333 do not meet. The sufficient condition is a per-consumer floor `Mbd p Z`. The necessary condition is an aggregate floor `−Z`. Endowments between the two are not classified.
- `Mbd` is a crude bound and not claimed to be sharp.
- Finitely many prices only. This is not the continuous case.
