# Stage 329: Finite Mantel with continuous utilities and endowments

Lean 4.35 + Mathlib. 31 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file reproduces stage 326 in full and adds 7 declarations.)

## Results
- `eu_continuous`, `eu_concave`, `eu_strictMono`: if `u` is continuous, concave and strictly monotone, so is the consumption utility `c ↦ u((c − e)/λ)` for any endowment `e` and scale `λ > 0`.
- `endow_transfer`: if `x` is the unique optimal trade on `{y | p·y ≤ 0}`, then `e + λx` is the unique optimal consumption on `{c | p·c ≤ p·e}`, and it spends exactly the endowment's value.
- `mantel_finite_endow`: take finitely many distinct, strictly positive, normalised prices and any `Z` satisfying Walras' law at them. There is a bound `M ≥ 0` such that, for every `λ > 0` and every endowment profile with all coordinates at least `λM`, the following hold. Each of the `|S|` consumers has a continuous, concave, strictly monotone utility over consumption. Each uniquely demands `e_i + λ x_i(p_k)` on their budget. All consumption is nonnegative. Aggregate excess demand equals `λ Z`.

## Reading
With `λ = 1` this is `Z` itself, for endowments of at least `M` in every good. For any floor `η > 0`, the choice `λ = η/(M+1)` admits every endowment of at least `η`, at the cost of rescaling `Z`. Stage 325 shows that rescaling cannot be avoided in general. This closes the stage 296 limit that consumers had zero-value endowments. It also brings the unique demand of stage 326 into the endowment setting.

## Limits
- Finite price sets only.
- The endowment bound `M` comes from the constructed trades. It is explicit but not small.
