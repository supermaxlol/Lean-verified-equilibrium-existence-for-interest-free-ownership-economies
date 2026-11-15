# Stage 338: exact single-price decomposition with the necessary floor

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `kink t = min t (t/2)`: continuous, concave, strictly increasing, `kink t ≤ t`, and `kink t < t` for `t < 0`.
- `ku p c0 c = ∑_s p_s · kink(c_s − c0_s)`: a continuous, concave, strictly monotone utility. It satisfies `ku ≤ p·(c − c0)`, and `c0` is its **unique** maximiser on the budget `p·c ≤ p·c0` (`ku_unique`).
- `single_price_exact`: at one price `p > 0` with `p·Z = 0`, let the endowments `e_i` have `p·e_i > 0` and meet the **aggregate** floor `−Z_s ≤ ∑_i e_i s`. This floor is necessary, since consumption is nonnegative. Set `c_i = (p·e_i / p·E)(E + Z)`. Then each `c_i` is nonnegative and affordable with equality, the `c_i − e_i` sum to `Z` exactly, and each `c_i` is the unique maximiser of a continuous, concave, strictly monotone utility.

## Meaning
At a single price, the gap between the stage-337 consumer-specific floors and the necessary aggregate floor closes completely. The gap is an artefact of Debreu's decomposition, not of rationalisation.

## Limits
- One price only. With several prices the consumption shares `c_i(p)` must come from one utility per consumer for all prices at once. That is the multi-price problem of stages 323–337, which this does not solve.
