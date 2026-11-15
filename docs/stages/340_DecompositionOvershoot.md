# Stage 340: Debreu's decomposition overshoots the necessary floor

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Result
- `overshoot`: take two goods, the two prices `(3/5, 4/5)` and `(4/5, 3/5)`, and `Z ≡ 0`. The decomposition of stage 337 has `mx 0 1 0 = 36/125` and `mx 1 0 0 = −48/125`. Every endowment profile meeting the stage-337 floors `e_i ≥ −mx_i(p_k)` then has `e_0 0 + e_1 0 ≥ 12/125`, while the necessary aggregate floor is `−Z = 0`.

## Meaning
The consumer-specific floors of stage 337 are strictly stronger than necessary, already for `n = 2` and two prices. The excess comes from taking `max_k` consumer by consumer (`∑_i max_k`) instead of on the aggregate (`max_k ∑_i`). Random searches show this overshoot is generic, not a corner case.

## Limits
- This is a counterexample to the *sharpness of one decomposition*. It does not show that the necessary floor cannot be reached by some other decomposition across several prices. At a single price it can (stage 338).
