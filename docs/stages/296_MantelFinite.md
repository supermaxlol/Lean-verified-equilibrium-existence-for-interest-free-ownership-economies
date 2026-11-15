# Stage 296: Mantel on finite price sets with continuous preferences

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Finitely many distinct price vectors `p_k`, strictly positive and normalised (`Σ p_k(s)² = 1`), and any excess demands `Z_k` with Walras' law `p_k · Z_k = 0`.

## Results
- `afriat_continuous`, `afriat_concave`, `afriat_strictMono`: Afriat utilities `min_k (−T_k + L T_k p_k · y)` are continuous, concave and strictly monotone.
- `afriat_potential`: data ordered by a strict potential is rationalised by such a utility.
- `dot_mdir`: Debreu's directions `e_i − p_i p` are budget-balanced.
- `mantel_finite`: with as many consumers as goods there are continuous, concave, strictly monotone utilities whose optimal net trades at each `p_k` sum to `Z_k`.

## Reading
This closes the gap left at stage 292 (whose utilities were discontinuous) for every finite set of prices: Walras' law is still the only restriction, now with well-behaved preferences.

## Limits
- Finite price sets only. The full continuous-function Mantel theorem (Mantel 1974, Debreu 1974) for a whole excess demand function is NOT proved.
- Afriat preferences are concave but not strictly concave, so demand need not be unique; `x i k` is an optimum, not the only one.
- Consumers have zero endowment value in net-trade form (budget `p · y ≤ 0`).
