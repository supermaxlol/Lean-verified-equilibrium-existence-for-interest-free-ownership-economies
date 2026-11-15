# Stage 354: equity and debt with heterogeneous CRRA — the fixed claim is traded

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Extends stage 285 (equity + a fixed claim, common homothetic felicity, where the fixed claim is never traded).

## Results
- `euler_necessary`: if `(θ, b)` is optimal among all affordable share/bond positions with positive consumption, the Euler condition `Σ_s π_s u'(c_s)(q_B Y_s − q_E) = 0` holds (derivative of a local maximum along the budget line).
- `crra_euler_zero_bond`: for marginal utility `c^(−γ)` and a zero bond position, Euler gives `q_B E[Y^{1−γ}] = q_E E[Y^{−γ}]`.
- `cheb_strict`: Chebyshev's sum inequality, strict, for weights and comonotone sequences.
- `tilted_strict`: `E[Y^{1−γ}]/E[Y^{−γ}]` is strictly decreasing in `γ` whenever output takes two values with positive probability.
- `hetero_crra_debt_traded`: at any prices with `q_B > 0` where every household (CRRA `γ_i`) is at an interior optimum, if two households have different `γ`, **some bond position is non-zero**.
- `issuer_and_holder`, `hetero_crra_issuer_holder`: with bond-market clearing `Σ b_i = 0`, some household issues the fixed claim and another holds it.

## Reading
With heterogeneous risk attitudes, the fixed claim is not redundant: every interior equilibrium has debt outstanding. With one consumption date, prices are relative, so the claim can be priced at par (`q_B = 1`): it is a fixed repayment, with no time premium. The result is about the **shape** of the claim (fixed versus residual), which stage 350 separates from interest.

## Limits
- One date, two assets (output share and a claim paying one in every state), common beliefs, interior consumption.
- Existence of the incomplete-market equilibrium is **not** proved here; the result is a property of any interior equilibrium that exists.
- Only the direction is shown (debt is traded, someone issues, someone holds), not the size of positions. Which type issues (the less risk-averse, intuitively) is not proved.
- Marginal utility exactly `c^(−γ_i)` (log and power utility, up to the scale of the felicity's derivative); other HARA families are not covered.
