# Stage 311: The interest-free intermediation stack (capstone)

Lean 4.35 + Mathlib. 10 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
A lender advances `I` per member at zero markup. The pooled per-member shortfall after collateral is `X`. The buffer is
`B = κ − c·a + k + (1−h)·C`:
takaful contribution, minus verification cost (301/308), plus reserve capital (304/310), plus haircut-LOLR liquidity (305). The lender receives `I − max(X − B, 0)`.

## Results
- `receipts_le`, `receipts_full`: the lender never receives more than principal, and is paid in full whenever `X ≤ B`.
- `fail_le`: P(not paid in full) ≤ Var X / (B − E X)² (Chebyshev, proved in the file).
- `shortfall_le`: the lender's expected loss is ≤ Var X / (B − E X).
- `buffer_ps`: profit sharing audits with probability `a ≤ θ` (308), so sizing at `θ` is conservative.
- `stack`: if the θ-sized buffer exceeds the mean loss and the pool has variance `ρv + (1−ρ)v/N`, all four hold. The failure probability is ≤ `(ρv + (1−ρ)v/N)/(B_θ − μ)²` and the expected loss is ≤ `(ρv + (1−ρ)v/N)/(B_θ − μ)`.
- `stack_limit`: as N → ∞ the bounds fall to the correlated floor `ρv/d`.
- `stack_sizing`: failure ≤ α once Var ≤ α(B − E X)².

## Reading
A zero-markup lender is made whole in expectation, up to an explicit and shrinking bound, by non-interest components alone: contributions, verification, reserves, and haircut central-bank liquidity.

## Honest limits
- Chebyshev bounds only.
- Buffer components are given numbers, not financed inside the model.
- The shortfall `X` is exogenous.
- The stack composes the earlier stages at the level of their conclusions (as parameters); it does not re-derive them inside one model.
