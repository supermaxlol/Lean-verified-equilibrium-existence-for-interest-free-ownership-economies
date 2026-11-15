# Stage 314: Stiglitz–Weiss screening without interest

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Types share mean output μ and differ in risk.

Debt at face R:
- `debt_borrower_ge`: every type's payoff ≥ the safe type's `max(μ−R,0)`.
- `debt_lender_le`: the lender's repayment ≤ the safe type's `min(μ,R)`.
- `safe_exits_first`: if the safe type borrows at R, so does every riskier type.
- `sw_example`: raising R from 0.9 to 1.0 drives out the safe type and lowers the lender's return from 0.675 to 0.5. This is credit rationing; the rate cannot clear the market.

Profit sharing at θ:
- `ps_payoff`: each type gets (1−θ)μ and the lender gets θμ.
- `ps_no_selection`: participation is identical across risk types.
- `ps_pool_return`, `ps_pool_mono`: the lender's pooled return is exactly θμ for any mix and is increasing in θ.

The Stiglitz–Weiss adverse-selection channel is absent.

Honest limits:
- Selection on risk only, with equal means.
- Profit sharing does select on the mean (high-mean types prefer debt).
- It needs verification (301/308/313).
