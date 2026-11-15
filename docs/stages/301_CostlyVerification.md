# Stage 301: Costly state verification and interest-free debt

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
A borrower needs `I` from a lender. Output `y s ≥ 0` depends on a finite state `s` that only the
borrower sees. The lender can verify the state at cost `c ≥ 0`. A contract is a payment `r s` as
a function of the reported state and a set `V` of reports that trigger verification. Lies caught by
verification are punished. Limited liability: `0 ≤ r s ≤ y s`. The lender's outside option is
cash (zero return), so there is no time premium: it needs expected receipts net of expected
verification cost of at least `I`.

## Results
- `ic_debt_form`: truth-telling forces the debt shape. The payment is one number `D` on every unverified state, never above `D` anywhere, and every state with output below `D` must be verified.
- `debt_ic`, `debt_dominates`, `lnet_mono`, `townsend`: standard debt `min (y, D)`, verified exactly on default, is truth-telling, pays the lender at least as much in every state and verifies on a subset of states. It dominates every truth-telling contract with some unverified state (Townsend 1979, Gale–Hellwig 1985, finite-state version).
- `full_audit_dominated`: profit sharing with an audit in every state is dominated by debt.
- `interest_free_bound`: if no payment exceeds the principal (`r ≤ I`), the lender gets at most `I`, and breaks even only if every positive-probability state pays exactly `I` (so output is at least `I` there) and expected verification cost is zero.
- `markup_needed`: with any positive-probability state where output is below `I`, a break-even debt face must be strictly above `I`.
- `riskless_qard`: if output covers `I` on the support, debt at face `I` breaks even with no verification.
- `collateral_qard`, `collateral_necessary`: with collateral `K`, interest-free debt at face `I` is truth-telling and breaks even if and only if `y + K ≥ I` on the support.

## Reading
This is the "separate interest from debt" question in its standard model. Two things come out.

1. The debt *shape* (a fixed payment, verification only on default) is the efficient answer to costly checking. That job of debt is real and survives without interest: the shape does not need a face above the principal.
2. The *markup* is not a price of time here, because the lender's outside option earns nothing. It is a premium for default losses and verification costs. With any risk of default, a face equal to the principal loses the lender money. Interest-free lending to a risky borrower is self-financing only when collateral (or output itself) covers the principal in every state.

So qard (interest-free loan) works exactly for covered lending: collateralised loans, liquidity to solvent institutions against good collateral, bridging riskless receivables. Risky lending at face `I` needs a subsidy (charity, a public guarantee, takaful pooling) or a contract that pays above `I` in good states. Whether a default premium paid only in non-default states is permissible is a question for scholars; the theorem only says what each choice costs.

## Limits
- Deterministic verification only. Random audits (Mookherjee–Png 1989) can beat debt and are not covered.
- One period, risk-neutral lender, finite states.
- Dominance is stated for the lender's payoff and the verification set. That the face can then be lowered to hand surplus back to the borrower needs a continuity step not formalised here.
- The lender's outside option is cash. If the outside option is an ownership claim with positive expected return, the break-even target rises above `I`; the same proofs apply with `I` replaced by that target, but the "no time premium" reading then needs care.
- No pooling across borrowers. Diversification (many independent borrowers) can lower the required premium but not to zero when defaults are correlated.
