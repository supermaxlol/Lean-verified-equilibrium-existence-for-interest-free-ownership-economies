# Stage 303: The price of profit sharing under costly verification

Lean 4.35 + Mathlib. 15 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
The stage 301 model is unchanged: finite states, output `y s ≥ 0` seen only by the borrower, verification at cost `c`, truth-telling and limited liability. Stage 301's eleven results are re-proved in this file. The new results are listed below.

## Results
- `surplus_split`: the lender's net receipts plus the borrower's expected residual equal total surplus `E[y] − c · P(verify)`. The contract only divides the surplus. Verification is the only thing that destroys it.
- `surplus_gap`: debt with face `D` (verify on default only) has `c · P(y ≥ D)` more surplus than any contract that verifies every state. That is the exact cost of auditing in non-default states.
- `profit_share_audits`: a truthful profit-share contract (payment `θ y`, `θ > 0`) with any unverified state must leave unverified only states with the top output level, and must verify every state with lower output.
- `profit_share_audit_prob`: so its verification probability is at least `P(y < top output)`.

## Reading
Profit sharing (mudaraba/musharaka) and interest-free debt both avoid a time premium. Under costly verification they differ in how often outcomes must be checked:
- debt checks only on default;
- profit sharing checks almost always.

The difference is a real resource cost, `c · P(no default)` per contract against full audit. It goes to zero only when verification is cheap (`c → 0`), for example with audited accounts, on-chain revenue or third-party reporting. So the case for equity-style finance over interest-free debt is strongest exactly where verification technology is cheap.

## Limits
- Same as stage 301: deterministic audits, one period, risk-neutral, finite states.
- Profit sharing is modelled as a linear share `θ y`. Non-linear sharing rules are covered by the general truth-telling result `ic_debt_form` but not stated separately.
- No moral hazard in effort. Debt and equity also differ in effort incentives, which this model leaves out.
