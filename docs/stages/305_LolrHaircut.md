# Stage 305: An interest-free lender of last resort: haircut in place of penalty rate

Lean 4.35 + Mathlib. 4 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
A bank pledges collateral worth `V0` today, which will be worth `V s` in state `s` at repayment. The central bank lends `(1 − h) V0` at zero interest and recovers `min(V s, loan)`. To raise cash `X`:
- in the market, it pays `m X` (a fire-sale discount, or a profit share given up);
- at the central bank, it ties up `X / (1 − h)` of collateral with shadow cost `λ` per unit.

## Results
- `safe_zero_loss`: if the haircut covers the worst collateral drop on the support (`V s ≥ (1 − d) V0`, `h ≥ d`), the central bank's expected loss is zero.
- `loss_antitone`: a larger haircut never raises the expected loss.
- `market_iff`: the bank strictly prefers the market iff `m < λ / (1 − h)`.
- `lolr_design`: if the normal-time market cost `m0` is below the stress-time cost `m1`, and the safe haircut is not too punitive (`λ / (1 − d) < m1`), then some haircut `h ≥ d` achieves all three at once:
  - the central bank is safe;
  - banks use the market in normal times (`m0 < λ / (1 − h)`);
  - banks come to the central bank under stress (`λ / (1 − h) < m1`).

## Reading
Bagehot's rule ("lend freely, at a penalty rate, against good collateral") uses the penalty rate to screen: it keeps banks in the market when markets work. This stage shows a haircut does the same screening job with zero interest, by making central-bank liquidity costlier per unit of collateral than normal market funding. The haircut also protects the central bank directly. This is the formal version of "interest-free debt for bailouts and liquidity".

The design has a tension: a safe haircut must be large, while a usable facility needs a haircut that is not too large. It works exactly when `λ / (1 − d) < m1`. If collateral is so risky that the safe haircut makes the facility costlier than fire-selling even in a crisis, no interest-free haircut design works, and with no haircut the central bank bears the loss.

## Limits
- Solvency is not modelled. The theorem protects the central bank through collateral; it does not separate solvent from insolvent banks beyond that.
- The encumbrance cost `λ` and market costs `m0`, `m1` are given constants, not derived.
- One period, one bank, no general-equilibrium feedback from central-bank lending to collateral prices.
