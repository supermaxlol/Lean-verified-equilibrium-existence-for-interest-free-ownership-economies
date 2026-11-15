# Stage 327: Innes's theorem: debt is optimal under MLRP

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
There are finitely many states `Ω`. Low effort puts weight `πL ≥ 0` on each state; high effort puts weight `l·πL`, with likelihood ratio `l > 0`. Output is `y`. A contract `R` has limited liability (`R ≤ y`) and is monotone (`y ω ≤ y ω' → R ω ≤ R ω'`). MLRP means `y ω ≤ y ω' → l ω ≤ l ω'`.

## Results
- `single_crossing`: suppose a difference `Δ` is negative only where `l` is low and positive only where `l` is high, and has zero high-effort mean. Then its low-effort mean is nonpositive. The proof uses a threshold `t` (a maximum of `l` over the negative set) and the identity `∑ πL (l - t) Δ = -t ∑ πL Δ`.
- `innes`: under MLRP, among monotone limited-liability contracts with the same high-effort expected repayment, debt `min(y, D)` has the largest low-effort expected repayment.
- `innes_ic`: if a monotone limited-liability contract satisfies the entrepreneur's effort constraint, so does debt with the same high-effort repayment.
- `debt_exists`: every repayment between `0` and full equity is achieved by some face value `D ≥ 0`, by the intermediate value theorem.
- `debt_optimal`: for every nonnegative, monotone, limited-liability contract there is a debt contract with the same high-effort expected repayment and a weakly larger low-effort expected repayment.

## Reading
This is Innes (1990, JET). Debt loads repayment onto low-output states, which MLRP makes relatively likelier under shirking. So debt punishes shirking most for a given investor stake. The face value `D` is only the level that makes the investor's expected repayment equal the stake. No time premium is involved. The result is about the shape of the claim (fixed claim, limited liability, monotone), which an interest-free fixed-claim contract shares. It is not an argument for interest.

## Limits
- Finitely many states and two effort levels. The continuous-effort version (first-order approach) is not formalized.
- Monotonicity of `R` is assumed, as in Innes. Without it, live-or-die contracts do better, and that case is not covered.
- Optimality is weak (`≤`). Strictness is not claimed.
