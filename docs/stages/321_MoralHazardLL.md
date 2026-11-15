# Stage 321: Moral hazard under limited liability, debt versus profit sharing

Lean 4.35 + Mathlib. 10 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/MoralHazardLL.lean`. Extends stage 309.

## Results
* `rent_lower`, `pledgeable_bound`: under limited liability, any incentive-compatible contract leaves the borrower an expected rent of at least κ. So no contract finances a project unless I ≤ E_H[y] − κ.
* `share_ic_iff`, `share_breakeven`: the profit share θ = I/E_H[y] breaks even and keeps the borrower working iff κ ≤ (1 − θ) Σ(πH − πL)y.
* Binary output (`tt_ic_iff`, `tt_feasible_iff`, `tt_min_rent`, `tt_share_equiv`):
  - financing exists iff I ≤ pH(Y − κ/(pH − pL));
  - the minimum agency rent is pH κ/(pH − pL);
  - every limited-liability debt contract pays exactly what a profit share pays.
  So with two outcomes, banning debt costs nothing.
* `debt_beats_share`: a three-outcome example with an increasing likelihood ratio, where debt (face 1) and the profit share 3/7 both give the lender 9/10. At effort cost 1/2, debt keeps the borrower working and the profit share does not.

## Honest reading
The example runs against the interest-free position. With more than two outcomes, moral hazard can make debt strictly better (Innes 1990). Stage 309's equivalence depends on binary output.

## Honest limits
Risk neutrality and one effort level. The optimal contract for general finite outcomes (Innes's live-or-die result) is not derived. Only the general bound and the counterexample are proved.
