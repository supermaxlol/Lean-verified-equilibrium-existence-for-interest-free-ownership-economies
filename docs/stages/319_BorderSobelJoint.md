# Stage 319: The Border–Sobel program with repayments chosen

Lean 4.35 + Mathlib. 13 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/BorderSobelJoint.lean`. Extends stage 315.

## Results
* `reduce`: in any feasible scheme (repayments ≤ output, truth-telling, lender breaks even after audit cost), the audits can be replaced by stage 315's `astar` at no higher cost. The joint problem reduces to choosing R alone.
* `astar_zero_iff`: a repayment schedule needs no audits iff it is flat.
* `audit_free_iff`: an audit-free feasible scheme exists iff every state's output covers the principal I. Otherwise every feasible scheme has positive expected audit cost.
* `two_state_lower`, `two_state_optimum`: with two states the optimum is solved in closed form:
  - the bottom state repays all its output;
  - the top report is never audited;
  - the bottom report is audited with probability a* = (I − yL)/(pH(yH − yL) − c·pL) ≤ 1;
  - no feasible scheme has lower expected audit cost.
* The audit-rule lemmas are restated from stage 315: `g_nonneg`, `g_le_one`, `pair_iff`, `astar_nonneg`, `astar_le_one`, `ic_iff`, `astar_ic`, `top_no_audit`.

## Honest limits
The closed form covers two states. For general finite S, Border–Sobel's theorem that the optimal repayment rises with output is **not** proved, and neither is existence of an optimum. Maximal penalty and audit commitment are assumed.
