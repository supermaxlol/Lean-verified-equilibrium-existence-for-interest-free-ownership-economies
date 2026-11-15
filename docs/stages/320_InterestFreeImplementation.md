# Stage 320: Every Arrow–Debreu equilibrium can be traded with interest-free contracts

Lean 4.35 + Mathlib. 14 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.
File: `formal/InterestFreeImplementation.lean`. Capstone linking the contract stages to the existence program.

## Results
* `cost_eq`: a portfolio costs exactly the state-price value of its payoff.
* `budget_eq`: with spanning contracts, the contract budget set equals the Arrow–Debreu budget set.
* `implement`: every Arrow–Debreu equilibrium is a contract-market equilibrium:
  - each household reaches its equilibrium bundle with a portfolio that is optimal among all affordable portfolios;
  - with linearly independent payoffs, every contract market clears.
* `debt_redundant`, `debt_adds_nothing`: a fixed debt claim is replicated by the spanning contracts, so allowing debt does not enlarge any budget set.
* `arrow_spans`, `arrow_indep`, `arrow_nonneg`: state-contingent claims with no fixed obligation span and are independent.
* `spans_of_indep`: as many ownership claims as states with linearly independent payoffs span. Shares in firms with linearly independent outputs are enough.

## Link to the existence program
Stage 261 proves an Arrow–Debreu equilibrium exists. This stage proves any such equilibrium can be traded with interest-free contracts alone. The link is between the two theorem statements; the files are not joined by one Lean import.

## Honest limits
One period, complete spanning, frictionless contracts. With costly verification (stages 301, 315, 319) or moral hazard (stage 309), banning debt is no longer costless, and those stages measure the cost. State prices still embed time preference. The claim is that no contract carries a fixed premium, not that consumption is undiscounted.
