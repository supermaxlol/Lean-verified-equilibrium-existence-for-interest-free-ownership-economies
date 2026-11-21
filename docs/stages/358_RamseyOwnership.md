# Stage 358: the Ramsey rule is paid by ownership, not by a loan

Lean 4.35 + Mathlib. 10 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/RamseyOwnership.lean`](../../formal/RamseyOwnership.lean).

The Euler (Ramsey) condition for consumption, `u'(C_t) = β R u'(C_{t+1})`, says that waiting
must earn the gross real return `R`. It is often read as proving that *interest* must be
positive. This file shows the required return is delivered in full by ownership of output.

* `ramsey_log`: with `u = log` and consumption growing by `1 + g`, the Euler condition holds
  exactly when `R = (1 + g) / β`.
* `ramsey_crra`: with marginal utility `c ^ (-γ)`, exactly when `R = (1 + g) ^ γ / β`.
* `ramsey_example`: `β = 0.96`, `g = 0.05`: `R = 1.09375` (a 9.375% real return).
* `ownership_clearing`: in a growing ownership economy where households consume `1 − β` of
  wealth and all output `D_t` is paid as dividends, the units market clears at value
  `Q_t = β D_t / (1 − β)`.
* `ownership_pays_ramsey`: the gross return on ownership, `(Q_{t+1} + D_{t+1}) / Q_t`, is then
  `(1 + g) / β`: exactly the Ramsey return for log utility. No lending contract is involved.
* `ownership_real`: a common change in the price level leaves the real return on ownership
  unchanged, because units are claims on output.
* `fisher_real`: a fixed nominal claim earns the real gross return `(1 + i) / (1 + π)`.
* `fisher_example_deflation`: `r = 5%`, `π = −3%` gives nominal `1 + i = 1.0185`.
* `hyperinflation_example`: `i = 50%`, `π = 500%` gives a real return of `0.25` on a nominal
  claim, while ownership still pays the Ramsey return.
* `cash_dominated`: whenever a nominal claim's real return is below the ownership return, a
  saver strictly gains by holding ownership instead.

Reading: impatience and diminishing marginal utility give waiting a positive time value. That
value is a return on ownership; it does not require an interest-bearing loan, and a claim on
output keeps it under inflation, where a nominal claim loses it.
