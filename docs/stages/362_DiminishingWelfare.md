# Stage 362: diminishing marginal utility — why the distribution of ownership matters

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/DiminishingWelfare.lean`](../../formal/DiminishingWelfare.lean).

Stage 250 shows that consumption shares equal ownership (wealth) shares, so with total
consumption `C` household `h` consumes `x h * C`. Let every household have the same felicity
`u`, strictly concave on `[0, ∞)`: marginal utility diminishes. Utilitarian welfare is
`welfare u C x = ∑ h, u (x h * C)`.

* `pigou_dalton`: moving `t` from a richer household (`b`) to a poorer one (`a`) without
  reversing their order (`0 < t < b − a`) strictly raises `u a + u b`. Same output, more welfare.
* `equal_maximises`: for any shares summing to one, `welfare ≤ N u (C / N)`: equal ownership
  gives the most welfare from a given output (Jensen).
* `concentrated_worse`: with `N ≥ 2` and `C > 0`, the fully concentrated outcome
  `u C + (N − 1) u 0` is strictly below the equal outcome `N u (C / N)`.
* `concentration_limit`: if one household's share tends to one and every other share tends to
  zero (stage 356, pro rata issuance under different patience), welfare tends to
  `u C + (N − 1) u 0`, hence eventually stays strictly below equal welfare.
* `floor_welfare`: if `u` is monotone and every share is at least `f` (stage 356, equal
  issuance), welfare is at least `N u (f C)`.

Reading: with diminishing marginal utility the same economy yields more total satisfaction the
more evenly ownership is spread. Pro rata issuance drives welfare toward its concentrated value;
an equal-issuance floor keeps it above an explicit bound. Output is held fixed throughout, so
this is a statement about distribution, not about growth.
