# Stage 282 — Heterogeneous risk attitudes: shifted linear sharing

Lean 4.35 + Mathlib. 5 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: finite states, common beliefs, aggregate output `Y s > 0`. Households differ in a shift `a` of a common-slope (HARA-type) felicity whose marginal utility depends on `y + a`.

- `hara_optimal`: at prices `π s * M (Y s + A)`, the bundle "share `w` of `Y + A` less the shift `a`" is optimal.
- `hara_clears`: these bundles use exactly output.
- `linear_rule`: such a bundle is a share of output plus a state-independent payment, `w * (y + A) - a = w * y + (w * A - a)`.
- `side_payments_cancel`: the payments sum to zero across households.
- `ownership_fails_heterogeneous`: if marginal utilities are `y ^ a` and `y ^ b` and both households optimally hold pure shares at common prices, and output differs between two states, then `a = b`.

Reading: pure constant-share ownership is the equilibrium only with a common risk attitude. With heterogeneous shifts, the efficient arrangement is still a share of output plus riskless transfers that net to zero.

Limits: the full Wilson (1968) converse, that linear sharing is efficient only within the common-slope class, is not proved. The failure result covers power utilities with different exponents, not arbitrary preferences.
