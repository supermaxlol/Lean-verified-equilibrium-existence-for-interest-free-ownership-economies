# Stage 359: control and inheritance under issuance rules

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ControlInheritance.lean`](../../formal/ControlInheritance.lean).

Voting weight equals ownership share. New units are issued at rate `g`, a fraction `σ` equally
(`c` per household) and the rest pro rata (`next`, stages 253 and 263, common patience).

* `coalition_next`: a coalition's total share follows the same rule as one household, with the
  equal share `|S| c`.
* `coalition_dev`: its share after `n` periods is `|S| c + rate ^ n (s0 − |S| c)`.
* `majority_dissolves`: if the coalition is less than half the population (`|S| c < 1/2`) and
  `σ > 0`, its majority is eventually lost, whatever its starting share.
* `majority_gone_at`: an explicit test: once `rate ^ n (s0 − |S| c) < 1/2 − |S| c`, the
  coalition is below one half.
* `pro_rata_majority_persists`: with `σ = 0`, a majority, once held, is held forever.
* `estate_split`: dividing an estate among heirs by weights summing to one preserves the
  dynasty's share.
* `dynasty_converges`: under equal issuance a dynasty's share tends to `m c`, where `m` is its
  number of members: per-household issuance tracks headcount, not inheritance.

Reading: under pro rata issuance control is permanent; any positive equal-issuance fraction
dissolves every minority's majority in finite time.
