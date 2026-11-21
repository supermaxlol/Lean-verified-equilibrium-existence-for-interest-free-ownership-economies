# Stage 368: long-run distributions under threshold (discontinuous) access

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ThresholdRest.lean`](../../formal/ThresholdRest.lean).

Stage 365 proved that a long-run distribution exists when saving and access rules are
continuous in the distribution, using Brouwer's theorem. All-or-nothing access rules (a
household gets new units pro rata only once its share reaches a threshold `θb`, stage 356) are
discontinuous, so that argument does not apply. This file treats them with an order argument
instead of a topological one, for two households.

Setup (stage 365, two households): household 1 holds the share `x`, household 2 holds `1 − x`.
Saving rates `s1, s2 > 0` are fixed, so household 1's share of saved ownership is
`p x = s1 x / (s1 x + s2 (1 − x))`. New units are issued at rate `g ≥ 0`: a fraction `σ ∈ [0, 1]`
equally (`1/2` each), the rest pro rata to saved ownership weighted by an access intensity
`a` read off the household's own current share. Household 1's next share is
`F x = (p x + g (σ / 2 + (1 − σ) U x / (U x + V x))) / (1 + g)` with `U x = a x · p x` and
`V x = a (1 − x) · (1 − p x)` (`F2` is household 2's share; `F_add_F2`: they sum to one).

* `fixed_greatest`, `fixed_least`: any nondecreasing self-map of `[0, 1]`, continuous or not,
  has a greatest and a least fixed point (Knaster–Tarski, proved directly with suprema).
* `F_mono`: if `a` is nondecreasing and non-negative on `[0, 1]` (it may jump), `F` is
  nondecreasing.
* **`exists_rest_monotone`**: under those conditions, and as long as some saved ownership has
  access (`U x + V x > 0`), a long-run distribution exists; there is a least and a greatest one
  and every other lies between them. `rest_floor`: in every long-run distribution each household
  holds at least `g σ / (2 (1 + g))`.
* **`exists_rest_threshold`**: the threshold rule `thr θb α0` (full access at a share of at least
  `θb`, intensity `α0 ∈ (0, 1]` below it) has a long-run distribution for any saving rates.
* **`exists_rest_all_or_nothing`**: the strict all-or-nothing rule (`α0 = 0`, no pro-rata units
  at all below the threshold) with equal saving rates and `θb ≤ 1/2`.
* **A poverty trap** (`two_rest_threshold`): with `g = 1`, `σ = 1/2`, equal saving, threshold
  `1/2` and intensity `2/5` below it, the shares `1/3`, `1/2` and `2/3` are all long-run
  distributions. At `1/3` household 1 stays below the threshold for ever, though the equal
  distribution is also a rest point.

Limits: two households only; saving rates do not depend on wealth (wealth-dependent patience is
covered, for continuous rules, by stage 365); the access intensity depends on the household's own
share and must be nondecreasing in it. Existence only: which rest point is reached, and whether
the iteration converges to one, is not proved (for a discontinuous map the limit of the
iteration need not be a rest point). The many-household case is not covered: there the update is
not monotone in any obvious order, and the argument does not extend directly.
