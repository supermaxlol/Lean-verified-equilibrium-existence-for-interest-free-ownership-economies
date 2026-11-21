# Stage 373: a unique two-period path with heterogeneous patience and `γ ≠ 1`

Lean 4.35 + Mathlib. 9 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/PathUniquenessHetero.lean`](../../formal/PathUniquenessHetero.lean).

Stage 370 proved uniqueness of the finite-horizon equilibrium path of stage 364 for log utility,
for common patience, and for horizon one. It left open heterogeneous patience with `γ ≠ 1` and
horizon above one, where the distribution path depends on returns and returns on the future
distribution. This file closes that case for horizon two under a band condition on `γ`. The
stage 364 definitions are restated unchanged (`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`).

* `I γ D q = 1 / q + 1 / (D q ^ (1 / γ))`: with stage 370's identity `qs_eq`, a household's
  saving rate times the return is `1 / I`. `I_lower`, `I_upper` compare `I` at two returns and
  two coefficients using only bounds on the powers `t` and `t ^ (1 / γ)` of the return ratio.
* `reduce`: a two-period equilibrium satisfies two clearing equations in the two returns
  `Q 0`, `Q 1` alone (`R1`: date 0; `R2`: date 1 with the date-1 distribution substituted).
* `reduced_unique`: the two equations have at most one positive solution whenever there are
  `lo, hi` with `0 < lo ≤ 1 ≤ hi`, `lo ≤ 1 / γ ≤ hi` and `(hi − lo)(hi + lo) < lo²`. Proof: if
  `Q 1 < Q' 1`, the date-0 equation bounds how far `Q 0` can fall; with that bound every date-1
  term at the primed returns exceeds the unprimed one by a factor above one, which contradicts
  date-1 clearing. Equal date-1 returns give equal date-0 returns by monotonicity.
* **`unique_two_period`**: for heterogeneous patience and horizon two, two equilibria with
  positive returns have the same returns and the same distributions at every date, under the
  band condition above, `g ≥ 0`, `amp ≥ 0` and `g σ c ≥ 0`.
* **`unique_two_period_band`**: the band condition holds whenever `1 / 2 < γ ^ 2 < 2`, so the
  two-period path is unique for `γ` between `1 / √2` and `√2` (log utility `γ = 1` included).

Limits: horizon two only. For horizon above two the same comparison has to be carried through
a chain of dates and is not done here; neither a contraction bound nor an induction on the
horizon is given. The band `1 / 2 < γ ^ 2 < 2` is a sufficient condition from crude bounds, not
a sharp one: for `γ` outside it uniqueness is neither proved nor refuted, and no example of two
distinct equilibrium paths is given. Uniqueness is among equilibria with positive returns at
dates 0 and 1. The infinite-horizon path is not covered.
