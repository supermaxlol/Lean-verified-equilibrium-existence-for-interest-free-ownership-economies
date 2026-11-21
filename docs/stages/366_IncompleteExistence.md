# Stage 366: existence of the equity-and-bond equilibrium with heterogeneous CRRA

Lean 4.35 + Mathlib. 11 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/IncompleteExistence.lean`](../../formal/IncompleteExistence.lean).

Stage 354 showed that in any equilibrium of the one-date economy with a share of output `Y` and
a bond paying one in every state, households with different CRRA coefficients trade the bond.
It did not prove that an equilibrium exists. This file proves it.

Setup: states `s` with probabilities `π s > 0` and output `Y s > 0`, not all equal (`lo` and `hi`
are a lowest and a highest state). Household `i` starts with `w i > 0` units of the equity (equity
price normalised to one), has marginal utility `c ^ (−γ i)` with `γ i > 0` (log and every power
utility), and chooses equity `θ` and bonds `b` at bond price `1 / R`, with `θ + b / R = w i`.
Consumption is `θ Y s + b = R w + θ (Y s − R)` (`cons`).

* `g_anti`: the Euler expression `g = Σ π c ^ (−γ) (Y − R)` is strictly decreasing in `θ` on the
  affordable set, for `Y lo < R < Y hi`.
* `exists_zero`: it has a zero, found by the intermediate value theorem between two explicit
  portfolios at which one state's consumption is pushed close to zero (`small_delta`).
* `optimal`: that zero maximises expected utility over every affordable portfolio (mean value
  theorem); so each household has a unique optimal portfolio `dem R`.
* `dem_continuous`: `dem` is continuous in `R` (sign persistence).
* `w_le_dem`, `dem_le_w`: at `R` below household `i`'s tilted mean
  `m i = E[Y ^ (1 − γ i)] / E[Y ^ (−γ i)]` it holds at least its endowment of equity, above it at
  most (`tilted_mem`: each `m i` lies strictly between `Y lo` and `Y hi`).
* **`exists_equilibrium`**: there are a bond return `R` with `Y lo < R < Y hi`, and portfolios
  `(θ i, b i)` such that each household's portfolio is affordable, gives positive consumption
  and is optimal among all affordable portfolios with positive consumption, and both markets
  clear: `Σ θ i = Σ w i` and `Σ b i = 0`. The aggregate excess demand for equity changes sign
  between the smallest and the largest tilted mean, and the intermediate value theorem gives
  the clearing return.

Reading: together with stage 354, the economy with equity and a fixed claim has an equilibrium,
and in it the fixed claim is traded whenever risk attitudes differ.

Limits: one date, two assets, common beliefs, utilities with marginal utility exactly
`c ^ (−γ)` (CRRA); positive endowments of equity only. Uniqueness of the equilibrium is not
proved. More assets, more dates, and general (non-CRRA) preferences are not covered.
