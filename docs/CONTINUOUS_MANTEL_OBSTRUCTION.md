# Continuous Mantel/Debreu on S_ε: where the formal construction stops

Draft, 2026-11-15. This is a status note, not a result. **The continuous case is not proved in this programme.**

## The target

Let `Z` be continuous on `S_ε`, the unit prices whose coordinates are all at least `ε`, and satisfy Walras' law. The goal is to write `Z` on `S_ε` as the sum of `n` demand functions. Each demand must maximise a continuous, concave, strictly monotone utility, and ideally that maximiser should be unique.

Debreu (1974) uses one consumer per good. Consumer `k` trades

    x^k(p) = α_k(p) · (e_k − p_k p),

where `α_k(p) = Z_k(p) + A p_k`, with `A` large enough that `α_k > 0`.

## What is formally proved (stages 296–337)

- **Finitely many prices** (stages 296, 323, 326, 329, 332–333):
  - any excess-demand data is a sum of unique utility maximisers;
  - with explicit endowment bounds (`Mbd p Z`), the given `Z` itself is reached, with no rescaling.
- **A continuum with constant weight** (stage 330; uniqueness in stage 331): `c · (e_k − p_k p)` is the unique demand of a continuous, concave, strictly monotone utility on all of `P ⊆ S_ε`.
- **A continuum with varying weight** (stage 334):
  - a weight that is relatively Lipschitz with a small constant (`|w p − w q| ≤ κ w q ‖p − q‖`, `4κ ≤ ε`) is rationalised on the continuum, without uniqueness;
  - where weights jump between touching pieces, unique demand is impossible;
  - revealed preference does not depend on the weights at all: the sign of `q·x(p)` is the sign of `q_k − p_k (q·p)`, and WARP holds for every positive weight function (`debreu_warp`).
- **Uniqueness for slowly varying weights** (stage 335): under the stage-334 condition, and if `P` contains short great-circle arcs around each of its points ("rich", e.g. any open subset of `S_ε`), the trade is the **unique** maximiser. Boundary prices of a closed `P` are not covered.
- **The weight `p_k` reduced to one variable** (stage 336): if `F, L` satisfy
  `F b − F a ≤ L a · b · (a − b (a b + √((1 − a²)(1 − b²))))` on `[ε, β]`, then `V q = F(q_k)`, `λ q = L(q_k)` are Afriat numbers. The weight-`p_k` consumer is then rationalised on the continuum (`weight_pk_rationalised`).
- **Finite case, consumer-specific floors** (stage 337): the uniform endowment floor of stage 333 is replaced by the exact floor `e_i ≥ −mx_i(p_k)`. The remaining gap to the necessary aggregate floor is `∑_i max_k` versus `max_k ∑_i`, and it belongs to the Debreu decomposition.

## Where it stops

1. **The issue is quantitative.** Revealed preference cannot see the weights, so no GARP violation can block the construction, on finite samples or on the continuum. A numerical check confirms this: 300 random prices in `S_0.2`, several weight shapes (`p_k`, `1/p_k`, `exp(3 p_1)`, …), zero GARP violations. By Afriat's theorem, every finite subset therefore has Afriat numbers. What is missing is a choice of those numbers, `V` and `λ`, that is **bounded uniformly** over the continuum. The stage-330 construction needs `λ ∈ [ε, Λ]` and a uniform Lipschitz bound, so that the infimum is finite and continuous.

2. **The obvious choice fails for Debreu's weights.** Stage 334 uses `V q = −q_k` and `λ q = 1/w q`. This needs a relative Lipschitz constant `κ ≤ ε/4`. Debreu's `α_k = Z_k + A p_k` has a relative Lipschitz constant of order `1/p_k ≥ 1`, and the `A p_k` term alone already gives that. Making `A` larger does not help: the ratio tends to `1/p_k`, not to zero.

3. **Uniqueness has a further, genuine obstruction.** `limit_optimal` shows that under any continuous utility, limits of optimal trades are optimal. So a demand with a jump cannot be the unique maximiser at the jump. That does not affect Debreu's continuous `α_k`, but it rules out piecewise or approximate shortcuts if unique demand is required.

4. **The classical theorem is weaker in the relevant sense.** Debreu (1974) obtains continuous, monotone, strictly convex *preferences*. He does not obtain a *concave utility*. The Afriat route formalised here produces concave utilities, which is a stronger conclusion. Some continuous, strictly convex preferences have no concave representation, so the formal target here may be strictly harder than the classical statement. This is unverified for Debreu's specific consumers.

## The weight `w(p) = p_k` (attempted 2026-11-15)

- **Reduction (proved, stage 336).** Take `V` and `λ` depending only on `q_k`. Cauchy–Schwarz on the other coordinates turns the `n`-dimensional Afriat inequalities into the one-variable inequality above. For `n = 2` the reduction loses nothing. The symmetric choice also loses nothing on rotation-invariant caps, because the constraints are convex and rotation-invariant (argued, not formalised).
- **Necessary condition** (from the first-order expansion): writing `q_k = cos α`, `L/(sin α cos α)` must be nonincreasing in `α`. This rules out `L` constant, `L = 1/w`, and similar simple choices.
- **Numerical evidence (not a proof).** Grid checks with 2000–3000 points on `[ε, √(1 − ε²)]`, plus Floyd–Warshall feasibility on 300 points, support one family:
  - `L a = a √(1 − a²) e^{−K arccos a}`, with `F' = −a L`, satisfies the inequality with positive relative slack;
  - the thresholds are `K ≳ 5` at `ε = 0.3`, `K ≳ 10` at `ε = 0.1`, and `K ≳ 20` at `ε = 0.05`;
  - power families `a^{M+1} √(1 − a²)` fail at `ε = 0.05` for every `M ≤ 64`.

  So, numerically, the pure `A p_k` weight **is** rationalisable on `S_ε` with uniformly bounded Afriat numbers. The bounds degrade as `ε → 0`, with `ℓ ≈ e^{−Kπ/2}`. This corrects the impression in point 2 above: the obvious choice fails, but a less obvious one appears to work.
- **Not done:** a Lean proof of the one-variable inequality for this family. It is an explicit trigonometric inequality, and the slack near `a = b` is second order, which makes it fiddly. The weight `Z_k + A p_k` is also not done. The Debreu consumers are not done jointly either: each consumer is rationalised separately, which is all Mantel needs, but their weights are not of the pure `p_k` form.

## The quasi-concave route (item 4, assessed 2026-11-15, not formalised)

Debreu's own route gives preferences, not concave utilities. One formal shortcut was examined:
- Budgets here are cones `{z | p·z ≤ 0}`. The direction of `d(p) = e_k − p_k p` determines `p` (for `p_k < 1`).
- So a positive weight `w` defines a degree-0 function `ψ` on those directions with `ψ(dir d(p)) = w(p)`.
- Composing the constant-weight utility `u₁` (stage 331, unique demand `d(p)`) with the radial map `z ↦ z/ψ(dir z)` gives a continuous utility whose unique maximiser on `C_p` is `w(p) d(p)`.

This, however, does not preserve monotonicity or quasi-concavity in general. Without those, rationalisation by "some continuous utility" is close to trivial. So the shortcut does not deliver Debreu's conclusion. A genuine formalisation would need Debreu's construction of convex indifference surfaces: a substantial, separate project, not started.

## Candidate next steps

- Prove the one-variable inequality of stage 336 for `L a = a √(1 − a²) e^{−K arccos a}` with explicit `K(ε)`. That would settle the pure `A p_k` weight.
- Extend the reduction to weights `φ(q_k) + (bounded, small Lipschitz) perturbation`. This would combine stages 334 and 336, and Debreu's `Z_k + A p_k` has this shape after dividing by `A`.
- Approximate: prove the result on finer and finer finite grids with explicit error bounds, and pass to a limit only for the aggregate (`Z` exactly), not for each individual consumer's utility.

## Honest summary

Finite Mantel: proved. Continuum with constant weights: proved, with unique demand. Continuum with slowly varying weights: proved, with uniqueness at relatively interior prices (335). Weight `p_k`: reduced to a one-variable inequality (336) that numerics support, not proved. Continuous Mantel/Debreu on `S_ε` with Debreu's weights: **open here**. The gap is a uniform bound on Afriat numbers, not a failure of revealed preference.

## Update, stages 338–355 (2026-11-15, later the same day)

Several of the open points above are now closed. The sections above are kept as written, as a record of the state before these stages.

- **The one-variable inequality is proved** (stage 339), with an explicit constant (`K σ ≥ 14` in the margin form). Explicit Afriat numbers for the weight `p_k` follow (344). Demand is unique on rich price sets (347) and up to the boundary of a closed cap (348). Boundary prices for slowly varying weights are resolved (341, 345).
- **The weight `A p_k + Z_k`** satisfies the Afriat inequalities with a quantitative margin (346). The assembly is done (353): if `Z` is bounded and Lipschitz on the cap, then for `A` large each Debreu trade maximises a continuous, concave, strictly monotone utility, and `Z = Σ_k x^k` by Debreu's decomposition. This is **continuous Mantel for Lipschitz excess demand on `S_ε`**, with concave utilities. Uniqueness for this weight is not proved.
- **Single-price endowment floors** (338, 340): the exact floor is necessary, and Debreu's own decomposition overshoots it.
- **Grid route** (343, 349): optimal trades are stable under locally uniform limits, and Arzelà–Ascoli compactness gives a limit utility that rationalises the trades at every price. Both **assume** a uniform Lipschitz bound.
- **That bound cannot come from approximation** (355). A pointwise limit of `L`-Lipschitz functions is `L`-Lipschitz. So a merely continuous `Z` (for example, one behaving like `√` near a point) has no Lipschitz approximants with bounded constants. Along any approximation, the stage-353 scale `A_m → ∞` and the Afriat multiplier bound tends to `0`.

**Revised honest summary.** Finite Mantel: proved. Lipschitz excess demand on `S_ε`: proved, with concave utilities, without uniqueness. Continuous but non-Lipschitz excess demand: **open**. The uniform-Lipschitz and grid route to it is closed (355). A different construction is needed, for example Afriat numbers driven by a modulus of continuity, or Debreu's preference-based construction. Point 2 above (a ratio of order `1/p_k`) was superseded by stage 339's family; the obstacle is now regularity of `Z`, not the shape of the weight.
