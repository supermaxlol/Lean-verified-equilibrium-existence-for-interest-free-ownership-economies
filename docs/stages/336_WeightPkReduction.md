# Stage 336: the weight `w q = q_k` reduces to a one-variable inequality

Lean 4.35 + Mathlib. 19 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Results
- `cs_bound`: for unit `p, q`, `q·p ≤ q_k p_k + √((1 − q_k²)(1 − p_k²))`. This is Cauchy–Schwarz on the other coordinates.
- `weight_pk_afriat`: suppose `F, L : ℝ → ℝ` satisfy, for all `a, b ∈ [ε, β]`,

      F b − F a ≤ L a · b · (a − b·(a b + √((1 − a²)(1 − b²))))

  with `ℓ ≤ L ≤ Λ` on `[ε, β]` and `ℓ > 0`. Then `V q = F(q_k)`, `λ q = L(q_k)` are continuum Afriat numbers for Debreu's consumer `x q = q_k·(e_k − q_k q)`. This holds on every set `P` of unit prices with coordinates in `[ε, β]`.
- `weight_pk_rationalised`: under the same inequality, by stage 330, one continuous, concave, strictly monotone utility rationalises the consumer on all of `P`.

## Reading
The `A p_k` part of Debreu's weight is the case that the small-constant condition of stage 334 misses. With `V` and `λ` depending only on `q_k`, the `n`-dimensional problem for this weight becomes a one-variable inequality. This is a sufficient condition; it is exact for `n = 2`.

## Numerical evidence (not a proof)
- Grid checks (Python, 2000–3000 points) are run on `[ε, √(1 − ε²)]`, with `F' = −a L`.
- `L a = a √(1 − a²) · e^{−K arccos a}` satisfies the inequality, with positive relative slack, at these values: `K ≥ 5` at `ε = 0.3, 0.2`; `K ≥ 10` at `ε = 0.1`; `K ≥ 20` at `ε = 0.05`.
- The power family `L a = a^{M+1} √(1 − a²)` works at `ε = 0.3, 0.2, 0.1` only for large `M`, and fails at `ε = 0.05` for every `M ≤ 64`.
- Absolute slack can be very small, so these checks are evidence only.

## Limits
- The one-variable inequality is **not proved in Lean** for any specific `F, L`. So the weight `q_k` is reduced, not settled.
- Uniqueness is not addressed.
- General Debreu weights `α_k = Z_k + A p_k` are not covered, and continuous Mantel/Debreu on `S_ε` remains open here.
