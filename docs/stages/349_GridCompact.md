# Stage 349: the compactness step of the grid route

Lean 4.35 + Mathlib. 15 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Stage 343 (`GridLimit`) took grid economies and **assumed** that the grid utilities converge. This stage proves the compactness step that supplies a limit, under explicit uniform bounds.

## Results
- `lipSet_compact` (Arzelà–Ascoli, via `ArzelaAscoli.isCompact_of_equicontinuous`): in `C(X, ℝ)` with the compact-open topology, the set `LipSet x₀ M B` of `M`-Lipschitz functions with `|f x₀| ≤ B` is compact. `X` is any pseudo-metric space, and no compactness of `X` is needed. Helpers: `lipFun_closed`, `lipFun_sub_pi`, `lipFun_compact`, `lip_continuous`, `image_lipSet`.
- `mem_of_cluster`: a closed property that holds eventually along a sequence holds at each of its cluster points.
- `concaveSet_closed`, `modulusSet_closed`: concavity is closed in `C(ℝ^S, ℝ)`, and so is a fixed uniform monotone modulus `a ≤ b ⇒ f a + m(a,b) ≤ f b`.
- `grid_cluster`: let `u n` lie in one `LipSet 0 M B` and rationalise a trade map `x`, continuous on `P`, on grids `G n ⊆ P` that become dense in `P`, with `∑ p_s > 0` on `P`. Then some cluster point `U` of `(u n)` is in `LipSet 0 M B`, and `p · y ≤ 0 ⇒ U y ≤ U (x p)` holds for **every** `p ∈ P`, not only grid points. Strict budgets come from density, continuity of `x` and the uniform Lipschitz bound. The closed budget then follows by shifting every coordinate down by `t`.
- `grid_cluster_shape`: concavity and a uniform monotone modulus pass to `U`.
- `grid_cluster_family`: there is one limit utility per consumer. No joint subsequence is needed, because each consumer's trades are fixed.

## Limits
- The uniform Lipschitz constant `M` and bound `B` for the grid utilities are **assumed**, not derived. This is the main open input of the grid route.
- `U` is a cluster point (a limit along a subnet), not necessarily the limit of a subsequence.
- Uniqueness of the maximiser does **not** pass to the limit. Strict monotonicity passes only through a uniform modulus `m`.
