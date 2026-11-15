# Stage 306: Mantel/Debreu on a continuum of prices with unique demand

Lean 4.35 + Mathlib. 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Statement (`MantelUnique.mantel_unique`)

Prices `P` on the unit sphere with every coordinate `≥ ε > 0`. `Z` bounded by `B`, Walras' law
`p·Z(p) = 0`. With `A = B/ε + 1`, `α_k(p) = Z_k(p) + A p_k` and
`x_k(p) = α_k(p) (e_k − p_k p)`:

1. `∑_k x_k(p) = Z(p)` (Debreu's decomposition).
2. `p·x_k(p) = 0` (each trade exhausts its budget).
3. Consumer `k` has a monotone, quasiconcave utility `u_k` such that, for every `p ∈ P`, `x_k(p)` is the
   **unique** maximizer of `u_k` on `{y | p·y ≤ 0}`. Every other affordable bundle is strictly worse.

The only extra hypothesis is continuity of each trade map `q ↦ x_k(q)` at every `p ∈ P`, stated as
"`∑_i |x_k(q)_i − x_k(p)_i| ≤ d` once `p·q > 1 − ρ`". It follows from continuity of `Z` on `P`,
because on the unit sphere `p·q → 1` exactly when `q → p`. That implication is not formalised here; the
hypothesis is stated directly on the trade map.

## Construction

`K_s = conv{x_k(q) | q ∈ P, q_k ≤ s} + ℝ^S_+`, `u_k(y) = −inf{s ≥ 0 | y ∈ K_s or s ≥ 2}`.

* `K_s` is convex, nested in `s` and closed upward, so `u_k` is monotone and quasiconcave (`uu_mono`,
  `uu_quasiconcave`).
* `x_k(p) ∈ K_{p_k}`, so `u_k(x_k(p)) ≥ −p_k`.
* **Strictness (`unique_demand`).** Take an affordable `y ≠ x_k(p)` with `d = ∑|y_i − x_k(p)_i| > 0`.
  Tilt the price functional: `ℓ(z) = p·z + δ w·z`, where `w_i = ∓1` is chosen against the sign of
  `y_i − x_k(p)_i`. For small `δ, η > 0`:
  - every generator `x_k(q)` with `q_k ≤ p_k + η` has `ℓ ≥ ℓ(x_k(p)) − δd/2`;
    - near `p` this uses continuity;
    - far from `p` it uses the strict revealed-preference margin `α ≥ ε`;
  - adding a nonnegative `r` raises `ℓ` (because `δ ≤ ε ≤ p_i`);
  - but `ℓ(y) ≤ ℓ(x_k(p)) − δd`.

  So `y ∉ K_{p_k+η}`, giving `u_k(y) ≤ −p_k − η < u_k(x_k(p))`.

## What this closes, and what it does not

* Stage 302 gave the weak form: `x_k(p)` is *a* maximizer. This stage gives single-valued demand,
  i.e. Debreu's 1974 statement on `S_ε` in its full form (`|S|` consumers, monotone convex preferences,
  demand equal to `x_k(p)` exactly).
* Utilities are quasiconcave, not strictly quasiconcave. Uniqueness is proved directly on the budget
  set and does not come from strict convexity.
* Endowments are implicit: the formal object is the excess-demand (trade) vector. Adding `e_k`-type
  endowments is a translation.
* Continuity of `Z` → continuity of `x_k` in the `p·q` form is assumed as stated, not derived.
* The price domain is `S_ε` (bounded away from the boundary), as in Debreu. The boundary behaviour
  of `Z` is not addressed.
