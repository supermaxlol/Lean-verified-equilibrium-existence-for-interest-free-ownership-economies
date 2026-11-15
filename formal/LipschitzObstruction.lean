import Mathlib

/-!
# Stage 355: why a uniform Lipschitz bound cannot close continuous Mantel

Stage 353 shows that a Walras excess demand which is bounded and `Lz`-Lipschitz on the cap is
a sum of `n` rational consumers' trades, with the scale `A` chosen so that
`Lz / (A ε) ≤ ν (1 − δ0)`. The natural route to merely continuous `z` approximates it by
Lipschitz `z_m` and passes to the limit, which needs a bound on the `Lz` of the `z_m` that does
not depend on `m`. This file shows that such a bound exists only when `z` is already Lipschitz:

* `lipschitz_of_tendsto`: a pointwise limit of `L`-Lipschitz functions is `L`-Lipschitz.
* `lipschitz_of_eventually`: the same if only eventually `L`-Lipschitz.
* `unbounded_constants`: so, if `z` is not Lipschitz, every Lipschitz approximating sequence
  has constants that are not eventually bounded by any `L`.
* `sqrt_not_lipschitz`: `√` on `[0, 1]` is continuous and not Lipschitz (a concrete case).
* `afriat_scale_vanishes`: along any sequence with `L_m → ∞`, the stage-353 scale obeys
  `A_m → ∞`, and the Afriat multiplier bound `1 / (A_m (1 − δ0)) → 0`: the constructed
  utilities become flat in the limit, so the limit is not a usable consumer.

Reading: the uniform-Lipschitz route to continuous Mantel is closed. A proof for continuous
`z` needs a different idea (for example, Afriat numbers driven by a modulus of continuity
rather than a Lipschitz constant). This is an obstruction to one route, not a proof that
continuous Mantel fails.
-/

open Filter Topology

namespace LipschitzObstruction

/-- A pointwise limit of `L`-Lipschitz functions is `L`-Lipschitz. -/
theorem lipschitz_of_tendsto {X : Type*} [PseudoMetricSpace X] (f : ℕ → X → ℝ) (g : X → ℝ)
    (L : NNReal) (hf : ∀ m, LipschitzWith L (f m))
    (h : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (g x))) : LipschitzWith L g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : Tendsto (fun m => dist (f m x) (f m y)) atTop (𝓝 (dist (g x) (g y))) :=
    (h x).dist (h y)
  exact le_of_tendsto' hd fun m => (hf m).dist_le_mul x y

/-- The same if the functions are only eventually `L`-Lipschitz. -/
theorem lipschitz_of_eventually {X : Type*} [PseudoMetricSpace X] (f : ℕ → X → ℝ)
    (g : X → ℝ) (L : NNReal) (hf : ∀ᶠ m in atTop, LipschitzWith L (f m))
    (h : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (g x))) : LipschitzWith L g := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  apply lipschitz_of_tendsto (fun m => f (m + N)) g L (fun m => hN _ (Nat.le_add_left _ _))
  intro x
  exact (h x).comp (tendsto_add_atTop_nat N)

/-- **Obstruction.** If `g` is not Lipschitz, the Lipschitz constants of any pointwise
approximating sequence are not eventually bounded. -/
theorem unbounded_constants {X : Type*} [PseudoMetricSpace X] (f : ℕ → X → ℝ) (g : X → ℝ)
    (hg : ∀ L : NNReal, ¬ LipschitzWith L g)
    (h : ∀ x, Tendsto (fun m => f m x) atTop (𝓝 (g x))) (L : NNReal) :
    ¬ ∀ᶠ m in atTop, LipschitzWith L (f m) :=
  fun hf => hg L (lipschitz_of_eventually f g L hf h)

/-- `√` on `[0, 1]` is not Lipschitz. -/
theorem sqrt_not_lipschitz (L : ℝ) (hL : 0 ≤ L) :
    ¬ ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt x - Real.sqrt y| ≤ L * |x - y| := by
  intro h
  have hL1 : 0 < L + 1 := by linarith
  set x : ℝ := 1 / (L + 1) ^ 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]
    nlinarith
  have hs : Real.sqrt x = 1 / (L + 1) := by
    rw [hx, Real.sqrt_div' 1 (sq_nonneg _), Real.sqrt_one, Real.sqrt_sq hL1.le]
  have := h x ⟨hx0.le, hx1⟩ 0 ⟨le_rfl, zero_le_one⟩
  rw [Real.sqrt_zero, sub_zero, sub_zero, hs, abs_of_pos hx0,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (L + 1)), hx] at this
  have e : L * (1 / (L + 1) ^ 2) = L / (L + 1) * (1 / (L + 1)) := by
    field_simp
  rw [e] at this
  have hlt : L / (L + 1) < 1 := by
    rw [div_lt_one hL1]
    linarith
  have hp : (0:ℝ) < 1 / (L + 1) := by positivity
  nlinarith

/-- **The Afriat scale degenerates.** If the Lipschitz constants `Lz m → ∞` and the scale
satisfies the stage-353 condition `Lz m ≤ c · A m` (with `c = ε ν (1 − δ0) > 0`), then
`A m → ∞` and the multiplier bound `1 / (A m (1 − δ0)) → 0`. -/
theorem afriat_scale_vanishes (Lz A : ℕ → ℝ) (c δ0 : ℝ) (hc : 0 < c) (hδ : δ0 < 1)
    (hL : Tendsto Lz atTop atTop) (hA : ∀ m, Lz m ≤ c * A m) :
    Tendsto A atTop atTop ∧ Tendsto (fun m => 1 / (A m * (1 - δ0))) atTop (𝓝 0) := by
  have hA' : Tendsto A atTop atTop := by
    have h1 : Tendsto (fun m => Lz m / c) atTop atTop := hL.atTop_div_const hc
    refine tendsto_atTop_mono (fun m => ?_) h1
    rw [div_le_iff₀ hc]
    linarith [hA m]
  refine ⟨hA', ?_⟩
  have h2 : Tendsto (fun m => A m * (1 - δ0)) atTop atTop :=
    hA'.atTop_mul_const (by linarith)
  have h3 := h2.inv_tendsto_atTop
  simp only [one_div]
  exact h3

end LipschitzObstruction

#print axioms LipschitzObstruction.lipschitz_of_tendsto
#print axioms LipschitzObstruction.lipschitz_of_eventually
#print axioms LipschitzObstruction.unbounded_constants
#print axioms LipschitzObstruction.sqrt_not_lipschitz
#print axioms LipschitzObstruction.afriat_scale_vanishes
