import Mathlib

/-!
# Stage 343: stability of optimal trades under locally uniform limits

The grid route to the continuum: rationalise the given excess demand exactly on finer and finer
finite grids of prices (finite Mantel, stages 296–333), then pass to a limit.  This file proves
the limit step that does not depend on any estimate:

* `uniform_limit_optimal` — if utilities `u n` converge locally uniformly to a continuous `U`,
  `x n` is optimal for `u n` on the budget at the price `q n`, `q n → p > 0` and `x n → z`, then
  `z` is on the budget at `p` and optimal for `U`.
* `aggregate_limit` — if the trades of the consumers add up to `Z (q n)` at each grid price and
  `Z` is continuous, the limit trades add up to `Z p` exactly.

What is **not** proved here, and is needed for a grid theorem:
1. grid-independent bounds on the finite Afriat numbers (so that the grid utilities are
   uniformly Lipschitz and the trades bounded);
2. a compactness step (Arzelà–Ascoli) to extract the locally uniform limits;
3. unique demand: limits only give *some* optimal trade, i.e. a selection from a demand
   correspondence, never uniqueness (compare `no_unique_of_jump`, stage 334).
-/

noncomputable section

open Finset Filter Topology

namespace GridLimit

variable {S : Type*} [Fintype S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

theorem dot_continuous : Continuous (fun pr : (S → ℝ) × (S → ℝ) => dot pr.1 pr.2) := by
  unfold dot
  exact continuous_finsetSum _ fun s _ =>
    ((continuous_apply s).comp continuous_fst).mul ((continuous_apply s).comp continuous_snd)

/-- **Optimality passes to locally uniform limits.** -/
theorem uniform_limit_optimal [Nonempty S] (u : ℕ → (S → ℝ) → ℝ) (U : (S → ℝ) → ℝ)
    (hU : Continuous U) (hconv : TendstoLocallyUniformly u U atTop)
    (q x : ℕ → S → ℝ) (hb : ∀ n, dot (q n) (x n) = 0)
    (hopt : ∀ n, ∀ y, dot (q n) y ≤ 0 → u n y ≤ u n (x n))
    (p z : S → ℝ) (hp : ∀ s, 0 < p s) (hqp : Tendsto q atTop (𝓝 p))
    (hxz : Tendsto x atTop (𝓝 z)) :
    dot p z = 0 ∧ ∀ y, dot p y ≤ 0 → U y ≤ U z := by
  have hdz : Tendsto (fun n => dot (q n) (x n)) atTop (𝓝 (dot p z)) :=
    (dot_continuous.tendsto (p, z)).comp (hqp.prodMk_nhds hxz)
  have e : (fun n => dot (q n) (x n)) = fun _ => (0 : ℝ) := funext hb
  rw [e] at hdz
  have h0 : dot p z = 0 := tendsto_nhds_unique hdz tendsto_const_nhds
  have hux : Tendsto (fun n => u n (x n)) atTop (𝓝 (U z)) :=
    hconv.tendsto_comp hU.continuousAt hxz
  have hstrict : ∀ y, dot p y < 0 → U y ≤ U z := by
    intro y hy
    have hdy : Tendsto (fun n => dot (q n) y) atTop (𝓝 (dot p y)) :=
      (dot_continuous.tendsto (p, y)).comp (hqp.prodMk_nhds tendsto_const_nhds)
    have hev : ∀ᶠ n in atTop, dot (q n) y < 0 := hdy.eventually (eventually_lt_nhds hy)
    exact le_of_tendsto_of_tendsto
      (hconv.tendsto_comp hU.continuousAt (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))) hux
      (hev.mono fun n hn => hopt n y hn.le)
  refine ⟨h0, fun y hy => ?_⟩
  have hsp : 0 < ∑ s, p s := Finset.sum_pos (fun s _ => hp s) Finset.univ_nonempty
  have hshift : ∀ t : ℝ, dot p (fun s => y s - t) = dot p y - t * ∑ s, p s := by
    intro t
    unfold dot
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hcont : Tendsto (fun t : ℝ => U (fun s => y s - t)) (𝓝[>] 0) (𝓝 (U y)) := by
    have hc : Continuous fun t : ℝ => U (fun s => y s - t) :=
      hU.comp (continuous_pi fun s => continuous_const.sub continuous_id)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), U (fun s => y s - t) ≤ U z :=
    eventually_nhdsWithin_of_forall fun t ht => hstrict _ (by
      rw [hshift]
      have : 0 < t * ∑ s, p s := mul_pos ht hsp
      linarith)
  exact le_of_tendsto hcont hev

omit [Fintype S] in
/-- **The aggregate is exact in the limit.** -/
theorem aggregate_limit {I : Type*} [Fintype I] (Z : (S → ℝ) → S → ℝ) (hZ : Continuous Z)
    (q : ℕ → S → ℝ) (x : I → ℕ → S → ℝ) (hsum : ∀ n, ∑ i, x i n = Z (q n))
    (p : S → ℝ) (z : I → S → ℝ) (hqp : Tendsto q atTop (𝓝 p))
    (hxz : ∀ i, Tendsto (x i) atTop (𝓝 (z i))) :
    ∑ i, z i = Z p := by
  have h1 : Tendsto (fun n => ∑ i, x i n) atTop (𝓝 (∑ i, z i)) :=
    tendsto_finsetSum _ fun i _ => hxz i
  have h2 : Tendsto (fun n => Z (q n)) atTop (𝓝 (Z p)) := (hZ.tendsto p).comp hqp
  have e : (fun n => ∑ i, x i n) = fun n => Z (q n) := funext hsum
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Grid limit, conditional form.**  Suppose that along grid prices `q n → p`, each
consumer `i` has a utility `u i n` with an optimal trade `x i n`, the trades add up to `Z (q n)`,
the utilities converge locally uniformly to continuous `U i`, and the trades converge.  Then the
limit trades are optimal for the limit utilities at `p` and add up to `Z p` exactly. -/
theorem grid_limit [Nonempty S] {I : Type*} [Fintype I] (Z : (S → ℝ) → S → ℝ)
    (hZ : Continuous Z) (u : I → ℕ → (S → ℝ) → ℝ) (U : I → (S → ℝ) → ℝ)
    (hU : ∀ i, Continuous (U i)) (hconv : ∀ i, TendstoLocallyUniformly (u i) (U i) atTop)
    (q : ℕ → S → ℝ) (x : I → ℕ → S → ℝ) (hb : ∀ i n, dot (q n) (x i n) = 0)
    (hopt : ∀ i n, ∀ y, dot (q n) y ≤ 0 → u i n y ≤ u i n (x i n))
    (hsum : ∀ n, ∑ i, x i n = Z (q n))
    (p : S → ℝ) (z : I → S → ℝ) (hp : ∀ s, 0 < p s) (hqp : Tendsto q atTop (𝓝 p))
    (hxz : ∀ i, Tendsto (x i) atTop (𝓝 (z i))) :
    (∀ i, dot p (z i) = 0 ∧ ∀ y, dot p y ≤ 0 → U i y ≤ U i (z i)) ∧ ∑ i, z i = Z p :=
  ⟨fun i => uniform_limit_optimal (u i) (U i) (hU i) (hconv i) q (x i) (hb i) (hopt i) p (z i)
    hp hqp (hxz i), aggregate_limit Z hZ q x hsum p z hqp hxz⟩

end GridLimit

end

#print axioms GridLimit.dot_continuous
#print axioms GridLimit.uniform_limit_optimal
#print axioms GridLimit.aggregate_limit
#print axioms GridLimit.grid_limit
