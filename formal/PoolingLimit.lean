import Mathlib

/-!
Stage 310: the pooling limit.

Stage 304 proved that with `N` members, common loss variance `v` and common correlation `ρ`, the
variance of the per-member pooled loss is `ρ v + (1 − ρ) v / N`.  Here, as a function of `N`:

* it decreases in `N` and tends to exactly `ρ v` (`pv_antitone`, `pv_tendsto`);
* it never falls below `ρ v` (`pv_floor`), and any target above `ρ v` is eventually met
  (`pv_eventually_lt`);
* with independent losses (`ρ = 0`) it is `v / N → 0` (`pv_indep`, `pv_indep_tendsto`);
* a Chebyshev reserve `k` per member that guarantees failure probability at most `α` must satisfy
  `k² ≥ ρ v / α` for every pool size (`reserve_floor`).  The correlated part of risk has to be held
  as capital; pooling cannot diversify it away.
-/

open Filter Topology

noncomputable section

namespace PoolingLimit

/-- Per-member pooled-loss variance with `N` members (stage 304). -/
def pv (ρ v : ℝ) (N : ℕ) : ℝ := ρ * v + (1 - ρ) * v / N

theorem pv_tendsto (ρ v : ℝ) : Tendsto (pv ρ v) atTop (𝓝 (ρ * v)) := by
  have h : Tendsto (fun N : ℕ => (1 - ρ) * v / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ * v) atTop (𝓝 (ρ * v))).add h
  rw [add_zero] at h2
  exact h2

theorem pv_floor (ρ v : ℝ) (hρ : ρ ≤ 1) (hv : 0 ≤ v) (N : ℕ) : ρ * v ≤ pv ρ v N := by
  unfold pv
  have : 0 ≤ (1 - ρ) * v / N := div_nonneg (mul_nonneg (by linarith) hv) (Nat.cast_nonneg N)
  linarith

theorem pv_antitone (ρ v : ℝ) (hρ : ρ ≤ 1) (hv : 0 ≤ v) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    pv ρ v M ≤ pv ρ v N := by
  unfold pv
  have h1 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have := div_le_div_of_nonneg_left (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ρ) hv) h1 h2
  linarith

theorem pv_eventually_lt (ρ v t : ℝ) (ht : ρ * v < t) : ∀ᶠ N in atTop, pv ρ v N < t :=
  (pv_tendsto ρ v).eventually (gt_mem_nhds ht)

theorem pv_indep (v : ℝ) (N : ℕ) : pv 0 v N = v / N := by
  unfold pv; ring

theorem pv_indep_tendsto (v : ℝ) : Tendsto (pv 0 v) atTop (𝓝 0) := by
  have h := pv_tendsto 0 v
  rwa [zero_mul] at h

/-- **Correlated risk needs capital at every pool size.** -/
theorem reserve_floor (ρ v α k : ℝ) (hρ : ρ ≤ 1) (hv : 0 ≤ v) (hα : 0 < α) (hk : 0 < k) (N : ℕ)
    (hguar : pv ρ v N / k ^ 2 ≤ α) : ρ * v / α ≤ k ^ 2 := by
  have h1 := pv_floor ρ v hρ hv N
  have h2 : pv ρ v N ≤ α * k ^ 2 := (div_le_iff₀ (by positivity)).1 hguar
  rw [div_le_iff₀ hα]
  nlinarith

end PoolingLimit

end

#print axioms PoolingLimit.pv_tendsto
#print axioms PoolingLimit.pv_floor
#print axioms PoolingLimit.pv_antitone
#print axioms PoolingLimit.pv_eventually_lt
#print axioms PoolingLimit.pv_indep
#print axioms PoolingLimit.pv_indep_tendsto
#print axioms PoolingLimit.reserve_floor
