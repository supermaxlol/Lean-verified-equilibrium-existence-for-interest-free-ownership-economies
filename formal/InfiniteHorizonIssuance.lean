import Mathlib

/-!
Stage 263: issuance dynamics with infinite-horizon savers.

Stage 253 used a two-period log saver.  Here every household follows the infinite-horizon
rule of stage 258: consume `1 - β` of wealth, hold the rest in ownership units.

* `clearing_cap`, `cap_clears` — the market for units clears exactly when the total value
  of units is `β D / (1 - β)`, `D` being total dividends;
* `equilibrium_return` — the gross return on ownership is then `1 / β`;
* `trade_preserves_share` — with a common saving rate, trade leaves every household's
  share of units equal to its share of wealth;
* `share_converges` — with growth `g > 0` and an equal-issuance fraction `σ > 0`, every
  share converges to the equal share `c`; `pro_rata_preserves` — with `σ = 0` shares
  never move;
* `consumption_share` — consumption shares equal wealth shares.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace InfiniteHorizonIssuance

variable {H : Type*} [Fintype H]

theorem clearing_cap (β Q D : ℝ) (hβ1 : β < 1) (h : β * (Q + D) = Q) :
    Q = β * D / (1 - β) := by
  have h1 : (0:ℝ) < 1 - β := by linarith
  rw [eq_div_iff h1.ne']
  linarith

theorem cap_clears (β D : ℝ) (hβ1 : β < 1) :
    β * (β * D / (1 - β) + D) = β * D / (1 - β) := by
  have h1 : (1:ℝ) - β ≠ 0 := by linarith
  field_simp
  ring

theorem cap_pos (β D : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hD : 0 < D) :
    0 < β * D / (1 - β) := div_pos (mul_pos hβ hD) (by linarith)

/-- At the clearing value the gross return on ownership is `1 / β`. -/
theorem equilibrium_return (β Q D : ℝ) (hβ : 0 < β) (hQ : 0 < Q) (h : β * (Q + D) = Q) :
    (Q + D) / Q = 1 / β := by
  rw [div_eq_div_iff hQ.ne' hβ.ne']
  linarith

/-- With a common saving rate, the share of units bought equals the share of wealth. -/
theorem trade_preserves_share (β q : ℝ) (W : H → ℝ) (hβ : β ≠ 0) (hq : q ≠ 0)
    (hW : ∑ h, W h ≠ 0) (h : H) :
    (β * W h / q) / ∑ k, β * W k / q = W h / ∑ k, W k := by
  have hs : ∑ k, β * W k / q = β / q * ∑ k, W k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hs]
  field_simp

theorem consumption_share (β : ℝ) (W : H → ℝ) (hβ : 1 - β ≠ 0) (hW : ∑ h, W h ≠ 0)
    (h : H) :
    ((1 - β) * W h) / ∑ k, (1 - β) * W k = W h / ∑ k, W k := by
  rw [← Finset.mul_sum]
  field_simp

/-- Share of units after one round of issuance. -/
def next (g σ c x : ℝ) : ℝ := (x + g * (σ * c + (1 - σ) * x)) / (1 + g)

def rate (g σ : ℝ) : ℝ := (1 + g * (1 - σ)) / (1 + g)

def shareAt (g σ c x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => next g σ c (shareAt g σ c x0 n)

theorem next_dev (g σ c x : ℝ) (hg : 1 + g ≠ 0) :
    next g σ c x - c = rate g σ * (x - c) := by
  unfold next rate
  field_simp
  ring

theorem shareAt_dev (g σ c x0 : ℝ) (hg : 1 + g ≠ 0) (n : ℕ) :
    shareAt g σ c x0 n - c = rate g σ ^ n * (x0 - c) := by
  induction n with
  | zero => simp [shareAt]
  | succ n ih =>
    show next g σ c (shareAt g σ c x0 n) - c = rate g σ ^ (n + 1) * (x0 - c)
    rw [next_dev g σ c _ hg, ih]
    ring

theorem rate_lt_one (g σ : ℝ) (hg : 0 < g) (hσ : 0 < σ) : rate g σ < 1 := by
  unfold rate
  rw [div_lt_one (by linarith)]
  nlinarith [mul_pos hg hσ]

theorem rate_nonneg (g σ : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) : 0 ≤ rate g σ := by
  unfold rate
  exact div_nonneg (by nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]) (by linarith)

/-- **Equal issuance equalises ownership** under infinite-horizon saving. -/
theorem share_converges (g σ c x0 : ℝ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (shareAt g σ c x0) atTop (𝓝 c) := by
  have hne : 1 + g ≠ 0 := by linarith
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (rate_nonneg g σ hg hσ1)
    (rate_lt_one g σ hg hσ)).mul_const (x0 - c)
  rw [zero_mul] at h
  have h2 : Tendsto (fun n => c + rate g σ ^ n * (x0 - c)) atTop (𝓝 (c + 0)) :=
    tendsto_const_nhds.add h
  rw [add_zero] at h2
  have e : shareAt g σ c x0 = fun n => c + rate g σ ^ n * (x0 - c) :=
    funext (fun n => by have := shareAt_dev g σ c x0 hne n; linarith)
  rw [e]
  exact h2

/-- Pro-rata issuance never moves shares. -/
theorem pro_rata_preserves (g c x0 : ℝ) (hg : 1 + g ≠ 0) (n : ℕ) :
    shareAt g 0 c x0 n = x0 := by
  have h := shareAt_dev g 0 c x0 hg n
  have hr : rate g 0 = 1 := by
    unfold rate
    rw [sub_zero, mul_one, div_self hg]
  rw [hr, one_pow, one_mul] at h
  linarith

end InfiniteHorizonIssuance

end

#print axioms InfiniteHorizonIssuance.clearing_cap
#print axioms InfiniteHorizonIssuance.cap_clears
#print axioms InfiniteHorizonIssuance.equilibrium_return
#print axioms InfiniteHorizonIssuance.trade_preserves_share
#print axioms InfiniteHorizonIssuance.consumption_share
#print axioms InfiniteHorizonIssuance.share_converges
#print axioms InfiniteHorizonIssuance.pro_rata_preserves
