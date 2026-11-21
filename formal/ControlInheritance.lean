import Mathlib

/-!
# Stage 359: control and inheritance under issuance rules

Voting weight equals ownership share. New units are issued at rate `g`, a fraction `σ` equally
(`c` per household) and the rest pro rata (`next`, stages 253 and 263, common patience).

* `coalition_next`: a coalition's total share follows the same rule as one household, with the
  equal share `|S| c`.
* `coalition_dev`: its share after `n` periods is `|S| c + rate ^ n (s0 − |S| c)`.
* `majority_dissolves`: if the coalition is less than half the population (`|S| c < 1/2`) and
  `σ > 0`, its majority is eventually lost, whatever its starting share.
* `majority_gone_at`: an explicit test: once `rate ^ n (s0 − |S| c) < 1/2 − |S| c`, the
  coalition is below one half.
* `pro_rata_majority_persists`: with `σ = 0`, a majority, once held, is held forever.
* `estate_split`: dividing an estate among heirs by weights summing to one preserves the
  dynasty's share.
* `dynasty_converges`: under equal issuance a dynasty's share tends to `m c`, where `m` is its
  number of members: per-household issuance tracks headcount, not inheritance.

Reading: under pro rata issuance control is permanent; any positive equal-issuance fraction
dissolves every minority's majority in finite time.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace ControlInheritance

def next (g σ c y : ℝ) : ℝ := (y + g * (σ * c + (1 - σ) * y)) / (1 + g)

def rate (g σ : ℝ) : ℝ := (1 + g * (1 - σ)) / (1 + g)

def iter (g σ c s0 : ℝ) : ℕ → ℝ
  | 0 => s0
  | n + 1 => next g σ c (iter g σ c s0 n)

/-- A coalition's share follows the one-household rule with equal share `|S| c`. -/
theorem coalition_next {H : Type*} (S : Finset H) (g σ c : ℝ) (x : H → ℝ) :
    ∑ h ∈ S, next g σ c (x h) = next g σ ((S.card : ℝ) * c) (∑ h ∈ S, x h) := by
  unfold next
  rw [← Finset.sum_div]
  congr 1
  have e : ∀ h, x h + g * (σ * c + (1 - σ) * x h) = (1 + g * (1 - σ)) * x h + g * σ * c :=
    fun h => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem next_dev (g σ c x : ℝ) (hg : 1 + g ≠ 0) :
    next g σ c x - c = rate g σ * (x - c) := by
  unfold next rate
  field_simp
  ring

theorem coalition_dev (g σ c s0 : ℝ) (hg : 1 + g ≠ 0) (n : ℕ) :
    iter g σ c s0 n = c + rate g σ ^ n * (s0 - c) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    show next g σ c (iter g σ c s0 n) = _
    have := next_dev g σ c (iter g σ c s0 n) hg
    rw [ih] at this ⊢
    rw [pow_succ]
    linarith [this]

theorem rate_lt_one (g σ : ℝ) (hg : 0 < g) (hσ : 0 < σ) : rate g σ < 1 := by
  unfold rate
  rw [div_lt_one (by linarith)]
  nlinarith [mul_pos hg hσ]

theorem rate_nonneg (g σ : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) : 0 ≤ rate g σ := by
  unfold rate
  exact div_nonneg (by nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]) (by linarith)

theorem iter_tendsto (g σ c s0 : ℝ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (iter g σ c s0) atTop (𝓝 c) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (rate_nonneg g σ hg hσ1)
    (rate_lt_one g σ hg hσ)).mul_const (s0 - c)
  rw [zero_mul] at h
  have h2 := (tendsto_const_nhds (x := c)).add h
  rw [add_zero] at h2
  have e : iter g σ c s0 = fun n => c + rate g σ ^ n * (s0 - c) :=
    funext fun n => coalition_dev g σ c s0 (by linarith) n
  rw [e]
  exact h2

/-- **A minority coalition's majority dissolves** under any positive equal issuance. -/
theorem majority_dissolves (g σ cS s0 : ℝ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hcS : cS < 1 / 2) : ∀ᶠ n in atTop, iter g σ cS s0 n < 1 / 2 :=
  (iter_tendsto g σ cS s0 hg hσ hσ1).eventually (gt_mem_nhds hcS)

/-- An explicit test for the period by which control is lost. -/
theorem majority_gone_at (g σ cS s0 : ℝ) (hg : 1 + g ≠ 0) (n : ℕ)
    (h : rate g σ ^ n * (s0 - cS) < 1 / 2 - cS) : iter g σ cS s0 n < 1 / 2 := by
  rw [coalition_dev g σ cS s0 hg n]
  linarith

/-- **Pro rata issuance makes control permanent.** -/
theorem pro_rata_majority_persists (g cS s0 : ℝ) (hg : 1 + g ≠ 0) (n : ℕ) :
    iter g 0 cS s0 n = s0 := by
  rw [coalition_dev g 0 cS s0 hg n]
  have hr : rate g 0 = 1 := by
    unfold rate
    rw [sub_zero, mul_one, div_self hg]
  rw [hr, one_pow, one_mul]
  ring

/-- Splitting an estate among heirs preserves the dynasty's share. -/
theorem estate_split {I : Type*} (s : Finset I) (w : I → ℝ) (hw : ∑ i ∈ s, w i = 1) (x : ℝ) :
    ∑ i ∈ s, w i * x = x := by
  rw [← Finset.sum_mul, hw, one_mul]

/-- **A dynasty's share tracks its headcount** under equal issuance. -/
theorem dynasty_converges (g σ c s0 : ℝ) (m : ℕ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (iter g σ ((m : ℝ) * c) s0) atTop (𝓝 ((m : ℝ) * c)) :=
  iter_tendsto g σ _ s0 hg hσ hσ1

end ControlInheritance

end

#print axioms ControlInheritance.coalition_next
#print axioms ControlInheritance.coalition_dev
#print axioms ControlInheritance.majority_dissolves
#print axioms ControlInheritance.majority_gone_at
#print axioms ControlInheritance.pro_rata_majority_persists
#print axioms ControlInheritance.estate_split
#print axioms ControlInheritance.dynasty_converges
