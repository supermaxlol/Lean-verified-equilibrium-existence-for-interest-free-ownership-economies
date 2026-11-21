import Mathlib

/-!
# Stage 360: productive capacity and the distribution of ownership

Household `h` saves the fraction `β h` of wealth (stage 356) and owns the share `x h`. Saved
wealth becomes next period's productive capacity, which returns the gross factor `R`, so
capacity grows by `R * B x`, where `B x = ∑ h, β h * x h` is the aggregate saving rate.

* `capacity_path`: with a constant saving rate, `K n = (R B) ^ n K 0`.
* `saving_bounds`: if every `β h ∈ [lo, hi]`, then `lo ≤ B x ≤ hi`.
* `common_patience_neutral`: with a common `β`, `B x = β` for every distribution: the issuance
  rule then costs no growth at all.
* `saving_diff`: for two distributions, `B x − B x' = ∑ (β h − m) (x h − x' h)` for any `m`.
* `growth_cost_bound`: `|B x − B x'| ≤ (hi − lo) / 2 · ∑ |x h − x' h|`: changing the
  distribution changes capacity growth by at most half the spread of patience times the total
  share moved.
* `growth_cost_floor`: hence an issuance rule that moves a total share `T` costs at most
  `R (hi − lo) T / 2` of growth per period.

Reading: when people are equally patient, distribution and growth are independent. When they
differ, the growth cost of spreading ownership is bounded by the spread of patience and the
share moved, and can be weighed against the welfare gain of stage 362.
-/

noncomputable section

open Finset BigOperators

namespace CapacityDistribution

variable {H : Type*} [Fintype H]

def B (β x : H → ℝ) : ℝ := ∑ h, β h * x h

def K (G K0 : ℝ) : ℕ → ℝ
  | 0 => K0
  | n + 1 => G * K G K0 n

theorem capacity_path (G K0 : ℝ) (n : ℕ) : K G K0 n = G ^ n * K0 := by
  induction n with
  | zero => simp [K]
  | succ n ih => rw [K, ih, pow_succ]; ring

theorem saving_bounds (β x : H → ℝ) (lo hi : ℝ) (hlo : ∀ h, lo ≤ β h) (hhi : ∀ h, β h ≤ hi)
    (hx : ∀ h, 0 ≤ x h) (hs : ∑ h, x h = 1) : lo ≤ B β x ∧ B β x ≤ hi := by
  unfold B
  constructor
  · calc lo = ∑ h, lo * x h := by rw [← Finset.mul_sum, hs, mul_one]
      _ ≤ ∑ h, β h * x h :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hlo h) (hx h)
  · calc ∑ h, β h * x h ≤ ∑ h, hi * x h :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hhi h) (hx h)
      _ = hi := by rw [← Finset.mul_sum, hs, mul_one]

theorem common_patience_neutral (b : ℝ) (x : H → ℝ) (hs : ∑ h, x h = 1) :
    B (fun _ => b) x = b := by
  unfold B
  rw [← Finset.mul_sum, hs, mul_one]

theorem saving_diff (β x x' : H → ℝ) (m : ℝ) (hs : ∑ h, x h = 1) (hs' : ∑ h, x' h = 1) :
    B β x - B β x' = ∑ h, (β h - m) * (x h - x' h) := by
  unfold B
  have e : ∑ h, (β h - m) * (x h - x' h) =
      ∑ h, β h * x h - ∑ h, β h * x' h - m * (∑ h, x h - ∑ h, x' h) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [e, hs, hs']
  ring

/-- **The growth cost of redistribution is bounded.** -/
theorem growth_cost_bound (β x x' : H → ℝ) (lo hi : ℝ) (hlo : ∀ h, lo ≤ β h)
    (hhi : ∀ h, β h ≤ hi) (hs : ∑ h, x h = 1) (hs' : ∑ h, x' h = 1) :
    |B β x - B β x'| ≤ (hi - lo) / 2 * ∑ h, |x h - x' h| := by
  rw [saving_diff β x x' ((hi + lo) / 2) hs hs', Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h _ => ?_)
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith [hlo h, hhi h]

theorem growth_cost_floor (β x x' : H → ℝ) (lo hi R T : ℝ) (hR : 0 ≤ R) (hlo : ∀ h, lo ≤ β h)
    (hhi : ∀ h, β h ≤ hi) (hs : ∑ h, x h = 1) (hs' : ∑ h, x' h = 1)
    (hT : ∑ h, |x h - x' h| ≤ T) :
    |R * B β x - R * B β x'| ≤ R * ((hi - lo) / 2 * T) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hR]
  apply mul_le_mul_of_nonneg_left _ hR
  have hspread : 0 ≤ (hi - lo) / 2 := by
    obtain ⟨h⟩ : Nonempty H := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      simp at hs
    linarith [hlo h, hhi h]
  exact (growth_cost_bound β x x' lo hi hlo hhi hs hs').trans
    (mul_le_mul_of_nonneg_left hT hspread)

end CapacityDistribution

end

#print axioms CapacityDistribution.capacity_path
#print axioms CapacityDistribution.saving_bounds
#print axioms CapacityDistribution.common_patience_neutral
#print axioms CapacityDistribution.saving_diff
#print axioms CapacityDistribution.growth_cost_bound
#print axioms CapacityDistribution.growth_cost_floor
