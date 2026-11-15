import Mathlib

/-!
Stage 252: Cobb–Douglas demand derived from utility maximisation.

For weights `α s > 0` summing to one, prices `p s > 0` and wealth `w > 0`, the bundle
`x* s = α s * w / p s` maximises `∑ α s * log (x s)` over all strictly positive bundles
within the budget, and is the unique maximiser.  This discharges the demand rule that
stage 250 took as given.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace CobbDouglasDemand

variable {S : Type*} [Fintype S]

/-- Per-good comparison: the log-utility gap is bounded by the expenditure gap. -/
theorem term_le (a p x w : ℝ) (ha : 0 < a) (hp : 0 < p) (hw : 0 < w) (hx : 0 < x) :
    a * Real.log x - a * Real.log (a * w / p) ≤ p * x / w - a := by
  have hstar : 0 < a * w / p := div_pos (mul_pos ha hw) hp
  have h1 : Real.log (x / (a * w / p)) ≤ x / (a * w / p) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx hstar)
  rw [Real.log_div hx.ne' hstar.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 ha.le
  have h3 : a * (x / (a * w / p) - 1) = p * x / w - a := by
    have := ha.ne'
    have := hp.ne'
    have := hw.ne'
    field_simp
  linarith

/-- Strict version away from the candidate bundle. -/
theorem term_lt (a p x w : ℝ) (ha : 0 < a) (hp : 0 < p) (hw : 0 < w) (hx : 0 < x)
    (hne : x ≠ a * w / p) :
    a * Real.log x - a * Real.log (a * w / p) < p * x / w - a := by
  have hstar : 0 < a * w / p := div_pos (mul_pos ha hw) hp
  have hne1 : x / (a * w / p) ≠ 1 := fun h => hne ((div_eq_one_iff_eq hstar.ne').1 h)
  have h1 : Real.log (x / (a * w / p)) < x / (a * w / p) - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos hx hstar) hne1
  rw [Real.log_div hx.ne' hstar.ne'] at h1
  have h2 := mul_lt_mul_of_pos_left h1 ha
  have h3 : a * (x / (a * w / p) - 1) = p * x / w - a := by
    have := ha.ne'
    have := hp.ne'
    have := hw.ne'
    field_simp
  linarith

/-- The Cobb–Douglas bundle is affordable (it spends exactly `w`). -/
theorem demand_budget (α p : S → ℝ) (w : ℝ) (hp : ∀ s, 0 < p s) (hsum : ∑ s, α s = 1) :
    ∑ s, p s * (α s * w / p s) = w := by
  have h1 : ∀ s, p s * (α s * w / p s) = α s * w := by
    intro s
    have := (hp s).ne'
    field_simp
  simp only [h1, ← Finset.sum_mul, hsum, one_mul]

/-- **Cobb–Douglas demand is utility-maximising.** -/
theorem demand_optimal (α p x : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, p s * x s ≤ w) :
    ∑ s, α s * Real.log (x s) ≤ ∑ s, α s * Real.log (α s * w / p s) := by
  have hs : ∑ s, (α s * Real.log (x s) - α s * Real.log (α s * w / p s))
      ≤ ∑ s, (p s * x s / w - α s) :=
    Finset.sum_le_sum (fun s _ => term_le (α s) (p s) (x s) w (hα s) (hp s) hw (hx s))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hs
  have h1 : (∑ s, p s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

/-- **Uniqueness.** Any other affordable positive bundle gives strictly lower utility. -/
theorem demand_unique (α p x : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, p s * x s ≤ w) (hne : ∃ s, x s ≠ α s * w / p s) :
    ∑ s, α s * Real.log (x s) < ∑ s, α s * Real.log (α s * w / p s) := by
  obtain ⟨t, ht⟩ := hne
  have hs : ∑ s, (α s * Real.log (x s) - α s * Real.log (α s * w / p s))
      < ∑ s, (p s * x s / w - α s) :=
    Finset.sum_lt_sum
      (fun s _ => term_le (α s) (p s) (x s) w (hα s) (hp s) hw (hx s))
      ⟨t, Finset.mem_univ t, term_lt (α t) (p t) (x t) w (hα t) (hp t) hw (hx t) ht⟩
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hs
  have h1 : (∑ s, p s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

end CobbDouglasDemand

end

#print axioms CobbDouglasDemand.term_le
#print axioms CobbDouglasDemand.term_lt
#print axioms CobbDouglasDemand.demand_budget
#print axioms CobbDouglasDemand.demand_optimal
#print axioms CobbDouglasDemand.demand_unique
