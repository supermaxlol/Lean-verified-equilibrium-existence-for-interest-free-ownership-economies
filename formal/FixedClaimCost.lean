import Mathlib

/-!
Stage 267: a fixed claim layered on ownership is strictly costly under log utility.

Setting of stage 266: states `S`, probabilities `π s > 0`, output `Y s > 0`, state prices
`π s / Y s`, a household of wealth `w` with expected log utility.

* `equity_strictly_optimal` — any affordable bundle that differs from the ownership bundle
  `w * Y s` in some state gives strictly lower expected utility;
* `fixed_claim_differs` — if output varies across states, a bundle `a * Y s - b` with
  `b ≠ 0` (ownership plus a fixed payment or receipt) is never the ownership bundle;
* `fixed_claim_strictly_worse` — hence both the payer (`b > 0`) and the receiver (`b < 0`)
  of a fixed claim are strictly worse off than with the ownership bundle of equal cost.
-/

noncomputable section

open Finset BigOperators

namespace FixedClaimCost

variable {S : Type*} [Fintype S]

theorem equity_strictly_optimal (π Y x : S → ℝ) (w : ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s / Y s * x s ≤ w) (s0 : S) (hne : x s0 ≠ w * Y s0) :
    ∑ s, π s * Real.log (x s) < ∑ s, π s * Real.log (w * Y s) := by
  have e : ∀ s, π s * (x s / (w * Y s) - 1) = π s / Y s * x s / w - π s := by
    intro s
    have := (hY s).ne'
    have := hw.ne'
    field_simp
  have hterm : ∀ s, π s * Real.log (x s)
      ≤ π s * Real.log (w * Y s) + (π s / Y s * x s / w - π s) := by
    intro s
    have hwy : 0 < w * Y s := mul_pos hw (hY s)
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hx s) hwy)
    rw [Real.log_div (hx s).ne' hwy.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    rw [e s] at h2
    linarith
  have hstrict : π s0 * Real.log (x s0)
      < π s0 * Real.log (w * Y s0) + (π s0 / Y s0 * x s0 / w - π s0) := by
    have hwy : 0 < w * Y s0 := mul_pos hw (hY s0)
    have hr : x s0 / (w * Y s0) ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hwy.ne'] at h
      exact hne h
    have h1 := Real.log_lt_sub_one_of_pos (div_pos (hx s0) hwy) hr
    rw [Real.log_div (hx s0).ne' hwy.ne'] at h1
    have h2 := mul_lt_mul_of_pos_left h1 (hπ s0)
    rw [e s0] at h2
    linarith
  have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
    ⟨s0, Finset.mem_univ s0, hstrict⟩
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hπ1] at hsum
  have h3 : (∑ s, π s / Y s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

theorem fixed_claim_differs (Y : S → ℝ) (a b w : ℝ) (hb : b ≠ 0) (s1 s2 : S)
    (hvar : Y s1 ≠ Y s2) : ∃ s0, a * Y s0 - b ≠ w * Y s0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon s1
  have h2 := hcon s2
  have h3 : (a - w) * (Y s1 - Y s2) = 0 := by linarith
  rcases mul_eq_zero.1 h3 with h | h
  · have ha : a = w := by linarith
    rw [ha] at h1
    exact hb (by linarith)
  · exact hvar (by linarith)

/-- **Cost of a fixed claim.** -/
theorem fixed_claim_strictly_worse (π Y : S → ℝ) (a b w : ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) (hw : 0 < w) (hb : b ≠ 0) (s1 s2 : S)
    (hvar : Y s1 ≠ Y s2) (hx : ∀ s, 0 < a * Y s - b)
    (hbud : ∑ s, π s / Y s * (a * Y s - b) ≤ w) :
    ∑ s, π s * Real.log (a * Y s - b) < ∑ s, π s * Real.log (w * Y s) := by
  obtain ⟨s0, hs0⟩ := fixed_claim_differs Y a b w hb s1 s2 hvar
  exact equity_strictly_optimal π Y (fun s => a * Y s - b) w hπ hπ1 hY hw hx hbud s0 hs0

end FixedClaimCost

end

#print axioms FixedClaimCost.equity_strictly_optimal
#print axioms FixedClaimCost.fixed_claim_differs
#print axioms FixedClaimCost.fixed_claim_strictly_worse
