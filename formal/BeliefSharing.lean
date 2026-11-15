import Mathlib

/-!
Stage 284: households with different beliefs (log utility).

Household `i` believes state `s` has probability `π i s`.  Let `w i` be wealth shares and
`P s = ∑ j, w j * π j s` the wealth-weighted belief.

* `belief_optimal` — at the prices `P s / Y s` the bundle `w * π s / P s * Y s` maximises
  expected log utility under the household's OWN beliefs among bundles costing no more;
* `belief_cost` — that bundle costs `w * ∑ s, π s`;
* `belief_clears` — the bundles use exactly output;
* `belief_common` — if the household's belief equals the weighted belief in a state, its
  consumption there is exactly its wealth share of output.

So with different beliefs the household's share of output varies by state: it is the
wealth share scaled by how likely the household thinks the state is relative to the
market.
-/

noncomputable section

open Finset BigOperators

namespace BeliefSharing

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Optimal bundle under own beliefs.** -/
theorem belief_optimal (π P Y x' : S → ℝ) (w : ℝ) (hπ : ∀ s, 0 < π s) (hP : ∀ s, 0 < P s)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w) (hx' : ∀ s, 0 < x' s)
    (hbud : ∑ s, P s / Y s * x' s ≤ ∑ s, P s / Y s * (w * π s / P s * Y s)) :
    ∑ s, π s * Real.log (x' s) ≤ ∑ s, π s * Real.log (w * π s / P s * Y s) := by
  have hterm : ∀ s, π s * Real.log (x' s) ≤ π s * Real.log (w * π s / P s * Y s)
      + 1 / w * (P s / Y s * x' s - P s / Y s * (w * π s / P s * Y s)) := by
    intro s
    have hxs : 0 < w * π s / P s * Y s :=
      mul_pos (div_pos (mul_pos hw (hπ s)) (hP s)) (hY s)
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hx' s) hxs)
    rw [Real.log_div (hx' s).ne' hxs.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    have e : π s * (x' s / (w * π s / P s * Y s) - 1)
        = 1 / w * (P s / Y s * x' s - P s / Y s * (w * π s / P s * Y s)) := by
      have := (hπ s).ne'
      have := (hP s).ne'
      have := (hY s).ne'
      have := hw.ne'
      field_simp
    rw [e] at h2
    linarith
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  have h3 := mul_nonpos_of_nonneg_of_nonpos (one_div_pos.2 hw).le (sub_nonpos.2 hbud)
  linarith

/-- The bundle costs the wealth share. -/
theorem belief_cost (π P Y : S → ℝ) (w : ℝ) (hP : ∀ s, 0 < P s) (hY : ∀ s, 0 < Y s) :
    ∑ s, P s / Y s * (w * π s / P s * Y s) = w * ∑ s, π s := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have := (hP s).ne'
  have := (hY s).ne'
  field_simp

omit [Fintype S] in
/-- The bundles use exactly output. -/
theorem belief_clears (π : I → S → ℝ) (w : I → ℝ) (Y : S → ℝ) (s : S)
    (hP : 0 < ∑ j, w j * π j s) :
    ∑ i, w i * π i s / (∑ j, w j * π j s) * Y s = Y s := by
  rw [← Finset.sum_mul, ← Finset.sum_div, div_self hP.ne', one_mul]

omit [Fintype S] in
/-- Where the household agrees with the market it holds its wealth share. -/
theorem belief_common (π P Y : S → ℝ) (w : ℝ) (s : S) (hP : 0 < P s) (h : π s = P s) :
    w * π s / P s * Y s = w * Y s := by
  rw [h, mul_div_assoc, div_self hP.ne', mul_one]

end BeliefSharing

end

#print axioms BeliefSharing.belief_optimal
#print axioms BeliefSharing.belief_cost
#print axioms BeliefSharing.belief_clears
#print axioms BeliefSharing.belief_common
