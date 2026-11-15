import Mathlib

/-!
Stage 268: ownership implements the complete-markets equilibrium for homothetic utility.

Generalises stage 266 from log utility to any felicity `u` with a marginal-utility function
`m` that is a supergradient (`u a ≤ u b + m b * (a - b)`) and homogeneous
(`m (w * y) = h w * m y`).  State prices are `π s * m (Y s)`.

* `share_optimal` — the share bundle `w * Y s` maximises expected utility in the budget set;
* `ownership_equilibrium` — shares are positive, sum to one, each household's share bundle
  costs exactly its endowment, is optimal, and every state market clears exactly;
* `log_supergradient`, `log_homogeneous` — log utility satisfies the hypotheses.

The hypotheses are not verified here for power utility.
-/

noncomputable section

open Finset BigOperators

namespace HomotheticOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

theorem share_optimal (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * (w * Y s)) :
    ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w * Y s) := by
  have hterm : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
    intro s
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s))
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
      ring
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have h3 := mul_nonneg hh (sub_nonneg.2 hbud)
  linarith

/-- **Ownership implements the complete-markets equilibrium.** -/
theorem ownership_equilibrium [Nonempty S] (π Y : S → ℝ) (ω : I → S → ℝ) (u m h : ℝ → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s * m (Y s) * (w i * Y s) = ∑ s, π s * m (Y s) * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * ω i s →
        ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w i * Y s)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s := by
  have hp : ∀ s, 0 < π s * m (Y s) := fun s => mul_pos (hπ s) (hm _ (hY s))
  have hT : 0 < ∑ s, π s * m (Y s) * Y s :=
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hY s)) Finset.univ_nonempty
  have hWi : ∀ i, 0 < ∑ s, π s * m (Y s) * ω i s := fun i =>
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hωpos i s)) Finset.univ_nonempty
  have hwpos : ∀ i, 0 < (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s :=
    fun i => div_pos (hWi i) hT
  have htot : ∑ i, ∑ s, π s * m (Y s) * ω i s = ∑ s, π s * m (Y s) * Y s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, hω s])
  have hsum : ∑ i, (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s = 1 := by
    rw [← Finset.sum_div, htot, div_self hT.ne']
  have hcost : ∀ i, ∑ s, π s * m (Y s)
        * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
      = ∑ s, π s * m (Y s) * ω i s := by
    intro i
    have e : ∀ s, π s * m (Y s)
          * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
        = (∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s)
          * (π s * m (Y s) * Y s) := fun s => by ring
    rw [Finset.sum_congr rfl (fun s _ => e s), ← Finset.mul_sum, div_mul_cancel₀ _ hT.ne']
  refine ⟨fun i => (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s, hwpos, hsum,
    hcost, fun i x hx hbud => ?_, fun s => ?_⟩
  · refine share_optimal π Y x u m h _ (fun s => (hπ s).le) hY (hwpos i) hsg
      (fun y hy => hhom _ y (hwpos i) hy) (hh _ (hwpos i)) hx ?_
    rw [hcost i]
    exact hbud
  · rw [← Finset.sum_mul, hsum, one_mul, hω s]

theorem log_supergradient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ Real.log b + 1 / b * (a - b) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have e : 1 / b * (a - b) = a / b - 1 := by
    have := hb.ne'
    field_simp
  rw [e]
  linarith

theorem log_homogeneous (w y : ℝ) (hw : 0 < w) (hy : 0 < y) :
    1 / (w * y) = 1 / w * (1 / y) := by
  have := hw.ne'
  have := hy.ne'
  field_simp

end HomotheticOwnership

end

#print axioms HomotheticOwnership.share_optimal
#print axioms HomotheticOwnership.ownership_equilibrium
#print axioms HomotheticOwnership.log_supergradient
#print axioms HomotheticOwnership.log_homogeneous
