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


/-!
Stage 270: with strictly concave homothetic utility the ownership bundle is the unique
optimum, and a fixed claim layered on it is strictly costly.

Setting of stage 268 with the supergradient inequality strict off the diagonal
(`u a < u b + m b * (a - b)` for `a ≠ b`).

* `share_strictly_optimal` — any affordable bundle that differs from the share bundle in
  some state gives strictly lower expected utility;
* `fixed_claim_strictly_worse` — a bundle `a * Y s - b` with `b ≠ 0` (a share of output
  plus or minus a fixed amount), when output varies across two states, is strictly worse
  than the share bundle of the same cost;
* `log_strict_supergradient` — log utility satisfies the strict hypothesis.
-/

noncomputable section

open Finset BigOperators

namespace HomotheticFixedClaim

variable {S : Type*} [Fintype S]

theorem share_strictly_optimal (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s * m (Y s) * x s ≤ w * ∑ s, π s * m (Y s) * Y s)
    (s0 : S) (hne : x s0 ≠ w * Y s0) :
    ∑ s, π s * u (x s) < ∑ s, π s * u (w * Y s) := by
  have hstrict : ∀ s, x s ≠ w * Y s → π s * u (x s) < π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
    intro s hs
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s)) hs
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_lt_mul_of_pos_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
      ring
    linarith
  have hweak : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
    intro s
    by_cases hs : x s = w * Y s
    · have e : h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) = 0 := by
        rw [hs]; ring
      rw [e, hs, add_zero]
    · exact (hstrict s hs).le
  have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hweak s)
    ⟨s0, Finset.mem_univ s0, hstrict s0 hne⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  have := mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.2 hbud)
  linarith

/-- **A fixed claim on top of ownership is strictly costly.** -/
theorem fixed_claim_strictly_worse (π Y : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (a b : ℝ) (hb : b ≠ 0) (s1 s2 : S) (hvar : Y s1 ≠ Y s2)
    (hpos : ∀ s, 0 < a * Y s - b)
    (hbud : ∑ s, π s * m (Y s) * (a * Y s - b) ≤ w * ∑ s, π s * m (Y s) * Y s) :
    ∑ s, π s * u (a * Y s - b) < ∑ s, π s * u (w * Y s) := by
  have hex : ∃ s0, a * Y s0 - b ≠ w * Y s0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon s1
    have h2 := hcon s2
    have h3 : (a - w) * (Y s1 - Y s2) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with hz | hz
    · apply hb
      have haw : a = w := by linarith
      rw [haw] at h1
      linarith
    · exact hvar (by linarith)
  obtain ⟨s0, hs0⟩ := hex
  exact share_strictly_optimal π Y (fun s => a * Y s - b) u m h w hπ hY hw hsg hhom hh
    hpos hbud s0 hs0

theorem log_strict_supergradient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log a < Real.log b + 1 / b * (a - b) := by
  have h1 : a / b ≠ 1 := fun hc => hab ((div_eq_one_iff_eq hb.ne').1 hc)
  have h2 := Real.log_lt_sub_one_of_pos (div_pos ha hb) h1
  rw [Real.log_div ha.ne' hb.ne'] at h2
  have e : 1 / b * (a - b) = a / b - 1 := by field_simp
  linarith

end HomotheticFixedClaim

end


/-!
Stage 275: every Pareto-efficient interior allocation is a division of ownership.

Converse of stage 269, under the strict hypotheses of stage 270.  If a strictly positive
allocation `x` uses exactly output and is Pareto efficient, there are shares `w i > 0`
summing to one with `x i s = w i * Y s` in every state.

Proof: take `x` itself as the endowment.  Stage 268 gives a share allocation that every
household weakly prefers; efficiency rules out a strict gain; strict optimality (stage 270)
then forces `x i` to be the share bundle.
-/

noncomputable section

open Finset BigOperators

namespace EfficientIsOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Efficient allocations are divisions of ownership.** -/
theorem efficient_is_ownership [Nonempty S] (π Y : S → ℝ) (u m h : ℝ → ℝ)
    (x : I → S → ℝ) (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s)
    (hx : ∀ i s, 0 < x i s) (hsum : ∀ s, ∑ i, x i s = Y s)
    (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w)
    (heff : ∀ x' : I → S → ℝ, (∀ i s, 0 < x' i s) → (∀ s, ∑ i, x' i s ≤ Y s) →
      (∀ i, ∑ s, π s * u (x i s) ≤ ∑ s, π s * u (x' i s)) →
      ∀ k, ¬ ∑ s, π s * u (x k s) < ∑ s, π s * u (x' k s)) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ i s, x i s = w i * Y s := by
  have hweaksg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b) := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab, sub_self, mul_zero, add_zero]
    · exact (hsg a b ha hb hab).le
  obtain ⟨w, hw, hw1, hcost, hopt, hclear⟩ :=
    HomotheticOwnership.ownership_equilibrium π Y x u m h hπ hY hx hsum hm hweaksg hhom hh
  refine ⟨w, hw, hw1, fun i s0 => ?_⟩
  by_contra hne
  have hbud : ∑ s, π s * m (Y s) * x i s ≤ w i * ∑ s, π s * m (Y s) * Y s := by
    rw [← hcost i, Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl (fun s _ => by ring))
  have hstrict := HomotheticFixedClaim.share_strictly_optimal π Y (x i) u m h (w i) hπ hY
    (hw i) hsg (fun y hy => hhom (w i) y (hw i) hy) (hh _ (hw i)) (hx i) hbud s0 hne
  exact heff (fun i s => w i * Y s) (fun i s => mul_pos (hw i) (hY s))
    (fun s => le_of_eq ((hclear s).trans (hsum s)))
    (fun i => hopt i (x i) (hx i) le_rfl) i hstrict

end EfficientIsOwnership

end

#print axioms EfficientIsOwnership.efficient_is_ownership
