import Mathlib

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

#print axioms HomotheticFixedClaim.share_strictly_optimal
#print axioms HomotheticFixedClaim.fixed_claim_strictly_worse
#print axioms HomotheticFixedClaim.log_strict_supergradient
