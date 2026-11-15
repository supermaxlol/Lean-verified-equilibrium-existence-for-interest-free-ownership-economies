import Mathlib

/-!
Stage 305: an interest-free lender of last resort with a haircut in place of Bagehot's
penalty rate.

A bank pledges collateral worth `V0` today; its value at repayment is `V s` in state `s`.  The
central bank lends `(1 − h) V0` at zero interest and recovers `min (V s, loan)`.

* Safety: if the haircut `h` covers the worst collateral drop on the support
  (`V s ≥ (1 − d) V0` with `d ≤ h`), the central bank loses nothing.  In general its expected
  loss `∑ π s · max (loan − V s, 0)` falls as the haircut rises.
* Screening: raising cash `X` in the market costs `m X` (a fire-sale discount or a profit
  share given up); borrowing from the central bank ties up `X / (1 − h)` of collateral with
  shadow cost `λ` per unit.  The bank goes to the market iff `m < λ / (1 − h)`.
* Design: if normal-time market cost `m0` is below stress cost `m1` and the safe haircut is not
  too large (`λ / (1 − d) < m1`), there is a haircut `h ≥ d` that is safe, keeps banks in the
  market in normal times and brings them to the central bank under stress.  The haircut does
  Bagehot's screening job with no interest.
-/

noncomputable section

open Finset

namespace LolrHaircut

variable {S : Type*} [Fintype S]

/-- Expected loss of an interest-free collateralised loan. -/
def eloss (π : S → ℝ) (V : S → ℝ) (loan : ℝ) : ℝ := ∑ s, π s * max (loan - V s) 0

/-- **Safe haircut: zero loss.** -/
theorem safe_zero_loss (π : S → ℝ) (V : S → ℝ) (V0 d h : ℝ) (hV0 : 0 ≤ V0) (hdh : d ≤ h)
    (hdrop : ∀ s, 0 < π s → (1 - d) * V0 ≤ V s) (hπ : ∀ s, 0 ≤ π s) :
    eloss π V ((1 - h) * V0) = 0 := by
  unfold eloss
  refine Finset.sum_eq_zero fun s _ => ?_
  rcases (hπ s).lt_or_eq with hp | hp
  · have h1 : (1 - h) * V0 ≤ (1 - d) * V0 := mul_le_mul_of_nonneg_right (by linarith) hV0
    have : max ((1 - h) * V0 - V s) 0 = 0 := max_eq_right (by linarith [hdrop s hp])
    rw [this, mul_zero]
  · rw [← hp, zero_mul]

/-- **A bigger haircut never raises the expected loss.** -/
theorem loss_antitone (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (V : S → ℝ) (V0 h h' : ℝ)
    (hV0 : 0 ≤ V0) (hh : h ≤ h') : eloss π V ((1 - h') * V0) ≤ eloss π V ((1 - h) * V0) := by
  unfold eloss
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hπ s)
  have : (1 - h') * V0 ≤ (1 - h) * V0 := mul_le_mul_of_nonneg_right (by linarith) hV0
  exact max_le_max (by linarith) le_rfl

/-- **Screening.**  Market funding is strictly cheaper than the central bank iff
`m < λ / (1 − h)`. -/
theorem market_iff (m lam h X : ℝ) (hh : h < 1) (hX : 0 < X) :
    m * X < lam * (X / (1 - h)) ↔ m < lam / (1 - h) := by
  have h1 : 0 < 1 - h := by linarith
  rw [show lam * (X / (1 - h)) = lam / (1 - h) * X by ring]
  exact mul_lt_mul_iff_left₀ hX

/-- **Design theorem: a haircut replaces the penalty rate.** -/
theorem lolr_design (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (V : S → ℝ) (V0 d lam m0 m1 : ℝ)
    (hV0 : 0 ≤ V0) (hd0 : 0 ≤ d) (hd1 : d < 1) (hlam : 0 < lam)
    (hdrop : ∀ s, 0 < π s → (1 - d) * V0 ≤ V s) (hm : m0 < m1) (hcap : lam / (1 - d) < m1) :
    ∃ h, d ≤ h ∧ h < 1 ∧ eloss π V ((1 - h) * V0) = 0 ∧
      m0 < lam / (1 - h) ∧ lam / (1 - h) < m1 := by
  have hd' : 0 < 1 - d := by linarith
  set τ := max (lam / (1 - d)) ((m0 + m1) / 2) with hτ
  have hτ1 : lam / (1 - d) ≤ τ := le_max_left _ _
  have hτ2 : (m0 + m1) / 2 ≤ τ := le_max_right _ _
  have hτlt : τ < m1 := max_lt hcap (by linarith)
  have hlamd : lam ≤ lam / (1 - d) := by
    rw [le_div_iff₀ hd']; nlinarith
  have hτpos : 0 < τ := lt_of_lt_of_le hlam (le_trans hlamd hτ1)
  have hq : 0 < lam / τ := div_pos hlam hτpos
  have hq1 : lam / τ ≤ 1 - d := by
    rw [div_le_iff₀ hτpos]
    have := mul_le_mul_of_nonneg_left hτ1 hd'.le
    rw [mul_div_cancel₀ _ hd'.ne'] at this
    linarith
  have hval : lam / (1 - (1 - lam / τ)) = τ := by
    rw [show 1 - (1 - lam / τ) = lam / τ by ring]
    field_simp
  refine ⟨1 - lam / τ, by linarith, by linarith, safe_zero_loss π V V0 d _ hV0 (by linarith)
    hdrop hπ, ?_, ?_⟩
  · rw [hval]; linarith
  · rw [hval]; exact hτlt

end LolrHaircut

end

#print axioms LolrHaircut.safe_zero_loss
#print axioms LolrHaircut.loss_antitone
#print axioms LolrHaircut.market_iff
#print axioms LolrHaircut.lolr_design
