import Mathlib

/-!
Stage 272: share claims are solvent in every state; fixed claims are not, and they amplify
the dispersion of what is left.

States `S`, output `Y s > 0`.  A share claim pays `w * Y s`.  A fixed claim pays `b` in
every state, leaving the issuer `a * Y s - b`.

* `share_solvent` — a positive share pays a positive amount in every state;
* `shares_exhaust` — share claims summing to one pay out exactly output in every state;
* `default_iff` — the issuer of a fixed claim is short exactly in the states with
  `Y s < b / a`;
* `fixed_claims_exceed` — fixed claims totalling more than output in some state cannot all
  be paid there;
* `leverage_amplifies` — for `Y s > Y s' > b > 0` the residual `Y - b` has a larger
  ratio across the two states than output itself;
* `share_ratio` — a share claim has the same ratio across states as output.
-/

noncomputable section

open Finset BigOperators

namespace SolvencyByConstruction

variable {I S : Type*} [Fintype I]

theorem share_solvent (Y : S → ℝ) (w : ℝ) (hY : ∀ s, 0 < Y s) (hw : 0 < w) (s : S) :
    0 < w * Y s := mul_pos hw (hY s)

theorem shares_exhaust (Y : S → ℝ) (w : I → ℝ) (hw1 : ∑ i, w i = 1) (s : S) :
    ∑ i, w i * Y s = Y s := by
  rw [← Finset.sum_mul, hw1, one_mul]

theorem default_iff (Y : S → ℝ) (a b : ℝ) (ha : 0 < a) (s : S) :
    a * Y s - b < 0 ↔ Y s < b / a := by
  rw [lt_div_iff₀ ha]
  constructor <;> intro h <;> linarith

theorem fixed_claims_exceed (Y : S → ℝ) (b : I → ℝ) (s : S) (hB : Y s < ∑ i, b i)
    (pay : I → ℝ) (hfeas : ∑ i, pay i ≤ Y s) : ∃ i, pay i < b i := by
  by_contra hcon
  push Not at hcon
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcon i)
  linarith

/-- **Leverage amplifies dispersion.** -/
theorem leverage_amplifies (y y' b : ℝ) (hb : 0 < b) (hy' : b < y') (hy : y' < y) :
    y / y' < (y - b) / (y' - b) := by
  have h1 : 0 < y' := by linarith
  have h2 : 0 < y' - b := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos hb (sub_pos.2 hy)]

theorem share_ratio (y y' w : ℝ) (hw : 0 < w) (hy' : 0 < y') :
    (w * y) / (w * y') = y / y' := by
  have := hw.ne'
  have := hy'.ne'
  field_simp

end SolvencyByConstruction

end

#print axioms SolvencyByConstruction.share_solvent
#print axioms SolvencyByConstruction.shares_exhaust
#print axioms SolvencyByConstruction.default_iff
#print axioms SolvencyByConstruction.fixed_claims_exceed
#print axioms SolvencyByConstruction.leverage_amplifies
#print axioms SolvencyByConstruction.share_ratio
