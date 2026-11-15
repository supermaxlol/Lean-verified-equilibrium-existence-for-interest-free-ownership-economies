import Mathlib

/-!
Stage 318: selection on the mean under profit sharing, and how borrower contribution limits it.

Stage 314 showed profit sharing removes Stiglitz–Weiss selection on *risk*.  It still prices every
applicant at the pool mean `μ̄`.  A project of size `I`, borrower contribution `k ≤ I`, lender share
`θ = (I − k)/μ̄` (lender breaks even at the pool mean).  For a type with mean `μ`:

* `subsidy_eq`: the type pays `θμ − (I − k) = (I − k)(μ − μ̄)/μ̄` more than its fair price.
* `subsidy_pos_iff`: above-average types overpay, below-average types are subsidized (adverse
  selection on the mean, Myers–Majluf style).
* `subsidy_abs`, `subsidy_anti`: the size of the mispricing is `(I − k)|μ − μ̄|/μ̄`, falling in the
  borrower's contribution `k`; `full_contribution`: it vanishes at `k = I`.
* `stays_iff`: with an outside source costing `(1 + φ)(I − k)`, a type stays iff `μ ≤ (1 + φ)μ̄`.
  Selection on the mean only removes types more than `φ` above the pool mean.
* `lender_return`: if the applicant mean `μa` differs from the priced `μ̄`, the lender's loss is at
  most `(I − k)|μa − μ̄|/μ̄`.
* `gain_diff`, `contribution_screens`: raising the required contribution lowers the net gain of
  below-average types and raises it for above-average types, so contribution screens on the mean.

Honest limits: means are known to borrowers and only the pool mean to the lender; the re-pricing
fixed point (unravelling) is not solved; the borrower's capacity to contribute is assumed.
-/

noncomputable section

namespace MeanSelection

theorem subsidy_eq (I k μ μbar : ℝ) (hμ : 0 < μbar) :
    (I - k) / μbar * μ - (I - k) = (I - k) * (μ - μbar) / μbar := by
  field_simp

theorem subsidy_pos_iff (I k μ μbar : ℝ) (hμ : 0 < μbar) (hk : k < I) :
    0 < (I - k) / μbar * μ - (I - k) ↔ μbar < μ := by
  rw [subsidy_eq I k μ μbar hμ, div_pos_iff_of_pos_right hμ]
  constructor
  · intro h
    by_contra hc
    have : (I - k) * (μ - μbar) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [not_lt.1 hc])
    linarith
  · intro h
    exact mul_pos (by linarith) (by linarith)

theorem subsidy_abs (I k μ μbar : ℝ) (hμ : 0 < μbar) (hk : k ≤ I) :
    |(I - k) / μbar * μ - (I - k)| = (I - k) * |μ - μbar| / μbar := by
  rw [subsidy_eq I k μ μbar hμ, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.2 hk), abs_of_pos hμ]

theorem subsidy_anti (I k k' μ μbar : ℝ) (hμ : 0 < μbar) (hkk : k ≤ k') (hk' : k' ≤ I) :
    |(I - k') / μbar * μ - (I - k')| ≤ |(I - k) / μbar * μ - (I - k)| := by
  rw [subsidy_abs I k' μ μbar hμ hk', subsidy_abs I k μ μbar hμ (hkk.trans hk')]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)) hμ.le

theorem full_contribution (I μ μbar : ℝ) : (I - I) / μbar * μ - (I - I) = 0 := by simp

theorem stays_iff (I k μ μbar φ : ℝ) (hμ : 0 < μbar) (hk : k < I) :
    (I - k) / μbar * μ ≤ (I - k) * (1 + φ) ↔ μ ≤ (1 + φ) * μbar := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
  constructor
  · intro h
    exact le_of_mul_le_mul_left (by linarith : (I - k) * μ ≤ (I - k) * ((1 + φ) * μbar))
      (sub_pos.2 hk)
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h (sub_pos.2 hk).le]

theorem lender_return (I k μa μbar : ℝ) (hμ : 0 < μbar) (hk : k ≤ I) :
    -((I - k) * |μa - μbar| / μbar) ≤ (I - k) / μbar * μa - (I - k) := by
  rw [← subsidy_abs I k μa μbar hμ hk]
  exact neg_abs_le _

/-- Net gain of a type with mean `μ` that contributes `k` and gives up share `(I − k)/μ̄`. -/
def gain (I k μ μbar : ℝ) : ℝ := μ - (I - k) / μbar * μ - k

theorem gain_diff (I k k' μ μbar : ℝ) (hμ : 0 < μbar) :
    gain I k' μ μbar - gain I k μ μbar = (k' - k) * (μ - μbar) / μbar := by
  unfold gain
  field_simp
  ring

theorem contribution_screens (I k k' μ μbar : ℝ) (hμ : 0 < μbar) (hkk : k < k') :
    (μ < μbar → gain I k' μ μbar < gain I k μ μbar) ∧
      (μbar < μ → gain I k μ μbar < gain I k' μ μbar) := by
  have h := gain_diff I k k' μ μbar hμ
  constructor
  · intro hlt
    have : (k' - k) * (μ - μbar) / μbar < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hμ
    linarith
  · intro hgt
    have : 0 < (k' - k) * (μ - μbar) / μbar :=
      div_pos (mul_pos (by linarith) (by linarith)) hμ
    linarith

end MeanSelection

end

#print axioms MeanSelection.subsidy_eq
#print axioms MeanSelection.subsidy_pos_iff
#print axioms MeanSelection.subsidy_abs
#print axioms MeanSelection.subsidy_anti
#print axioms MeanSelection.full_contribution
#print axioms MeanSelection.stays_iff
#print axioms MeanSelection.lender_return
#print axioms MeanSelection.gain_diff
#print axioms MeanSelection.contribution_screens
