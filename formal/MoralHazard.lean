import Mathlib

/-!
Stage 309: Moral hazard, profit sharing and interest-free debt.

Effort is high or low and shifts the distribution of output: `πH`, `πL` over finitely many states
with output `y s`.  High effort costs the entrepreneur `κ`.  Under repayment schedule `R` the
entrepreneur keeps `y − R`, so high effort is chosen iff `κ ≤ E_H[y − R] − E_L[y − R]`.

* Profit sharing (`R = θ y`) dilutes incentives: the gain is `(1 − θ) ΔY` (`ps_gain`), and effort
  holds iff `θ ≤ 1 − κ/ΔY` (`ps_ic_iff`).
* A profit-sharing contract that induces effort and returns principal `I` exists iff
  `I ≤ E_H y · (1 − κ/ΔY)` (`ps_financeable_iff`).  This is weakly below the first-best bound
  `E_H y − κ`, strictly when low-effort output is positive (`ps_gap`, `ps_gap_strict`).
* An interest-free loan of face `I` keeps full incentives: if it never defaults, the gain is exactly
  `ΔY` (`qard_gain`); if it defaults only in states whose probability effort does not change, the
  same holds (`qard_gain_default`).  The dilution objection is to profit sharing, not to
  interest-free finance.
-/

open Finset BigOperators

noncomputable section

namespace MoralHazard

variable {S : Type*} [Fintype S]

/-- Expectation. -/
def Ex (π y : S → ℝ) : ℝ := ∑ s, π s * y s

/-- The entrepreneur's gain from high effort under repayment `R`. -/
def gain (πH πL y R : S → ℝ) : ℝ := Ex πH (fun s => y s - R s) - Ex πL (fun s => y s - R s)

/-- High effort is incentive compatible. -/
def ICe (πH πL y R : S → ℝ) (κ : ℝ) : Prop := κ ≤ gain πH πL y R

theorem gain_eq (πH πL y R : S → ℝ) :
    gain πH πL y R = (Ex πH y - Ex πL y) - ∑ s, (πH s - πL s) * R s := by
  unfold gain Ex
  simp only [mul_sub, Finset.sum_sub_distrib, sub_mul]
  ring

/-- **Profit sharing dilutes the effort gain.** -/
theorem ps_gain (πH πL y : S → ℝ) (θ : ℝ) :
    gain πH πL y (fun s => θ * y s) = (1 - θ) * (Ex πH y - Ex πL y) := by
  rw [gain_eq]
  have h : ∑ s, (πH s - πL s) * (θ * y s) = θ * (Ex πH y - Ex πL y) := by
    unfold Ex
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h]; ring

/-- **Effort under profit sharing.** -/
theorem ps_ic_iff (πH πL y : S → ℝ) (θ κ : ℝ) (hΔ : 0 < Ex πH y - Ex πL y) :
    ICe πH πL y (fun s => θ * y s) κ ↔ θ ≤ 1 - κ / (Ex πH y - Ex πL y) := by
  unfold ICe
  rw [ps_gain]
  constructor
  · intro h
    have : κ / (Ex πH y - Ex πL y) ≤ 1 - θ := by rw [div_le_iff₀ hΔ]; linarith
    linarith
  · intro h
    have : κ / (Ex πH y - Ex πL y) ≤ 1 - θ := by linarith
    rw [div_le_iff₀ hΔ] at this
    linarith

/-- **Which projects profit sharing can finance.** -/
theorem ps_financeable_iff (πH πL y : S → ℝ) (κ I : ℝ) (hΔ : 0 < Ex πH y - Ex πL y)
    (hEH : 0 < Ex πH y) (hκ : 0 ≤ κ) (hI : 0 ≤ I) :
    (∃ θ, 0 ≤ θ ∧ θ ≤ 1 ∧ ICe πH πL y (fun s => θ * y s) κ ∧ I ≤ θ * Ex πH y) ↔
      I ≤ Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) := by
  constructor
  · rintro ⟨θ, _, _, hic, hθI⟩
    have h1 := (ps_ic_iff πH πL y θ κ hΔ).1 hic
    have h2 := mul_le_mul_of_nonneg_right h1 hEH.le
    nlinarith
  · intro h
    have hq : 0 ≤ κ / (Ex πH y - Ex πL y) := div_nonneg hκ hΔ.le
    have hc := mul_comm (Ex πH y) (1 - κ / (Ex πH y - Ex πL y))
    refine ⟨1 - κ / (Ex πH y - Ex πL y), ?_, by linarith,
      (ps_ic_iff πH πL y _ κ hΔ).2 le_rfl, by linarith⟩
    by_contra hneg
    have : Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) < 0 :=
      mul_neg_of_pos_of_neg hEH (lt_of_not_ge hneg)
    linarith

/-- **The moral-hazard cost of profit sharing**: its bound is below the first-best `E_H y − κ`. -/
theorem ps_gap (πH πL y : S → ℝ) (κ : ℝ) (hΔ : 0 < Ex πH y - Ex πL y) (hL : 0 ≤ Ex πL y)
    (hκ : 0 ≤ κ) : Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) ≤ Ex πH y - κ := by
  have e : Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) =
      Ex πH y - Ex πH y * κ / (Ex πH y - Ex πL y) := by ring
  have h : κ ≤ Ex πH y * κ / (Ex πH y - Ex πL y) := by
    rw [le_div_iff₀ hΔ]; nlinarith
  linarith

theorem ps_gap_strict (πH πL y : S → ℝ) (κ : ℝ) (hΔ : 0 < Ex πH y - Ex πL y)
    (hL : 0 < Ex πL y) (hκ : 0 < κ) :
    Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) < Ex πH y - κ := by
  have e : Ex πH y * (1 - κ / (Ex πH y - Ex πL y)) =
      Ex πH y - Ex πH y * κ / (Ex πH y - Ex πL y) := by ring
  have h : κ < Ex πH y * κ / (Ex πH y - Ex πL y) := by
    rw [lt_div_iff₀ hΔ]; nlinarith
  linarith

/-- **A riskless interest-free loan keeps full incentives.** -/
theorem qard_gain (πH πL y : S → ℝ) (I : ℝ) (hH : ∑ s, πH s = 1) (hL : ∑ s, πL s = 1) :
    gain πH πL y (fun _ => I) = Ex πH y - Ex πL y := by
  rw [gain_eq]
  have h : ∑ s, (πH s - πL s) * I = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hH, hL]; ring
  rw [h, sub_zero]

/-- **Defaulting interest-free debt keeps full incentives** when effort does not change the
probability of the default states. -/
theorem qard_gain_default (πH πL y : S → ℝ) (I : ℝ) (hH : ∑ s, πH s = 1) (hL : ∑ s, πL s = 1)
    (hsame : ∀ s, y s < I → πH s = πL s) :
    gain πH πL y (fun s => min (y s) I) = Ex πH y - Ex πL y := by
  rw [gain_eq]
  have h : ∑ s, (πH s - πL s) * min (y s) I = ∑ s, (πH s - πL s) * I :=
    Finset.sum_congr rfl fun s _ => by
      by_cases hs : y s < I
      · rw [hsame s hs, sub_self, zero_mul, zero_mul]
      · rw [min_eq_right (not_lt.1 hs)]
  have h0 : ∑ s, (πH s - πL s) * I = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hH, hL]; ring
  rw [h, h0, sub_zero]

/-- **First-best effort under an interest-free loan.** -/
theorem qard_ic_iff (πH πL y : S → ℝ) (I κ : ℝ) (hH : ∑ s, πH s = 1) (hL : ∑ s, πL s = 1)
    (hsame : ∀ s, y s < I → πH s = πL s) :
    ICe πH πL y (fun s => min (y s) I) κ ↔ κ ≤ Ex πH y - Ex πL y := by
  unfold ICe; rw [qard_gain_default πH πL y I hH hL hsame]

end MoralHazard

end

#print axioms MoralHazard.gain_eq
#print axioms MoralHazard.ps_gain
#print axioms MoralHazard.ps_ic_iff
#print axioms MoralHazard.ps_financeable_iff
#print axioms MoralHazard.ps_gap
#print axioms MoralHazard.ps_gap_strict
#print axioms MoralHazard.qard_gain
#print axioms MoralHazard.qard_gain_default
#print axioms MoralHazard.qard_ic_iff
