import Mathlib

/-!
# Stage 350: the shape of debt and the interest on it are separable

Finite states `S`, probabilities `π`, output `y`. A debt contract with face `D` pays
`min (y s) D`; the state is verified (at cost `c`) exactly when the borrower defaults,
`y s < D`. The lender's outside option is cash at zero return, so the face `D0` that just
returns the principal carries no time premium. Any larger face `D ≥ D0` is a premium.

Results:
* `surplus_split`: lender's net receipts plus the borrower's residual equal total surplus.
* `surplus_anti`, `surplus_strict`: a premium never raises total surplus, and strictly
  lowers it when it adds default states with positive probability and `c > 0`.
* `resid_anti`: a premium never raises the borrower's residual.
* `gain_anti`: under first-order stochastic dominance, a premium never raises the
  borrower's gain from effort.
* `premium_transfer`, `lender_gain_le_loss`: what the lender gains from a premium is at most
  what the borrower loses; the difference is verification cost.
* `zero_premium_dominates`: the capstone.
-/

open Finset

namespace ShapeInterest

variable {S : Type*} [Fintype S]

/-- Expectation under weights `π`. -/
def E (π f : S → ℝ) : ℝ := ∑ s, π s * f s

/-- Probability of default (and so of verification) under face `D`. -/
noncomputable def vprob (π y : S → ℝ) (D : ℝ) : ℝ := ∑ s, if y s < D then π s else 0

/-- Lender's expected receipts net of verification cost. -/
noncomputable def lender (π y : S → ℝ) (c D : ℝ) : ℝ :=
  E π (fun s => min (y s) D) - c * vprob π y D

/-- Borrower's expected residual. -/
noncomputable def resid (π y : S → ℝ) (D : ℝ) : ℝ := E π (fun s => y s - min (y s) D)

/-- Total surplus: expected output less expected verification cost. -/
noncomputable def surplus (π y : S → ℝ) (c D : ℝ) : ℝ := E π y - c * vprob π y D

/-- Borrower's gain from effort: residual under `πH` less residual under `πL`. -/
noncomputable def gain (πH πL y : S → ℝ) (D : ℝ) : ℝ := resid πH y D - resid πL y D

theorem surplus_split (π y : S → ℝ) (c D : ℝ) :
    lender π y c D + resid π y D = surplus π y c D := by
  unfold lender resid surplus E
  have h : ∑ s, π s * min (y s) D + ∑ s, π s * (y s - min (y s) D) = ∑ s, π s * y s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

omit [Fintype S] in
theorem vterm_le {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {D D' : ℝ} (h : D ≤ D') (s : S) :
    (if y s < D then π s else 0) ≤ (if y s < D' then π s else 0) := by
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 h) h2
  · exact hπ s
  · exact le_rfl

theorem vprob_mono {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {D D' : ℝ} (h : D ≤ D') :
    vprob π y D ≤ vprob π y D' :=
  Finset.sum_le_sum fun s _ => vterm_le hπ h s

theorem vprob_strict {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {D D' : ℝ} (h : D ≤ D')
    (hs : ∃ s, D ≤ y s ∧ y s < D' ∧ 0 < π s) : vprob π y D < vprob π y D' := by
  obtain ⟨s, h1, h2, hp⟩ := hs
  refine Finset.sum_lt_sum (fun t _ => vterm_le hπ h t) ⟨s, Finset.mem_univ _, ?_⟩
  rw [ite_eq_right (not_lt.2 h1), ite_eq_left h2]
  exact hp

theorem surplus_anti {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {c : ℝ} (hc : 0 ≤ c) {D D' : ℝ}
    (h : D ≤ D') : surplus π y c D' ≤ surplus π y c D := by
  unfold surplus
  linarith [mul_le_mul_of_nonneg_left (vprob_mono (y := y) hπ h) hc]

theorem surplus_strict {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {c : ℝ} (hc : 0 < c) {D D' : ℝ}
    (h : D ≤ D') (hs : ∃ s, D ≤ y s ∧ y s < D' ∧ 0 < π s) :
    surplus π y c D' < surplus π y c D := by
  unfold surplus
  linarith [mul_lt_mul_of_pos_left (vprob_strict hπ h hs) hc]

theorem resid_anti {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {D D' : ℝ} (h : D ≤ D') :
    resid π y D' ≤ resid π y D := by
  unfold resid E
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hπ s)
  have := min_le_min_left (y s) h
  linarith

/-- The extra repayment from raising the face is nondecreasing in output. -/
theorem step_mono {D D' : ℝ} (h : D ≤ D') {a b : ℝ} (hab : a ≤ b) :
    min a D' - min a D ≤ min b D' - min b D := by
  simp only [min_def]
  split_ifs <;> linarith

theorem resid_diff (π y : S → ℝ) (D D' : ℝ) :
    resid π y D - resid π y D' = E π (fun s => min (y s) D' - min (y s) D) := by
  unfold resid E
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- First-order stochastic dominance: `πH` gives every output-monotone payoff a weakly
larger expectation than `πL`. -/
def FOSD (πH πL y : S → ℝ) : Prop :=
  ∀ g : S → ℝ, (∀ s t, y s ≤ y t → g s ≤ g t) → E πL g ≤ E πH g

theorem gain_anti {πH πL y : S → ℝ} (hF : FOSD πH πL y) {D D' : ℝ} (h : D ≤ D') :
    gain πH πL y D' ≤ gain πH πL y D := by
  have hm : ∀ s t, y s ≤ y t →
      (fun s => min (y s) D' - min (y s) D) s ≤ (fun s => min (y s) D' - min (y s) D) t :=
    fun s t hst => step_mono h hst
  have h1 := hF _ hm
  have eH := resid_diff πH y D D'
  have eL := resid_diff πL y D D'
  unfold gain
  linarith

theorem premium_transfer (π y : S → ℝ) (c D0 D : ℝ) :
    lender π y c D - lender π y c D0 =
      (resid π y D0 - resid π y D) - c * (vprob π y D - vprob π y D0) := by
  have h1 := surplus_split π y c D
  have h2 := surplus_split π y c D0
  unfold surplus at h1 h2
  linarith

theorem lender_gain_le_loss {π y : S → ℝ} (hπ : ∀ s, 0 ≤ π s) {c : ℝ} (hc : 0 ≤ c)
    {D0 D : ℝ} (h : D0 ≤ D) :
    lender π y c D - lender π y c D0 ≤ resid π y D0 - resid π y D := by
  rw [premium_transfer]
  have := mul_nonneg hc (sub_nonneg.2 (vprob_mono (y := y) hπ h))
  linarith

/-- **Capstone.** Let `D0` be a face that returns the lender its principal `I` at zero
return (no time premium), and `D ≥ D0` any face carrying a premium. Then the premium lowers
(weakly) total surplus, the borrower's residual and the borrower's gain from effort; and what
the lender gains is at most what the borrower loses. The debt *shape* is unchanged; the
*premium* buys no surplus and no incentive. -/
theorem zero_premium_dominates {π πH πL y : S → ℝ} (hπ : ∀ s, 0 ≤ π s)
    (hF : FOSD πH πL y) {c I D0 D : ℝ} (hc : 0 ≤ c) (h0 : I ≤ lender π y c D0)
    (h : D0 ≤ D) :
    I ≤ lender π y c D0 ∧
      surplus π y c D ≤ surplus π y c D0 ∧
      resid π y D ≤ resid π y D0 ∧
      gain πH πL y D ≤ gain πH πL y D0 ∧
      lender π y c D - lender π y c D0 ≤ resid π y D0 - resid π y D :=
  ⟨h0, surplus_anti hπ hc h, resid_anti hπ h, gain_anti hF h, lender_gain_le_loss hπ hc h⟩

end ShapeInterest

#print axioms ShapeInterest.surplus_split
#print axioms ShapeInterest.vterm_le
#print axioms ShapeInterest.vprob_mono
#print axioms ShapeInterest.vprob_strict
#print axioms ShapeInterest.surplus_anti
#print axioms ShapeInterest.surplus_strict
#print axioms ShapeInterest.resid_anti
#print axioms ShapeInterest.step_mono
#print axioms ShapeInterest.resid_diff
#print axioms ShapeInterest.gain_anti
#print axioms ShapeInterest.premium_transfer
#print axioms ShapeInterest.lender_gain_le_loss
#print axioms ShapeInterest.zero_premium_dominates
