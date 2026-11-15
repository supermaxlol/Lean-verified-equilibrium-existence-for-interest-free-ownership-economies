import Mathlib

/-!
Stage 314: Stiglitz–Weiss screening without interest.

Borrower types share a mean output `μ` but differ in risk.  Each type `t` has a distribution
`π t` over finitely many states with output `y`.  A safe type has output `μ` for sure.

Debt at face `R` (Stiglitz–Weiss):
* `debt_borrower_ge`: every type's payoff `E max(y − R, 0)` is at least the safe type's
  `max(μ − R, 0)`; risk-takers value debt more (limited liability makes the payoff convex).
* `debt_lender_le`: the lender's repayment `E min(y, R)` from any type is at most the safe type's
  `min(μ, R)`.
* `safe_exits_first`: as `R` rises, if the safe type still borrows, so does every riskier type.
* `sw_example`: raising `R` from 0.9 to 1.0 drives out the safe type and *lowers* the lender's
  return (0.675 → 0.5).  The interest rate cannot clear the market; this is credit rationing.

Profit sharing at share `θ`:
* `ps_payoff`: every type's payoff is `(1 − θ)·μ`, and the lender's take is `θ·μ`.
* `ps_no_selection`: participation is identical across types with the same mean, so raising `θ`
  never changes the risk composition of the pool.
* `ps_pool_return`: for any mix of types the lender's average return is exactly `θ·μ`, so it is
  increasing in `θ` (`ps_pool_mono`).  The Stiglitz–Weiss adverse-selection channel is absent.

Honest limits: screening is on risk with equal means.  Profit sharing does select on the mean
(high-mean types prefer debt, Myers–Majluf), and it needs verification (stages 301, 308, 313).
-/

open Finset BigOperators

noncomputable section

namespace Screening

variable {Ω : Type*} [Fintype Ω]

def Ex (π y : Ω → ℝ) : ℝ := ∑ ω, π ω * y ω

theorem debt_borrower_ge (π y : Ω → ℝ) (R μ : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (h1 : ∑ ω, π ω = 1)
    (hμ : Ex π y = μ) : max (μ - R) 0 ≤ Ex π (fun ω => max (y ω - R) 0) := by
  apply max_le
  · have h : Ex π (fun ω => y ω - R) = μ - R := by
      unfold Ex at hμ ⊢
      rw [Finset.sum_congr rfl fun ω _ => mul_sub (π ω) (y ω) R, Finset.sum_sub_distrib,
        ← Finset.sum_mul, h1, one_mul, hμ]
    rw [← h]
    exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hπ ω)
  · exact Finset.sum_nonneg fun ω _ => mul_nonneg (hπ ω) (le_max_right _ _)

theorem debt_lender_le (π y : Ω → ℝ) (R μ : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (h1 : ∑ ω, π ω = 1)
    (hμ : Ex π y = μ) : Ex π (fun ω => min (y ω) R) ≤ min μ R := by
  apply le_min
  · rw [← hμ]
    exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hπ ω)
  · have h : Ex π (fun _ => R) = R := by
      unfold Ex; rw [← Finset.sum_mul, h1, one_mul]
    calc Ex π (fun ω => min (y ω) R) ≤ Ex π (fun _ => R) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hπ ω)
      _ = R := h

/-- **The safe type exits first.** -/
theorem safe_exits_first (π y : Ω → ℝ) (R μ u0 : ℝ) (hπ : ∀ ω, 0 ≤ π ω)
    (h1 : ∑ ω, π ω = 1) (hμ : Ex π y = μ) (hsafe : u0 ≤ max (μ - R) 0) :
    u0 ≤ Ex π (fun ω => max (y ω - R) 0) :=
  hsafe.trans (debt_borrower_ge π y R μ hπ h1 hμ)

/-- **A Stiglitz–Weiss example.**  Safe type: output 1.  Risky type: 0 or 2 with probability ½.
Outside option 0.05.  At `R = 0.9` both borrow and the lender's average return over an equal mix is
0.675.  At `R = 1` the safe type's payoff 0 is below 0.05 and it exits; the lender gets 0.5. -/
theorem sw_example :
    -- at R = 0.9 both participate
    (0.05 : ℝ) ≤ max (1 - 0.9) 0 ∧ (0.05 : ℝ) ≤ (1/2) * max (2 - 0.9) 0 + (1/2) * max (0 - 0.9) 0 ∧
    -- pooled lender return at R = 0.9
    (1/2 : ℝ) * min 1 0.9 + (1/2) * ((1/2) * min 2 0.9 + (1/2) * min 0 0.9) = 0.675 ∧
    -- at R = 1 the safe type exits, the risky type stays
    ¬ ((0.05 : ℝ) ≤ max (1 - 1) 0) ∧ (0.05 : ℝ) ≤ (1/2) * max (2 - 1) 0 + (1/2) * max (0 - 1) 0 ∧
    -- lender return at R = 1 from the remaining pool
    (1/2 : ℝ) * min 2 1 + (1/2) * min 0 1 = 0.5 ∧ (0.5 : ℝ) < 0.675 := by
  norm_num

/-- **Profit sharing pays every type by the mean.** -/
theorem ps_payoff (π y : Ω → ℝ) (θ μ : ℝ) (hμ : Ex π y = μ) :
    Ex π (fun ω => (1 - θ) * y ω) = (1 - θ) * μ ∧ Ex π (fun ω => θ * y ω) = θ * μ := by
  unfold Ex at hμ ⊢
  constructor
  · rw [Finset.sum_congr rfl fun ω _ => (by ring : π ω * ((1 - θ) * y ω) = (1 - θ) * (π ω * y ω)),
      ← Finset.mul_sum, hμ]
  · rw [Finset.sum_congr rfl fun ω _ => (by ring : π ω * (θ * y ω) = θ * (π ω * y ω)),
      ← Finset.mul_sum, hμ]

/-- **No selection on risk under profit sharing.** -/
theorem ps_no_selection (π π' y : Ω → ℝ) (θ μ u0 : ℝ) (hμ : Ex π y = μ) (hμ' : Ex π' y = μ) :
    u0 ≤ Ex π (fun ω => (1 - θ) * y ω) ↔ u0 ≤ Ex π' (fun ω => (1 - θ) * y ω) := by
  rw [(ps_payoff π y θ μ hμ).1, (ps_payoff π' y θ μ hμ').1]

/-- **The lender's pooled return under profit sharing is `θ μ` for any mix of types.** -/
theorem ps_pool_return {T : Type*} [Fintype T] (π : T → Ω → ℝ) (y : Ω → ℝ) (w : T → ℝ)
    (θ μ : ℝ) (hw : ∑ t, w t = 1) (hμ : ∀ t, Ex (π t) y = μ) :
    ∑ t, w t * Ex (π t) (fun ω => θ * y ω) = θ * μ := by
  rw [Finset.sum_congr rfl fun t _ => by rw [(ps_payoff (π t) y θ μ (hμ t)).2],
    ← Finset.sum_mul, hw, one_mul]

theorem ps_pool_mono {T : Type*} [Fintype T] (π : T → Ω → ℝ) (y : Ω → ℝ) (w : T → ℝ)
    (θ θ' μ : ℝ) (hw : ∑ t, w t = 1) (hμ : ∀ t, Ex (π t) y = μ) (hμ0 : 0 ≤ μ) (hθ : θ ≤ θ') :
    ∑ t, w t * Ex (π t) (fun ω => θ * y ω) ≤ ∑ t, w t * Ex (π t) (fun ω => θ' * y ω) := by
  rw [ps_pool_return π y w θ μ hw hμ, ps_pool_return π y w θ' μ hw hμ]
  exact mul_le_mul_of_nonneg_right hθ hμ0

end Screening

end

#print axioms Screening.debt_borrower_ge
#print axioms Screening.debt_lender_le
#print axioms Screening.safe_exits_first
#print axioms Screening.sw_example
#print axioms Screening.ps_payoff
#print axioms Screening.ps_no_selection
#print axioms Screening.ps_pool_return
#print axioms Screening.ps_pool_mono
