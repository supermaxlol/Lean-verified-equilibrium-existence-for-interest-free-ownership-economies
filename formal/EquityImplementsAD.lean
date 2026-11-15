import Mathlib

/-!
Stage 266: with log utility, the complete-markets equilibrium is pure ownership.

States `S` with probabilities `π`, aggregate output `Y s > 0`, households `I` with
endowments `ω i` summing to `Y` and expected log utility.  At state prices `π s / Y s`
each household's optimal contingent consumption is `w i * Y s`, a fixed share `w i` of
output in every state, the shares sum to one, and every state market clears exactly.  So
the Arrow–Debreu allocation needs no fixed claim: it is a division of ownership.

* `equity_optimal` — the share bundle maximises expected log utility in the budget set;
* `equity_budget` — it costs exactly the household's wealth;
* `shares_sum` — the shares sum to one;
* `equity_equilibrium` — the full statement.
-/

noncomputable section

open Finset BigOperators

namespace EquityImplementsAD

variable {I S : Type*} [Fintype I] [Fintype S]

theorem equity_budget (π Y : S → ℝ) (w : ℝ) (hY : ∀ s, 0 < Y s) (hπ1 : ∑ s, π s = 1) :
    ∑ s, π s / Y s * (w * Y s) = w := by
  have h : ∀ s, π s / Y s * (w * Y s) = w * π s := by
    intro s
    have := (hY s).ne'
    field_simp
  rw [Finset.sum_congr rfl (fun s _ => h s), ← Finset.mul_sum, hπ1, mul_one]

theorem equity_optimal (π Y x : S → ℝ) (w : ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s / Y s * x s ≤ w) :
    ∑ s, π s * Real.log (x s) ≤ ∑ s, π s * Real.log (w * Y s) := by
  have hterm : ∀ s, π s * Real.log (x s)
      ≤ π s * Real.log (w * Y s) + (π s / Y s * x s / w - π s) := by
    intro s
    have hwy : 0 < w * Y s := mul_pos hw (hY s)
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hx s) hwy)
    rw [Real.log_div (hx s).ne' hwy.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
    have e : π s * (x s / (w * Y s) - 1) = π s / Y s * x s / w - π s := by
      have := (hY s).ne'
      have := hw.ne'
      field_simp
    rw [e] at h2
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hπ1] at hsum
  have h3 : (∑ s, π s / Y s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

theorem shares_sum (π Y : S → ℝ) (ω : I → S → ℝ) (hY : ∀ s, 0 < Y s)
    (hπ1 : ∑ s, π s = 1) (hω : ∀ s, ∑ i, ω i s = Y s) :
    ∑ i, ∑ s, π s / Y s * ω i s = 1 := by
  rw [Finset.sum_comm]
  have h : ∀ s, ∑ i, π s / Y s * ω i s = π s := by
    intro s
    rw [← Finset.mul_sum, hω s, div_mul_cancel₀ _ (hY s).ne']
  rw [Finset.sum_congr rfl (fun s _ => h s), hπ1]

/-- **Ownership implements the complete-markets equilibrium.** -/
theorem equity_equilibrium (π Y : S → ℝ) (ω : I → S → ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) [Nonempty S] :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s / Y s * (w i * Y s) = ∑ s, π s / Y s * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s / Y s * x s ≤ ∑ s, π s / Y s * ω i s →
        ∑ s, π s * Real.log (x s) ≤ ∑ s, π s * Real.log (w i * Y s)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s := by
  have hwpos : ∀ i, 0 < ∑ s, π s / Y s * ω i s := fun i =>
    Finset.sum_pos (fun s _ => mul_pos (div_pos (hπ s) (hY s)) (hωpos i s))
      Finset.univ_nonempty
  have hsum := shares_sum π Y ω hY hπ1 hω
  refine ⟨fun i => ∑ s, π s / Y s * ω i s, hwpos, hsum,
    fun i => equity_budget π Y _ hY hπ1,
    fun i x hx hbud => equity_optimal π Y x _ (fun s => (hπ s).le) hπ1 hY (hwpos i) hx hbud,
    fun s => ?_⟩
  rw [← Finset.sum_mul, hsum, one_mul, hω s]

end EquityImplementsAD

end

#print axioms EquityImplementsAD.equity_budget
#print axioms EquityImplementsAD.equity_optimal
#print axioms EquityImplementsAD.shares_sum
#print axioms EquityImplementsAD.equity_equilibrium
