import Mathlib

/-!
Stage 285: incomplete markets with only equity and debt.

Only two assets are traded: a share of output (payoff `Y s`) and a bond (payoff one in
every state).  A household endowed with the share `e` chooses a share `θ` and a bond
position `b`, consuming `θ * Y s + b`.  Asset prices are those implied by the ownership
state prices: equity `∑ π m(Y) Y`, bond `∑ π m(Y)`.

* `equity_debt_optimal` — keeping the endowed share and trading no bond is optimal;
* `debt_zero_unique` — under the strict supergradient inequality, if output differs
  across two states, it is the ONLY optimal portfolio: `θ = e` and `b = 0`;
* `equity_debt_clears` — shares sum to one and bond positions are all zero.
-/

noncomputable section

open Finset BigOperators

namespace EquityDebt

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **No bond trade is optimal.** -/
theorem equity_debt_optimal (π Y : S → ℝ) (u m h : ℝ → ℝ) (e θ b : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (he : 0 < e)
    (hsg : ∀ c d : ℝ, 0 < c → 0 < d → u c ≤ u d + m d * (c - d))
    (hhom : ∀ y : ℝ, 0 < y → m (e * y) = h e * m y) (hh : 0 ≤ h e)
    (hc : ∀ s, 0 < θ * Y s + b)
    (hbud : θ * (∑ s, π s * m (Y s) * Y s) + b * (∑ s, π s * m (Y s))
      ≤ e * (∑ s, π s * m (Y s) * Y s)) :
    ∑ s, π s * u (θ * Y s + b) ≤ ∑ s, π s * u (e * Y s) := by
  have hterm : ∀ s, π s * u (θ * Y s + b) ≤ π s * u (e * Y s)
      + h e * (π s * m (Y s) * Y s * (θ - e) + π s * m (Y s) * b) := by
    intro s
    have h1 := hsg (θ * Y s + b) (e * Y s) (hc s) (mul_pos he (hY s))
    rw [hhom _ (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    calc π s * u (θ * Y s + b)
        ≤ π s * (u (e * Y s) + h e * m (Y s) * (θ * Y s + b - e * Y s)) := h2
      _ = _ := by ring
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul] at hs
  have h3 : (∑ s, π s * m (Y s) * Y s) * (θ - e) + (∑ s, π s * m (Y s)) * b ≤ 0 := by
    nlinarith [hbud]
  have h4 := mul_nonpos_of_nonneg_of_nonpos hh h3
  linarith

/-- **Zero debt is the unique optimum.** -/
theorem debt_zero_unique (π Y : S → ℝ) (u m h : ℝ → ℝ) (e θ b : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (he : 0 < e)
    (hsg : ∀ c d : ℝ, 0 < c → 0 < d → c ≠ d → u c < u d + m d * (c - d))
    (hhom : ∀ y : ℝ, 0 < y → m (e * y) = h e * m y) (hh : 0 ≤ h e)
    (hc : ∀ s, 0 < θ * Y s + b)
    (hbud : θ * (∑ s, π s * m (Y s) * Y s) + b * (∑ s, π s * m (Y s))
      ≤ e * (∑ s, π s * m (Y s) * Y s))
    (hopt : ∑ s, π s * u (e * Y s) ≤ ∑ s, π s * u (θ * Y s + b))
    (s₁ s₂ : S) (hne : Y s₁ ≠ Y s₂) : θ = e ∧ b = 0 := by
  have hweak : ∀ c d : ℝ, 0 < c → 0 < d → u c ≤ u d + m d * (c - d) := by
    intro c d hc0 hd0
    by_cases hcd : c = d
    · rw [hcd, sub_self, mul_zero, add_zero]
    · exact (hsg c d hc0 hd0 hcd).le
  have hterm : ∀ s, π s * u (θ * Y s + b) ≤ π s * u (e * Y s)
      + h e * (π s * m (Y s) * Y s * (θ - e) + π s * m (Y s) * b) := by
    intro s
    have h1 := hweak (θ * Y s + b) (e * Y s) (hc s) (mul_pos he (hY s))
    rw [hhom _ (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    calc π s * u (θ * Y s + b)
        ≤ π s * (u (e * Y s) + h e * m (Y s) * (θ * Y s + b - e * Y s)) := h2
      _ = _ := by ring
  have hall : ∀ s, θ * Y s + b = e * Y s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s0, hs0⟩ := hcon
    have hst : π s0 * u (θ * Y s0 + b) < π s0 * u (e * Y s0)
        + h e * (π s0 * m (Y s0) * Y s0 * (θ - e) + π s0 * m (Y s0) * b) := by
      have h1 := hsg (θ * Y s0 + b) (e * Y s0) (hc s0) (mul_pos he (hY s0)) hs0
      rw [hhom _ (hY s0)] at h1
      have h2 := mul_lt_mul_of_pos_left h1 (hπ s0)
      calc π s0 * u (θ * Y s0 + b)
          < π s0 * (u (e * Y s0) + h e * m (Y s0) * (θ * Y s0 + b - e * Y s0)) := h2
        _ = _ := by ring
    have hs := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
      ⟨s0, Finset.mem_univ _, hst⟩
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul] at hs
    have h3 : (∑ s, π s * m (Y s) * Y s) * (θ - e) + (∑ s, π s * m (Y s)) * b ≤ 0 := by
      nlinarith [hbud]
    have h4 := mul_nonpos_of_nonneg_of_nonpos hh h3
    linarith
  have h1 := hall s₁
  have h2 := hall s₂
  have hprod : (θ - e) * (Y s₁ - Y s₂) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.1 hprod with h0 | h0
  · have hθ : θ = e := sub_eq_zero.1 h0
    refine ⟨hθ, ?_⟩
    rw [hθ] at h1
    linarith
  · exact absurd (sub_eq_zero.1 h0) hne

omit [Fintype S] in
/-- Asset markets and the goods market clear with no bond outstanding. -/
theorem equity_debt_clears (e : I → ℝ) (Y : S → ℝ) (he : ∑ i, e i = 1) (s : S) :
    ∑ i, (e i * Y s + 0) = Y s ∧ ∑ _i : I, (0 : ℝ) = 0 := by
  refine ⟨?_, Finset.sum_const_zero⟩
  simp only [add_zero]
  rw [← Finset.sum_mul, he, one_mul]

end EquityDebt

end

#print axioms EquityDebt.equity_debt_optimal
#print axioms EquityDebt.debt_zero_unique
#print axioms EquityDebt.equity_debt_clears
