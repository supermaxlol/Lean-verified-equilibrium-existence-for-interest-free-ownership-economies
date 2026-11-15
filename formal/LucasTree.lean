import Mathlib

/-!
Stage 286: dynamic ownership (Lucas tree, log utility, Markov output).

Finitely many states `S`, transition weights `π s s'` summing to one, output `Y s > 0`,
discount `0 < β < 1`.  One asset: the claim to all future output, price
`p s = β / (1 - β) * Y s`.

* `tree_price_euler` — the price satisfies the Euler equation
  `p s / Y s = β * ∑ π s s' * (p s' + Y s') / Y s'`;
* `hold_bellman` — for any consumption `c` and next-period share `θ'` affordable from the
  share `θ`, `log c + β/(1-β) * log θ' ≤ log θ / (1-β) + log (Y s)`;
* `hold_bellman_eq` — equality at `c = θ * Y s`, `θ' = θ`;
* `tree_bellman`, `tree_bellman_eq` — with `V θ s = log θ / (1 - β) + v s`, where `v`
  solves `v s = log (Y s) + β * ∑ π s s' * v s'`, the Bellman inequality holds for every
  affordable choice and holding the share forever attains it;
* `tree_clears` — constant shares summing to one consume exactly output.
-/

noncomputable section

open Finset BigOperators

namespace LucasTree

variable {I S : Type*} [Fintype I] [Fintype S]

theorem tree_price_euler (β : ℝ) (π : S → S → ℝ) (Y : S → ℝ) (hβ1 : β < 1)
    (hsum : ∀ s, ∑ s', π s s' = 1) (hY : ∀ s, 0 < Y s) (s : S) :
    β / (1 - β) * Y s / Y s
      = β * ∑ s', π s s' * ((β / (1 - β) * Y s' + Y s') / Y s') := by
  have h1β : (1 - β) ≠ 0 := by linarith
  have e : ∀ s', π s s' * ((β / (1 - β) * Y s' + Y s') / Y s') = π s s' * (1 / (1 - β)) := by
    intro s'
    have := (hY s').ne'
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun s' _ => e s'), ← Finset.sum_mul, hsum, one_mul]
  have := (hY s).ne'
  field_simp

theorem hold_bellman (β θ θ' c y : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hθ' : 0 < θ') (hc : 0 < c) (hy : 0 < y)
    (hbud : c + β / (1 - β) * y * θ' ≤ θ * (β / (1 - β) * y + y)) :
    Real.log c + β / (1 - β) * Real.log θ' ≤ Real.log θ / (1 - β) + Real.log y := by
  have h1β : 0 < 1 - β := by linarith
  have hB : 0 ≤ β / (1 - β) := (div_pos hβ h1β).le
  have hB1 : β / (1 - β) + 1 = 1 / (1 - β) := by field_simp; ring
  have hθy : 0 < θ * y := mul_pos hθ hy
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hθy)
  rw [Real.log_div hc.ne' hθy.ne', Real.log_mul hθ.ne' hy.ne'] at h1
  have h2 := Real.log_le_sub_one_of_pos (div_pos hθ' hθ)
  rw [Real.log_div hθ'.ne' hθ.ne'] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hB
  have e3 : θ * (β / (1 - β) * y + y) = (β / (1 - β) + 1) * (θ * y) := by ring
  rw [e3, hB1] at hbud
  have ekey : c / (θ * y) + β / (1 - β) * (θ' / θ) = (c + β / (1 - β) * y * θ') / (θ * y) := by
    have := hθ.ne'
    have := hy.ne'
    field_simp
  have key : c / (θ * y) + β / (1 - β) * (θ' / θ) ≤ 1 / (1 - β) := by
    rw [ekey, div_le_iff₀ hθy]
    exact hbud
  have e4 : Real.log θ / (1 - β) = (β / (1 - β) + 1) * Real.log θ := by
    rw [hB1]; ring
  rw [e4]
  linarith

theorem hold_bellman_eq (β θ y : ℝ) (hβ1 : β < 1) (hθ : 0 < θ) (hy : 0 < y) :
    Real.log (θ * y) + β / (1 - β) * Real.log θ = Real.log θ / (1 - β) + Real.log y := by
  have h1β : (1 - β) ≠ 0 := by linarith
  have hB1 : β / (1 - β) + 1 = 1 / (1 - β) := by field_simp; ring
  have e4 : Real.log θ / (1 - β) = (β / (1 - β) + 1) * Real.log θ := by
    rw [hB1]; ring
  rw [Real.log_mul hθ.ne' hy.ne', e4]
  ring

/-- **Bellman inequality: no affordable choice beats holding the share.** -/
theorem tree_bellman (β : ℝ) (π : S → S → ℝ) (Y v : S → ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hsum : ∀ s, ∑ s', π s s' = 1) (hY : ∀ s, 0 < Y s)
    (hv : ∀ s, v s = Real.log (Y s) + β * ∑ s', π s s' * v s')
    (s : S) (θ θ' c : ℝ) (hθ : 0 < θ) (hθ' : 0 < θ') (hc : 0 < c)
    (hbud : c + β / (1 - β) * Y s * θ' ≤ θ * (β / (1 - β) * Y s + Y s)) :
    Real.log c + β * ∑ s', π s s' * (Real.log θ' / (1 - β) + v s')
      ≤ Real.log θ / (1 - β) + v s := by
  have e : ∑ s', π s s' * (Real.log θ' / (1 - β) + v s')
      = Real.log θ' / (1 - β) + ∑ s', π s s' * v s' := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hb := hold_bellman β θ θ' c (Y s) hβ hβ1 hθ hθ' hc (hY s) hbud
  have e5 : β * (Real.log θ' / (1 - β)) = β / (1 - β) * Real.log θ' := by ring
  have hvs := hv s
  rw [e]
  linarith

/-- Holding the share attains the Bellman value. -/
theorem tree_bellman_eq (β : ℝ) (π : S → S → ℝ) (Y v : S → ℝ) (hβ1 : β < 1)
    (hsum : ∀ s, ∑ s', π s s' = 1) (hY : ∀ s, 0 < Y s)
    (hv : ∀ s, v s = Real.log (Y s) + β * ∑ s', π s s' * v s')
    (s : S) (θ : ℝ) (hθ : 0 < θ) :
    Real.log (θ * Y s) + β * ∑ s', π s s' * (Real.log θ / (1 - β) + v s')
      = Real.log θ / (1 - β) + v s := by
  have e : ∑ s', π s s' * (Real.log θ / (1 - β) + v s')
      = Real.log θ / (1 - β) + ∑ s', π s s' * v s' := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hb := hold_bellman_eq β θ (Y s) hβ1 hθ (hY s)
  have e5 : β * (Real.log θ / (1 - β)) = β / (1 - β) * Real.log θ := by ring
  have hvs := hv s
  rw [e]
  linarith

omit [Fintype S] in
theorem tree_clears (θ : I → ℝ) (Y : S → ℝ) (hθ : ∑ i, θ i = 1) (s : S) :
    ∑ i, θ i * Y s = Y s := by
  rw [← Finset.sum_mul, hθ, one_mul]

end LucasTree

end

#print axioms LucasTree.tree_price_euler
#print axioms LucasTree.hold_bellman
#print axioms LucasTree.hold_bellman_eq
#print axioms LucasTree.tree_bellman
#print axioms LucasTree.tree_bellman_eq
#print axioms LucasTree.tree_clears
