import Mathlib

/-!
Stage 283: households with different risk tolerance (exponential utility).

Household `i` has felicity `-τ i * exp (-c / τ i)` with risk tolerance `τ i > 0`; the
tolerances may all differ.  Let `T = ∑ τ`.

* `cara_supergradient` — the supergradient inequality;
* `cara_optimal` — at the prices `π s * exp (-Y s / T)` the bundle `τ / T * Y s + k` is
  optimal among ALL bundles costing no more;
* `cara_clears` — if the constants `k i` sum to zero the bundles use exactly output.

So each household holds a share of output equal to its share of total risk tolerance,
plus a state-independent payment, and the payments sum to zero.
-/

noncomputable section

open Finset BigOperators

namespace CARASharing

variable {I S : Type*} [Fintype I] [Fintype S]

theorem cara_supergradient (τ c b : ℝ) (hτ : 0 < τ) :
    -τ * Real.exp (-c / τ) ≤ -τ * Real.exp (-b / τ) + Real.exp (-b / τ) * (c - b) := by
  have h := Real.add_one_le_exp (-(c - b) / τ)
  have e : Real.exp (-c / τ) = Real.exp (-b / τ) * Real.exp (-(c - b) / τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 0 < Real.exp (-b / τ) := Real.exp_pos _
  have e2 : τ * (-(c - b) / τ + 1) = τ - (c - b) := by
    have h0 := div_mul_cancel₀ (-(c - b)) hτ.ne'
    linear_combination h0
  have h1 := mul_le_mul_of_nonneg_left h hτ.le
  rw [e2] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hE.le
  rw [e]
  linarith

/-- **Optimal bundle with exponential utility.** -/
theorem cara_optimal (π Y x' : S → ℝ) (τ T k : ℝ) (hπ : ∀ s, 0 < π s) (hτ : 0 < τ)
    (hT : 0 < T)
    (hbud : ∑ s, π s * Real.exp (-(Y s) / T) * x' s
      ≤ ∑ s, π s * Real.exp (-(Y s) / T) * (τ / T * Y s + k)) :
    ∑ s, π s * (-τ * Real.exp (-(x' s) / τ))
      ≤ ∑ s, π s * (-τ * Real.exp (-(τ / T * Y s + k) / τ)) := by
  have hc0 : 0 ≤ Real.exp (-k / τ) := (Real.exp_pos _).le
  have hterm : ∀ s, π s * (-τ * Real.exp (-(x' s) / τ))
      ≤ π s * (-τ * Real.exp (-(τ / T * Y s + k) / τ))
        + Real.exp (-k / τ) * (π s * Real.exp (-(Y s) / T) * x' s
          - π s * Real.exp (-(Y s) / T) * (τ / T * Y s + k)) := by
    intro s
    have h1 := cara_supergradient τ (x' s) (τ / T * Y s + k) hτ
    have hEb : Real.exp (-(τ / T * Y s + k) / τ)
        = Real.exp (-k / τ) * Real.exp (-(Y s) / T) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    calc π s * (-τ * Real.exp (-(x' s) / τ))
        ≤ π s * (-τ * Real.exp (-(τ / T * Y s + k) / τ)
            + Real.exp (-(τ / T * Y s + k) / τ) * (x' s - (τ / T * Y s + k))) := h2
      _ = π s * (-τ * Real.exp (-(τ / T * Y s + k) / τ))
            + π s * (Real.exp (-(τ / T * Y s + k) / τ) * (x' s - (τ / T * Y s + k))) := by
          ring
      _ = _ := by rw [hEb]; ring
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  have h3 := mul_nonpos_of_nonneg_of_nonpos hc0 (sub_nonpos.2 hbud)
  linarith

/-- The bundles use exactly output. -/
theorem cara_clears (τ k : I → ℝ) (y : ℝ) (hT : 0 < ∑ i, τ i) (hk : ∑ i, k i = 0) :
    ∑ i, (τ i / (∑ j, τ j) * y + k i) = y := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, div_self hT.ne', hk]
  ring

end CARASharing

end

#print axioms CARASharing.cara_supergradient
#print axioms CARASharing.cara_optimal
#print axioms CARASharing.cara_clears
