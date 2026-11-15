import Mathlib

/-!
Stage 265: a competitive equilibrium allocation lies in the core.

Exchange economy, households `I`, goods `S`, endowments `ω`, utilities `U`.  At prices
`p ≥ 0` each `x i` is optimal in the budget set `{x ≥ 0 | p · x ≤ p · ω i}`.

* `cost_strict` — a strictly preferred bundle costs strictly more than the endowment;
* `cost_weak` — under semi-strict quasi-concavity and non-satiation, a weakly preferred
  bundle costs at least the endowment;
* `not_blocked` — no coalition can reallocate its own endowments so that every member is
  at least as well off and one member strictly better off;
* `pareto_efficient` — the grand-coalition case.
-/

noncomputable section

open Finset BigOperators

namespace EquilibriumCore

variable {I S : Type*} [Fintype I] [Fintype S]

theorem dot_lin (p a b : S → ℝ) (t : ℝ) :
    ∑ s, p s * ((1 - t) * a s + t * b s)
      = (1 - t) * ∑ s, p s * a s + t * ∑ s, p s * b s := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => by ring)

theorem small_scalar (g a : ℝ) (hg : 0 < g) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * a ≤ g := by
  have hA := abs_nonneg a
  have hden : 0 < |a| + g + 1 := by linarith
  refine ⟨g / (|a| + g + 1), div_pos hg hden, by rw [div_lt_one hden]; linarith, ?_⟩
  have h1 : g / (|a| + g + 1) * a ≤ g / (|a| + g + 1) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) (div_pos hg hden).le
  have h2 : g / (|a| + g + 1) * |a| ≤ g := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [mul_pos hg hg, mul_nonneg hg.le hA]
  linarith

theorem cost_strict (U : (S → ℝ) → ℝ) (p : S → ℝ) (w : ℝ) (x : S → ℝ)
    (hopt : ∀ x' : S → ℝ, (∀ s, 0 ≤ x' s) → ∑ s, p s * x' s ≤ w → U x' ≤ U x)
    (x' : S → ℝ) (hx' : ∀ s, 0 ≤ x' s) (h : U x < U x') : w < ∑ s, p s * x' s := by
  by_contra hc
  exact absurd (hopt x' hx' (le_of_not_gt hc)) (not_le.2 h)

theorem cost_weak (U : (S → ℝ) → ℝ)
    (hss : ∀ a b : S → ℝ, U a < U b → ∀ t : ℝ, 0 < t → t < 1 →
      U a < U (fun s => (1 - t) * a s + t * b s))
    (hns : ∀ a : S → ℝ, (∀ s, 0 ≤ a s) → ∃ b : S → ℝ, (∀ s, 0 ≤ b s) ∧ U a < U b)
    (p : S → ℝ) (w : ℝ) (x : S → ℝ)
    (hopt : ∀ x' : S → ℝ, (∀ s, 0 ≤ x' s) → ∑ s, p s * x' s ≤ w → U x' ≤ U x)
    (x' : S → ℝ) (hx' : ∀ s, 0 ≤ x' s) (h : U x ≤ U x') : w ≤ ∑ s, p s * x' s := by
  by_contra hc
  have hlt : ∑ s, p s * x' s < w := lt_of_not_ge hc
  obtain ⟨b, hb0, hb⟩ := hns x' hx'
  obtain ⟨t, ht0, ht1, ht⟩ :=
    small_scalar (w - ∑ s, p s * x' s) (∑ s, p s * b s - ∑ s, p s * x' s) (by linarith)
  have hz := hss x' b hb t ht0 ht1
  have hbud : ∑ s, p s * ((1 - t) * x' s + t * b s) ≤ w := by
    rw [dot_lin]
    linarith
  have hnn : ∀ s, 0 ≤ (1 - t) * x' s + t * b s :=
    fun s => add_nonneg (mul_nonneg (by linarith) (hx' s)) (mul_nonneg ht0.le (hb0 s))
  have := hopt _ hnn hbud
  linarith

omit [Fintype I] in
/-- **Core property.** No coalition blocks a competitive equilibrium allocation. -/
theorem not_blocked (U : I → (S → ℝ) → ℝ)
    (hss : ∀ i (a b : S → ℝ), U i a < U i b → ∀ t : ℝ, 0 < t → t < 1 →
      U i a < U i (fun s => (1 - t) * a s + t * b s))
    (hns : ∀ i (a : S → ℝ), (∀ s, 0 ≤ a s) → ∃ b : S → ℝ, (∀ s, 0 ≤ b s) ∧ U i a < U i b)
    (ω : I → S → ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (x : I → S → ℝ)
    (hopt : ∀ i (x' : S → ℝ), (∀ s, 0 ≤ x' s) →
      ∑ s, p s * x' s ≤ ∑ s, p s * ω i s → U i x' ≤ U i (x i))
    (C : Finset I) (x' : I → S → ℝ) (hx'0 : ∀ i ∈ C, ∀ s, 0 ≤ x' i s)
    (hfeas : ∀ s, ∑ i ∈ C, x' i s ≤ ∑ i ∈ C, ω i s)
    (hweak : ∀ i ∈ C, U i (x i) ≤ U i (x' i)) :
    ∀ k ∈ C, ¬ U k (x k) < U k (x' k) := by
  intro k hk hlt
  have h1 : ∑ i ∈ C, ∑ s, p s * ω i s < ∑ i ∈ C, ∑ s, p s * x' i s :=
    Finset.sum_lt_sum
      (fun i hi => cost_weak (U i) (hss i) (hns i) p _ (x i) (hopt i) (x' i) (hx'0 i hi)
        (hweak i hi))
      ⟨k, hk, cost_strict (U k) p _ (x k) (hopt k) (x' k) (hx'0 k hk) hlt⟩
  have e1 : ∑ i ∈ C, ∑ s, p s * x' i s = ∑ s, p s * ∑ i ∈ C, x' i s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [Finset.mul_sum])
  have e2 : ∑ i ∈ C, ∑ s, p s * ω i s = ∑ s, p s * ∑ i ∈ C, ω i s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [Finset.mul_sum])
  have h3 : ∑ s, p s * ∑ i ∈ C, x' i s ≤ ∑ s, p s * ∑ i ∈ C, ω i s :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfeas s) (hp s))
  rw [e1, e2] at h1
  linarith

/-- The grand-coalition case: the allocation is Pareto efficient. -/
theorem pareto_efficient (U : I → (S → ℝ) → ℝ)
    (hss : ∀ i (a b : S → ℝ), U i a < U i b → ∀ t : ℝ, 0 < t → t < 1 →
      U i a < U i (fun s => (1 - t) * a s + t * b s))
    (hns : ∀ i (a : S → ℝ), (∀ s, 0 ≤ a s) → ∃ b : S → ℝ, (∀ s, 0 ≤ b s) ∧ U i a < U i b)
    (ω : I → S → ℝ) (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (x : I → S → ℝ)
    (hopt : ∀ i (x' : S → ℝ), (∀ s, 0 ≤ x' s) →
      ∑ s, p s * x' s ≤ ∑ s, p s * ω i s → U i x' ≤ U i (x i))
    (x' : I → S → ℝ) (hx'0 : ∀ i s, 0 ≤ x' i s)
    (hfeas : ∀ s, ∑ i, x' i s ≤ ∑ i, ω i s)
    (hweak : ∀ i, U i (x i) ≤ U i (x' i)) (k : I) : ¬ U k (x k) < U k (x' k) :=
  not_blocked U hss hns ω p hp x hopt Finset.univ x' (fun i _ => hx'0 i) hfeas
    (fun i _ => hweak i) k (Finset.mem_univ k)

end EquilibriumCore

end

#print axioms EquilibriumCore.cost_strict
#print axioms EquilibriumCore.cost_weak
#print axioms EquilibriumCore.not_blocked
#print axioms EquilibriumCore.pareto_efficient
