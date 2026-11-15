import Mathlib

/-!
Stage 295: boundary allocations for log and CRRA with `p < 0`.

These felicities are `-∞` at zero.  Lean's real `log 0` and `0 ^ p` are junk finite values,
so the boundary is handled with an extended-value utility in `EReal` that equals `⊥` off the
strictly positive orthant.

* `log_blowup`, `crra_neg_blowup` — `log c` and `c ^ p / p` (`p < 0`) fall below every bound
  as `c → 0⁺`: `⊥` is the true limit, not a convention.
* `ext_optimum_interior` — for any felicity, an optimum of the extended utility over
  non-negative affordable bundles is strictly positive in every state.
* `log_optimum` — with log felicity the optimum exists and is the interior bundle
  `c s = π s * W / q s`.
-/

noncomputable section

open Finset

namespace BoundaryExtended

theorem log_blowup (M : ℝ) : ∃ δ > 0, ∀ c, 0 < c → c < δ → Real.log c < -M := by
  refine ⟨Real.exp (-M), Real.exp_pos _, fun c hc hcδ => ?_⟩
  have := Real.log_lt_log hc hcδ
  rwa [Real.log_exp] at this

theorem crra_neg_blowup (p M : ℝ) (hp : p < 0) :
    ∃ δ > 0, ∀ c, 0 < c → c ≤ δ → 1 / p * c ^ p < -M := by
  set m := max M 0 with hm
  set K := m * (-p) + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ m * (-p) := mul_nonneg (le_max_right _ _) (by linarith)
    linarith
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hK0 _, fun c hc hcδ => ?_⟩
  have h1 : (K ^ (1 / p)) ^ p ≤ c ^ p := Real.rpow_le_rpow_of_nonpos hc hcδ hp.le
  have h2 : (K ^ (1 / p)) ^ p = K := by
    rw [← Real.rpow_mul hK0.le, one_div_mul_cancel hp.ne, Real.rpow_one]
  rw [h2] at h1
  have hinv : 1 / p < 0 := by rw [one_div]; exact inv_lt_zero.2 hp
  have h3 : 1 / p * c ^ p ≤ 1 / p * K := mul_le_mul_of_nonpos_left h1 hinv.le
  have h4 : 1 / p * K = -m + 1 / p := by
    rw [hK, mul_add, mul_one]
    have : 1 / p * (m * -p) = -m := by
      rw [one_div, mul_comm m, neg_mul, mul_neg, ← mul_assoc, inv_mul_cancel₀ hp.ne, one_mul]
    rw [this]
  have h5 : M ≤ m := le_max_left _ _
  linarith

variable {S : Type*} [Fintype S]

/-- Extended expected utility: `⊥` unless every coordinate is strictly positive. -/
def ext (u : ℝ → ℝ) (π c : S → ℝ) : EReal :=
  if ∀ s, 0 < c s then ((∑ s, π s * u (c s) : ℝ) : EReal) else ⊥

/-- **Optima are interior.** -/
theorem ext_optimum_interior [Nonempty S] (u : ℝ → ℝ) (π q c : S → ℝ) (W : ℝ)
    (hq : ∀ s, 0 < q s) (hW : 0 < W)
    (hopt : ∀ d : S → ℝ, (∀ s, 0 ≤ d s) → ∑ s, q s * d s ≤ W → ext u π d ≤ ext u π c) :
    ∀ s, 0 < c s := by
  by_contra hc
  have hcb : ext u π c = ⊥ := by unfold ext; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  have hQ : 0 < ∑ s, q s := Finset.sum_pos (fun s _ => hq s) univ_nonempty
  set d : S → ℝ := fun _ => W / ∑ s, q s with hd
  have hdpos : ∀ s, 0 < d s := fun _ => div_pos hW hQ
  have hdb : ∑ s, q s * d s ≤ W := by
    rw [hd, ← Finset.sum_mul]
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hQ.ne']
  have h := hopt d (fun s => (hdpos s).le) hdb
  rw [hcb, le_bot_iff] at h
  unfold ext at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hdpos)] at h
  exact EReal.coe_ne_bot _ h

/-- **Log felicity: the optimum is the interior bundle `π s * W / q s`.** -/
theorem log_optimum (π q : S → ℝ) (W : ℝ) (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    (hq : ∀ s, 0 < q s) (hW : 0 < W) :
    (∀ s, 0 < π s * W / q s) ∧ ∑ s, q s * (π s * W / q s) = W ∧
    ∀ d : S → ℝ, (∀ s, 0 ≤ d s) → ∑ s, q s * d s ≤ W →
      ext Real.log π d ≤ ext Real.log π (fun s => π s * W / q s) := by
  have hc : ∀ s, 0 < π s * W / q s := fun s => div_pos (mul_pos (hπ s) hW) (hq s)
  refine ⟨hc, ?_, fun d hd0 hdb => ?_⟩
  · have : ∀ s, q s * (π s * W / q s) = π s * W := fun s => by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (hq s).ne']
    simp only [this, ← Finset.sum_mul, hπ1, one_mul]
  by_cases hd : ∀ s, 0 < d s
  · unfold ext
    rw [ite_eq_left_of_eq_true _ _ (eq_true hd), ite_eq_left_of_eq_true _ _ (eq_true hc), EReal.coe_le_coe_iff]
    have key : ∀ s, π s * Real.log (d s) ≤
        π s * Real.log (π s * W / q s) + (q s * d s / W - π s) := by
      intro s
      have hcs := hc s
      have h1 := Real.log_le_sub_one_of_pos (div_pos (hd s) hcs)
      rw [Real.log_div (hd s).ne' hcs.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
      have h3 : π s * (d s / (π s * W / q s)) = q s * d s / W := by
        have := (hπ s).ne'; have := (hq s).ne'; have := hW.ne'
        field_simp
      nlinarith
    have hs := Finset.sum_le_sum fun s (_ : s ∈ univ) => key s
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hπ1] at hs
    have : (∑ s, q s * d s) / W ≤ 1 := (div_le_one hW).2 hdb
    linarith
  · unfold ext
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact bot_le

end BoundaryExtended

end

#print axioms BoundaryExtended.log_blowup
#print axioms BoundaryExtended.crra_neg_blowup
#print axioms BoundaryExtended.ext_optimum_interior
#print axioms BoundaryExtended.log_optimum
