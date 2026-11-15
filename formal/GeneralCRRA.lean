import Mathlib

/-!
Stage 268: ownership implements the complete-markets equilibrium for homothetic utility.

Generalises stage 266 from log utility to any felicity `u` with a marginal-utility function
`m` that is a supergradient (`u a ≤ u b + m b * (a - b)`) and homogeneous
(`m (w * y) = h w * m y`).  State prices are `π s * m (Y s)`.

* `share_optimal` — the share bundle `w * Y s` maximises expected utility in the budget set;
* `ownership_equilibrium` — shares are positive, sum to one, each household's share bundle
  costs exactly its endowment, is optimal, and every state market clears exactly;
* `log_supergradient`, `log_homogeneous` — log utility satisfies the hypotheses.

The hypotheses are not verified here for power utility.
-/

noncomputable section

open Finset BigOperators

namespace HomotheticOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

theorem share_optimal (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * (w * Y s)) :
    ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w * Y s) := by
  have hterm : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
    intro s
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s))
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
      ring
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have h3 := mul_nonneg hh (sub_nonneg.2 hbud)
  linarith

/-- **Ownership implements the complete-markets equilibrium.** -/
theorem ownership_equilibrium [Nonempty S] (π Y : S → ℝ) (ω : I → S → ℝ) (u m h : ℝ → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s * m (Y s) * (w i * Y s) = ∑ s, π s * m (Y s) * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * ω i s →
        ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w i * Y s)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s := by
  have hp : ∀ s, 0 < π s * m (Y s) := fun s => mul_pos (hπ s) (hm _ (hY s))
  have hT : 0 < ∑ s, π s * m (Y s) * Y s :=
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hY s)) Finset.univ_nonempty
  have hWi : ∀ i, 0 < ∑ s, π s * m (Y s) * ω i s := fun i =>
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hωpos i s)) Finset.univ_nonempty
  have hwpos : ∀ i, 0 < (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s :=
    fun i => div_pos (hWi i) hT
  have htot : ∑ i, ∑ s, π s * m (Y s) * ω i s = ∑ s, π s * m (Y s) * Y s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, hω s])
  have hsum : ∑ i, (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s = 1 := by
    rw [← Finset.sum_div, htot, div_self hT.ne']
  have hcost : ∀ i, ∑ s, π s * m (Y s)
        * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
      = ∑ s, π s * m (Y s) * ω i s := by
    intro i
    have e : ∀ s, π s * m (Y s)
          * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
        = (∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s)
          * (π s * m (Y s) * Y s) := fun s => by ring
    rw [Finset.sum_congr rfl (fun s _ => e s), ← Finset.mul_sum, div_mul_cancel₀ _ hT.ne']
  refine ⟨fun i => (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s, hwpos, hsum,
    hcost, fun i x hx hbud => ?_, fun s => ?_⟩
  · refine share_optimal π Y x u m h _ (fun s => (hπ s).le) hY (hwpos i) hsg
      (fun y hy => hhom _ y (hwpos i) hy) (hh _ (hwpos i)) hx ?_
    rw [hcost i]
    exact hbud
  · rw [← Finset.sum_mul, hsum, one_mul, hω s]

theorem log_supergradient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ Real.log b + 1 / b * (a - b) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have e : 1 / b * (a - b) = a / b - 1 := by
    have := hb.ne'
    field_simp
  rw [e]
  linarith

theorem log_homogeneous (w y : ℝ) (hw : 0 < w) (hy : 0 < y) :
    1 / (w * y) = 1 / w * (1 / y) := by
  have := hw.ne'
  have := hy.ne'
  field_simp

end HomotheticOwnership

end


/-!
Stage 279: every constant-relative-risk-aversion utility satisfies the hypotheses.

For any exponent `p < 1`, `p ≠ 0` (relative risk aversion `1 - p`), the felicity
`u c = (1 / p) * c ^ p` has marginal utility `m y = y ^ (p - 1)`, which is homogeneous with
`h w = w ^ (p - 1)`, and satisfies the supergradient inequality on the positive reals.
Stage 268 therefore applies to the whole CRRA class (the log case is stage 266).
-/

noncomputable section

open Finset BigOperators

namespace GeneralCRRA

/-- Bernoulli from below, negative exponent. -/
theorem bernoulli_neg (p t : ℝ) (hp : p < 0) (ht : 0 < t) : 1 + p * (t - 1) ≤ t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_le_sub_one_of_pos ht
  have h3 : p * (t - 1) ≤ p * Real.log t := mul_le_mul_of_nonpos_left h2 hp.le
  linarith

/-- Strict version away from `t = 1`. -/
theorem bernoulli_neg_strict (p t : ℝ) (hp : p < 0) (ht : 0 < t) (hne : t ≠ 1) :
    1 + p * (t - 1) < t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_lt_sub_one_of_pos ht hne
  have h3 : p * (t - 1) < p * Real.log t := mul_lt_mul_of_neg_left h2 hp
  linarith

/-- Bernoulli from above, exponent between zero and one. -/
theorem bernoulli_pos (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    t ^ p ≤ 1 + p * (t - 1) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hp.le (by linarith : (0 : ℝ) ≤ 1 - p)
    ht.le zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- **Supergradient inequality for CRRA utility.** -/
theorem crra_supergradient (p a b : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    1 / p * a ^ p ≤ 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  have ht : 0 < a / b := div_pos ha hb
  have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hA : a ^ p = (a / b) ^ p * b ^ p := by
    rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
  have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp
  have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp0
  have hkey : (a / b) ^ p * (1 / p) ≤ 1 / p + (a / b - 1) := by
    rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · have hk := bernoulli_neg p (a / b) hneg ht
      have hc : 1 / p < 0 := one_div_neg.2 hneg
      have h := mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
    · have hk := bernoulli_pos p (a / b) hpos hp1 ht
      have hc : 0 < 1 / p := one_div_pos.2 hpos
      have h := mul_nonneg hc.le (sub_nonneg.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
  have h2 := mul_le_mul_of_nonneg_left hkey hB.le
  rw [hA, hm]
  linarith

/-- Strict supergradient when relative risk aversion exceeds one. -/
theorem crra_strict_supergradient (p a b : ℝ) (hp : p < 0) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) : 1 / p * a ^ p < 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  have ht : 0 < a / b := div_pos ha hb
  have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hA : a ^ p = (a / b) ^ p * b ^ p := by
    rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
  have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp
  have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp.ne
  have hne' : a / b ≠ 1 := fun h => hne ((div_eq_one_iff_eq hb.ne').1 h)
  have hk := bernoulli_neg_strict p (a / b) hp ht hne'
  have hc : 1 / p < 0 := one_div_neg.2 hp
  have h := mul_pos_of_neg_of_neg hc (sub_neg.2 hk)
  have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
      = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
  rw [e, hpc, one_mul] at h
  have h2 := mul_lt_mul_of_pos_left (by linarith : (a / b) ^ p * (1 / p) < 1 / p + (a / b - 1)) hB
  rw [hA, hm]
  linarith

theorem crra_homogeneous (p w y : ℝ) (hw : 0 < w) (hy : 0 < y) :
    (w * y) ^ (p - 1) = w ^ (p - 1) * y ^ (p - 1) := Real.mul_rpow hw.le hy.le

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Ownership equilibrium for every CRRA utility.** -/
theorem crra_ownership_equilibrium [Nonempty S] (p : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0)
    (π Y : S → ℝ) (ω : I → S → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s * Y s ^ (p - 1) * (w i * Y s) = ∑ s, π s * Y s ^ (p - 1) * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s * Y s ^ (p - 1) * x s ≤ ∑ s, π s * Y s ^ (p - 1) * ω i s →
        ∑ s, π s * (1 / p * x s ^ p) ≤ ∑ s, π s * (1 / p * (w i * Y s) ^ p)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s :=
  HomotheticOwnership.ownership_equilibrium π Y ω (fun c => 1 / p * c ^ p)
    (fun y => y ^ (p - 1)) (fun w => w ^ (p - 1)) hπ hY hωpos hω
    (fun _ hy => Real.rpow_pos_of_pos hy _)
    (fun a b ha hb => crra_supergradient p a b hp1 hp0 ha hb)
    (fun w y hw hy => crra_homogeneous p w y hw hy)
    (fun _ hw => (Real.rpow_pos_of_pos hw _).le)

end GeneralCRRA

end

#print axioms GeneralCRRA.bernoulli_neg
#print axioms GeneralCRRA.bernoulli_neg_strict
#print axioms GeneralCRRA.bernoulli_pos
#print axioms GeneralCRRA.crra_supergradient
#print axioms GeneralCRRA.crra_strict_supergradient
#print axioms GeneralCRRA.crra_homogeneous
#print axioms GeneralCRRA.crra_ownership_equilibrium
