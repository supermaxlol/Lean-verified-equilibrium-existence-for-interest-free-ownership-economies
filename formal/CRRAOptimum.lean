import Mathlib

/-!
Stage 298: CRRA optimum in closed form for every `p < 1`, `p ≠ 0`.

With extended utility (`⊥` off the positive orthant, as in stage 295), the bundle
`c s = W / (∑ t, q t * r t) * r s`, `r s = (π s / q s) ^ (1 / (1 - p))`, is optimal among all
non-negative affordable bundles.  For `p < 0` this is the honest model (`c ^ p / p → -∞` at 0).
For `0 < p < 1`, `power_optimum` proves the same bundle optimal against all non-negative
bundles with the real-valued utility, zeros included.
-/

noncomputable section

open Finset

namespace CRRAOptimum

theorem bernoulli_neg (p t : ℝ) (hp : p < 0) (ht : 0 < t) : 1 + p * (t - 1) ≤ t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_le_sub_one_of_pos ht
  have h3 : p * (t - 1) ≤ p * Real.log t := mul_le_mul_of_nonpos_left h2 hp.le
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

theorem power_sg_nonneg (p c d : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 ≤ c) (hd : 0 < d) :
    1 / p * c ^ p ≤ 1 / p * d ^ p + d ^ (p - 1) * (c - d) := by
  rcases hc.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow hp0.ne', mul_zero, zero_sub, Real.rpow_sub_one hd.ne']
    have hD : 0 < d ^ p := Real.rpow_pos_of_pos hd p
    have e : d ^ p / d * -d = - d ^ p := by field_simp
    rw [e]
    have h1 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    nlinarith
  · exact crra_supergradient p c d hp1 hp0.ne' h hd

variable {S : Type*} [Fintype S]

/-- Extended expected utility: `⊥` unless every coordinate is strictly positive. -/
def ext (u : ℝ → ℝ) (π c : S → ℝ) : EReal :=
  if ∀ s, 0 < c s then ((∑ s, π s * u (c s) : ℝ) : EReal) else ⊥

def rr (p : ℝ) (π q : S → ℝ) (s : S) : ℝ := (π s / q s) ^ (1 / (1 - p))

def copt (p W : ℝ) (π q : S → ℝ) (s : S) : ℝ := W / (∑ t, q t * rr p π q t) * rr p π q s

theorem copt_props [Nonempty S] (p W : ℝ) (π q : S → ℝ) (hp1 : p < 1)
    (hπ : ∀ s, 0 < π s) (hq : ∀ s, 0 < q s) (hW : 0 < W) :
    (∀ s, 0 < copt p W π q s) ∧ ∑ s, q s * copt p W π q s = W ∧
    ∀ s, π s * copt p W π q s ^ (p - 1) = (W / ∑ t, q t * rr p π q t) ^ (p - 1) * q s := by
  have hr : ∀ s, 0 < rr p π q s := fun s => Real.rpow_pos_of_pos (div_pos (hπ s) (hq s)) _
  have hQ : 0 < ∑ t, q t * rr p π q t :=
    Finset.sum_pos (fun t _ => mul_pos (hq t) (hr t)) univ_nonempty
  set A := W / ∑ t, q t * rr p π q t with hA
  have hA0 : 0 < A := div_pos hW hQ
  refine ⟨fun s => mul_pos hA0 (hr s), ?_, fun s => ?_⟩
  · have e : ∑ s, q s * copt p W π q s = A * ∑ s, q s * rr p π q s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by simp only [copt, ← hA]; ring
    rw [e, hA, div_mul_cancel₀ W hQ.ne']
  · have h1 : copt p W π q s ^ (p - 1) = A ^ (p - 1) * rr p π q s ^ (p - 1) := by
      simp only [copt, ← hA]
      exact Real.mul_rpow hA0.le (hr s).le
    have hne : (1 - p) ≠ 0 := by linarith
    have hexp : 1 / (1 - p) * (p - 1) = -1 := by
      have : 1 / (1 - p) * (p - 1) = -((1 - p) / (1 - p)) := by ring
      rw [this, div_self hne]
    have h2 : rr p π q s ^ (p - 1) = q s / π s := by
      simp only [rr]
      rw [← Real.rpow_mul (div_pos (hπ s) (hq s)).le, hexp, Real.rpow_neg_one, inv_div]
    rw [h1, h2, mul_left_comm, mul_div_assoc', mul_div_cancel_left₀ _ (hπ s).ne']

/-- **CRRA optimum, extended utility** (`p < 1`, `p ≠ 0`; the honest model for `p < 0`). -/
theorem crra_optimum [Nonempty S] (p W : ℝ) (π q : S → ℝ) (hp1 : p < 1) (hp0 : p ≠ 0)
    (hπ : ∀ s, 0 < π s) (hq : ∀ s, 0 < q s) (hW : 0 < W) :
    (∀ s, 0 < copt p W π q s) ∧ ∑ s, q s * copt p W π q s = W ∧
    ∀ d : S → ℝ, (∀ s, 0 ≤ d s) → ∑ s, q s * d s ≤ W →
      ext (fun x => 1 / p * x ^ p) π d ≤ ext (fun x => 1 / p * x ^ p) π (copt p W π q) := by
  obtain ⟨hc, hb, hfoc⟩ := copt_props p W π q hp1 hπ hq hW
  refine ⟨hc, hb, fun d _ hdb => ?_⟩
  set A' := (W / ∑ t, q t * rr p π q t) ^ (p - 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have hr : ∀ s, 0 < rr p π q s := fun s => Real.rpow_pos_of_pos (div_pos (hπ s) (hq s)) _
    have hQ : 0 < ∑ t, q t * rr p π q t :=
      Finset.sum_pos (fun t _ => mul_pos (hq t) (hr t)) univ_nonempty
    exact (Real.rpow_pos_of_pos (div_pos hW hQ) _).le
  by_cases hd : ∀ s, 0 < d s
  · unfold ext
    rw [ite_eq_left_of_eq_true _ _ (eq_true hd), ite_eq_left_of_eq_true _ _ (eq_true hc),
      EReal.coe_le_coe_iff]
    show ∑ s, π s * (1 / p * d s ^ p) ≤ ∑ s, π s * (1 / p * copt p W π q s ^ p)
    have key : ∀ s, π s * (1 / p * d s ^ p) ≤
        π s * (1 / p * copt p W π q s ^ p) + A' * q s * (d s - copt p W π q s) := by
      intro s
      have h1 := crra_supergradient p (d s) (copt p W π q s) hp1 hp0 (hd s) (hc s)
      have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
      have e : π s * (1 / p * copt p W π q s ^ p +
            copt p W π q s ^ (p - 1) * (d s - copt p W π q s)) =
          π s * (1 / p * copt p W π q s ^ p) +
            (π s * copt p W π q s ^ (p - 1)) * (d s - copt p W π q s) := by ring
      rw [e, hfoc s] at h2
      exact h2
    have hs := Finset.sum_le_sum fun s (_ : s ∈ univ) => key s
    rw [Finset.sum_add_distrib] at hs
    have e2 : ∑ s, A' * q s * (d s - copt p W π q s) =
        A' * ∑ s, q s * d s - A' * ∑ s, q s * copt p W π q s := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e2, hb] at hs
    have h3 := mul_le_mul_of_nonneg_left hdb hA'0
    linarith
  · unfold ext
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact bot_le

/-- **Power utility `0 < p < 1`: the same bundle is optimal, zeros allowed, real-valued.** -/
theorem power_optimum [Nonempty S] (p W : ℝ) (π q : S → ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hπ : ∀ s, 0 < π s) (hq : ∀ s, 0 < q s) (hW : 0 < W) (d : S → ℝ)
    (hd : ∀ s, 0 ≤ d s) (hdb : ∑ s, q s * d s ≤ W) :
    ∑ s, π s * (1 / p * d s ^ p) ≤ ∑ s, π s * (1 / p * copt p W π q s ^ p) := by
  obtain ⟨hc, hb, hfoc⟩ := copt_props p W π q hp1 hπ hq hW
  set A' := (W / ∑ t, q t * rr p π q t) ^ (p - 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have hr : ∀ s, 0 < rr p π q s := fun s => Real.rpow_pos_of_pos (div_pos (hπ s) (hq s)) _
    have hQ : 0 < ∑ t, q t * rr p π q t :=
      Finset.sum_pos (fun t _ => mul_pos (hq t) (hr t)) univ_nonempty
    exact (Real.rpow_pos_of_pos (div_pos hW hQ) _).le
  have key : ∀ s, π s * (1 / p * d s ^ p) ≤
      π s * (1 / p * copt p W π q s ^ p) + A' * q s * (d s - copt p W π q s) := by
    intro s
    have h1 := power_sg_nonneg p (d s) (copt p W π q s) hp0 hp1 (hd s) (hc s)
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    have e : π s * (1 / p * copt p W π q s ^ p +
          copt p W π q s ^ (p - 1) * (d s - copt p W π q s)) =
        π s * (1 / p * copt p W π q s ^ p) +
          (π s * copt p W π q s ^ (p - 1)) * (d s - copt p W π q s) := by ring
    rw [e, hfoc s] at h2
    exact h2
  have hs := Finset.sum_le_sum fun s (_ : s ∈ univ) => key s
  rw [Finset.sum_add_distrib] at hs
  have e2 : ∑ s, A' * q s * (d s - copt p W π q s) =
      A' * ∑ s, q s * d s - A' * ∑ s, q s * copt p W π q s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2, hb] at hs
  have h3 := mul_le_mul_of_nonneg_left hdb hA'0
  linarith

end CRRAOptimum

end

#print axioms CRRAOptimum.crra_supergradient
#print axioms CRRAOptimum.power_sg_nonneg
#print axioms CRRAOptimum.copt_props
#print axioms CRRAOptimum.crra_optimum
#print axioms CRRAOptimum.power_optimum
