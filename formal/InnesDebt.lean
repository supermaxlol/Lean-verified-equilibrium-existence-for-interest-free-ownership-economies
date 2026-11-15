import Mathlib

/-!
# Stage 327 — Innes (1990): debt is optimal under MLRP

Finite states `Ω`. Low effort has state weights `πL ≥ 0`; high effort has weights
`l ω * πL ω` with a positive likelihood ratio `l`. Output is `y`. A contract `R` is
*limited liability* (`R ≤ y`) and *monotone* (`y ω ≤ y ω' → R ω ≤ R ω'`). The
monotone likelihood ratio property (MLRP) says `y ω ≤ y ω' → l ω ≤ l ω'`.

Among such contracts with the same high-effort expected repayment, the standard
debt contract `min y D` has the largest low-effort expected repayment, so it gives
the entrepreneur the strongest incentive to exert effort (`innes`, `innes_ic`).
A face value achieving any feasible repayment exists (`debt_exists`), giving the
optimality statement `debt_optimal`.

Note that debt here is a fixed claim with *no time premium*: `D` is whatever face
value makes the investor's expected repayment equal to the stake, so the result is
about the shape of the claim, not about interest.
-/

namespace InnesDebt

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- **Single-crossing lemma.** If a signed difference `Δ` is negative only where
the likelihood ratio is low and positive only where it is high, and it has zero
high-effort mean, then its low-effort mean is nonpositive. -/
theorem single_crossing (πL l Δ : Ω → ℝ) (hL : ∀ ω, 0 ≤ πL ω) (hl : ∀ ω, 0 < l ω)
    (hH : ∑ ω, l ω * πL ω * Δ ω = 0)
    (hsc : ∀ ω ω', Δ ω < 0 → 0 < Δ ω' → l ω ≤ l ω') :
    ∑ ω, πL ω * Δ ω ≤ 0 := by
  classical
  by_cases hN : (univ.filter fun ω => Δ ω < 0).Nonempty
  · set t := (univ.filter fun ω => Δ ω < 0).sup' hN l
    have htpos : 0 < t := by
      obtain ⟨ω, hω⟩ := hN
      exact lt_of_lt_of_le (hl ω) (Finset.le_sup' l hω)
    have hneg : ∀ ω, Δ ω < 0 → l ω ≤ t := fun ω h =>
      Finset.le_sup' l (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have hpos : ∀ ω, 0 < Δ ω → t ≤ l ω := fun ω h =>
      Finset.sup'_le hN l fun ω' hω' => hsc ω' ω (Finset.mem_filter.1 hω').2 h
    have hterm : ∀ ω, 0 ≤ πL ω * ((l ω - t) * Δ ω) := by
      intro ω
      apply mul_nonneg (hL ω)
      rcases lt_trichotomy (Δ ω) 0 with h | h | h
      · nlinarith [hneg ω h]
      · rw [h, mul_zero]
      · nlinarith [hpos ω h]
    have hsum : 0 ≤ ∑ ω, πL ω * ((l ω - t) * Δ ω) :=
      Finset.sum_nonneg fun ω _ => hterm ω
    have hexp : ∑ ω, πL ω * ((l ω - t) * Δ ω) =
        ∑ ω, l ω * πL ω * Δ ω - t * ∑ ω, πL ω * Δ ω := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [hexp, hH] at hsum
    nlinarith
  · have hnn : ∀ ω, 0 ≤ Δ ω := fun ω => by
      by_contra h
      exact hN ⟨ω, Finset.mem_filter.2 ⟨Finset.mem_univ _, not_le.1 h⟩⟩
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ =>
      mul_nonneg (mul_nonneg (hl ω).le (hL ω)) (hnn ω)).1 hH
    have hz : ∀ ω ∈ (univ : Finset Ω), πL ω * Δ ω = 0 := fun ω hω => by
      have h1 : l ω * (πL ω * Δ ω) = 0 := by rw [← mul_assoc]; exact h0 ω hω
      exact (mul_eq_zero.1 h1).resolve_left (hl ω).ne'
    rw [Finset.sum_eq_zero hz]

/-- **Innes.** Under MLRP, a monotone limited-liability contract with the same
high-effort expected repayment as debt `min y D` has a weakly smaller low-effort
expected repayment. -/
theorem innes (πL l y R : Ω → ℝ) (D : ℝ) (hL : ∀ ω, 0 ≤ πL ω) (hl : ∀ ω, 0 < l ω)
    (hmlrp : ∀ ω ω', y ω ≤ y ω' → l ω ≤ l ω')
    (hR : ∀ ω, R ω ≤ y ω) (hmono : ∀ ω ω', y ω ≤ y ω' → R ω ≤ R ω')
    (heq : ∑ ω, l ω * πL ω * R ω = ∑ ω, l ω * πL ω * min (y ω) D) :
    ∑ ω, πL ω * R ω ≤ ∑ ω, πL ω * min (y ω) D := by
  have hH : ∑ ω, l ω * πL ω * (R ω - min (y ω) D) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hsc : ∀ ω ω', R ω - min (y ω) D < 0 → 0 < R ω' - min (y ω') D → l ω ≤ l ω' := by
    intro ω ω' h1 h2
    apply hmlrp
    by_contra hlt
    have hRR := hmono ω' ω (not_le.1 hlt).le
    have hD : D < R ω' := by
      rcases le_total (y ω') D with h | h
      · rw [min_eq_left h] at h2
        linarith [hR ω']
      · rw [min_eq_right h] at h2
        linarith
    have := min_le_right (y ω) D
    linarith
  have h := single_crossing πL l (fun ω => R ω - min (y ω) D) hL hl hH hsc
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  linarith

/-- **Incentives.** If a monotone limited-liability contract satisfies the
entrepreneur's effort constraint (effort cost `c`), so does debt with the same
high-effort expected repayment. -/
theorem innes_ic (πL l y R : Ω → ℝ) (D c : ℝ) (hL : ∀ ω, 0 ≤ πL ω) (hl : ∀ ω, 0 < l ω)
    (hmlrp : ∀ ω ω', y ω ≤ y ω' → l ω ≤ l ω')
    (hR : ∀ ω, R ω ≤ y ω) (hmono : ∀ ω ω', y ω ≤ y ω' → R ω ≤ R ω')
    (heq : ∑ ω, l ω * πL ω * R ω = ∑ ω, l ω * πL ω * min (y ω) D)
    (hIC : ∑ ω, πL ω * (y ω - R ω) ≤ ∑ ω, l ω * πL ω * (y ω - R ω) - c) :
    ∑ ω, πL ω * (y ω - min (y ω) D) ≤ ∑ ω, l ω * πL ω * (y ω - min (y ω) D) - c := by
  have h := innes πL l y R D hL hl hmlrp hR hmono heq
  simp only [mul_sub, Finset.sum_sub_distrib] at hIC ⊢
  linarith

/-- **A face value exists** for every repayment between zero and full equity. -/
theorem debt_exists (πL l y : Ω → ℝ) (I : ℝ) (hy : ∀ ω, 0 ≤ y ω) (hI0 : 0 ≤ I)
    (hI1 : I ≤ ∑ ω, l ω * πL ω * y ω) :
    ∃ D, 0 ≤ D ∧ ∑ ω, l ω * πL ω * min (y ω) D = I := by
  have hB : 0 ≤ ∑ ω, y ω := Finset.sum_nonneg fun ω _ => hy ω
  have hyB : ∀ ω, y ω ≤ ∑ ω, y ω := fun ω =>
    Finset.single_le_sum (fun ω _ => hy ω) (Finset.mem_univ ω)
  have hf : Continuous fun D : ℝ => ∑ ω, l ω * πL ω * min (y ω) D :=
    continuous_finsetSum _ fun ω _ => continuous_const.mul (continuous_const.min continuous_id)
  have h0 : ∑ ω, l ω * πL ω * min (y ω) 0 = 0 :=
    Finset.sum_eq_zero fun ω _ => by rw [min_eq_right (hy ω), mul_zero]
  have hBv : ∑ ω, l ω * πL ω * min (y ω) (∑ ω, y ω) = ∑ ω, l ω * πL ω * y ω :=
    Finset.sum_congr rfl fun ω _ => by rw [min_eq_left (hyB ω)]
  have hmem : I ∈ Set.Icc (∑ ω, l ω * πL ω * min (y ω) 0)
      (∑ ω, l ω * πL ω * min (y ω) (∑ ω, y ω)) := by
    rw [h0, hBv]
    exact ⟨hI0, hI1⟩
  obtain ⟨D, hD, hDI⟩ := intermediate_value_Icc hB hf.continuousOn hmem
  exact ⟨D, hD.1, hDI⟩

/-- **Debt is optimal.** For every nonnegative, monotone, limited-liability contract
there is a debt contract with the same high-effort expected repayment and a weakly
larger low-effort expected repayment. -/
theorem debt_optimal (πL l y R : Ω → ℝ) (hL : ∀ ω, 0 ≤ πL ω) (hl : ∀ ω, 0 < l ω)
    (hy : ∀ ω, 0 ≤ y ω) (hmlrp : ∀ ω ω', y ω ≤ y ω' → l ω ≤ l ω')
    (hR0 : ∀ ω, 0 ≤ R ω) (hR : ∀ ω, R ω ≤ y ω)
    (hmono : ∀ ω ω', y ω ≤ y ω' → R ω ≤ R ω') :
    ∃ D, 0 ≤ D ∧ ∑ ω, l ω * πL ω * min (y ω) D = ∑ ω, l ω * πL ω * R ω ∧
      ∑ ω, πL ω * R ω ≤ ∑ ω, πL ω * min (y ω) D := by
  have hw : ∀ ω, 0 ≤ l ω * πL ω := fun ω => mul_nonneg (hl ω).le (hL ω)
  have hI0 : 0 ≤ ∑ ω, l ω * πL ω * R ω :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hR0 ω)
  have hI1 : ∑ ω, l ω * πL ω * R ω ≤ ∑ ω, l ω * πL ω * y ω :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hR ω) (hw ω)
  obtain ⟨D, hD, hDI⟩ := debt_exists πL l y _ hy hI0 hI1
  exact ⟨D, hD, hDI, innes πL l y R D hL hl hmlrp hR hmono hDI.symm⟩

end InnesDebt

#print axioms InnesDebt.single_crossing
#print axioms InnesDebt.innes
#print axioms InnesDebt.innes_ic
#print axioms InnesDebt.debt_exists
#print axioms InnesDebt.debt_optimal
