import Mathlib

/-!
Stage 321: moral hazard under limited liability, debt versus profit sharing.

Finite outcomes `s`, output `y s ≥ 0`, outcome probabilities `πH` (effort) and `πL` (shirking),
effort cost `κ`.  A contract repays `R s` with `0 ≤ R s ≤ y s` (limited liability).  The borrower
works iff `Σ πL (y − R) ≤ Σ πH (y − R) − κ`.

* `ic_iff`, `rent_lower`, `pledgeable_bound`: under limited liability the borrower keeps a rent of
  at least `κ`, so a project is financeable only if `I ≤ E_H[y] − κ`, whatever the contract.
* `share_ic_iff`, `share_breakeven`: the profit share `θ = I / E_H[y]` breaks even, and works iff
  `κ ≤ (1 − θ) Σ (πH − πL) y`.
* Binary output (success `Y`, failure `0`): `tt_ic_iff`, `tt_feasible_iff`, `tt_min_rent`,
  `tt_share_equiv`.  Financing exists iff `I ≤ pH (Y − κ/(pH − pL))`, and every limited-liability
  debt contract is literally a profit share.  So with two outcomes, banning debt costs nothing.
* `debt_beats_share`: with three outcomes (likelihood ratio increasing) there is a project that
  debt can finance and the profit share with the same lender value cannot.  This is the Innes
  (1990) direction: with more than two outcomes and moral hazard, banning debt can cost something.

Honest limits: one effort choice, risk neutrality.  The optimal contract for general finite
outcomes (Innes's live-or-die / debt result) is not derived; only the bound and the example.
-/

open Finset BigOperators

noncomputable section

namespace MoralHazardLL

section General

variable {S : Type*} [Fintype S]

def Ex (π y : S → ℝ) : ℝ := ∑ s, π s * y s

def IC (πH πL y R : S → ℝ) (κ : ℝ) : Prop :=
  Ex πL (fun s => y s - R s) ≤ Ex πH (fun s => y s - R s) - κ

theorem ic_iff (πH πL y R : S → ℝ) (κ : ℝ) :
    IC πH πL y R κ ↔ κ ≤ ∑ s, (πH s - πL s) * (y s - R s) := by
  have e : ∑ s, (πH s - πL s) * (y s - R s) =
      Ex πH (fun s => y s - R s) - Ex πL (fun s => y s - R s) := by
    unfold Ex
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  unfold IC
  rw [e]
  constructor <;> intro h <;> linarith

/-- **The borrower's rent is at least the effort cost.** -/
theorem rent_lower (πH πL y R : S → ℝ) (κ : ℝ) (hL : ∀ s, 0 ≤ πL s) (hLL : ∀ s, R s ≤ y s)
    (h : IC πH πL y R κ) : κ ≤ Ex πH (fun s => y s - R s) := by
  have : 0 ≤ Ex πL (fun s => y s - R s) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hL s) (by linarith [hLL s])
  unfold IC at h
  linarith

/-- **Pledgeable income bound, for every contract.** -/
theorem pledgeable_bound (πH πL y R : S → ℝ) (κ I : ℝ) (hL : ∀ s, 0 ≤ πL s)
    (hLL : ∀ s, R s ≤ y s) (h : IC πH πL y R κ) (hI : I ≤ Ex πH R) : I ≤ Ex πH y - κ := by
  have h1 := rent_lower πH πL y R κ hL hLL h
  have e : Ex πH (fun s => y s - R s) = Ex πH y - Ex πH R := by
    unfold Ex
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

theorem share_ic_iff (πH πL y : S → ℝ) (θ κ : ℝ) :
    IC πH πL y (fun s => θ * y s) κ ↔ κ ≤ (1 - θ) * ∑ s, (πH s - πL s) * y s := by
  rw [ic_iff, Finset.mul_sum]
  have e : ∑ s, (πH s - πL s) * (y s - θ * y s) = ∑ s, (1 - θ) * ((πH s - πL s) * y s) :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [e]

theorem share_breakeven (πH y : S → ℝ) (I : ℝ) (hy : 0 < Ex πH y) :
    Ex πH (fun s => I / Ex πH y * y s) = I := by
  have hne : Ex πH y ≠ 0 := hy.ne'
  have e : Ex πH (fun s => I / Ex πH y * y s) = I / Ex πH y * Ex πH y := by
    conv_lhs => unfold Ex
    conv_rhs => rw [Ex, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  field_simp

end General

section Binary

def ttIC (pH pL Y R κ : ℝ) : Prop := pL * (Y - R) ≤ pH * (Y - R) - κ

theorem tt_ic_iff (pH pL Y R κ : ℝ) (hΔ : pL < pH) :
    ttIC pH pL Y R κ ↔ R ≤ Y - κ / (pH - pL) := by
  unfold ttIC
  have hd : 0 < pH - pL := by linarith
  have e : R ≤ Y - κ / (pH - pL) ↔ κ / (pH - pL) ≤ Y - R := by
    constructor <;> intro h <;> linarith
  rw [e, div_le_iff₀ hd]
  have key : (Y - R) * (pH - pL) = pH * (Y - R) - pL * (Y - R) := by ring
  rw [key]
  constructor <;> intro h <;> linarith

/-- **Financing under binary output.** -/
theorem tt_feasible_iff (pH pL Y κ I : ℝ) (hΔ : pL < pH) (hH : 0 < pH) (hI : 0 ≤ I)
    (hκ : 0 ≤ κ) :
    (∃ R, 0 ≤ R ∧ R ≤ Y ∧ ttIC pH pL Y R κ ∧ I ≤ pH * R) ↔
      I ≤ pH * (Y - κ / (pH - pL)) := by
  constructor
  · rintro ⟨R, -, -, hic, hR⟩
    have h := (tt_ic_iff pH pL Y R κ hΔ).1 hic
    calc I ≤ pH * R := hR
      _ ≤ pH * (Y - κ / (pH - pL)) := mul_le_mul_of_nonneg_left h hH.le
  · intro h
    have hd : 0 < pH - pL := by linarith
    have hk : 0 ≤ κ / (pH - pL) := div_nonneg hκ hd.le
    have hne : pH ≠ 0 := hH.ne'
    have hR : I / pH ≤ Y - κ / (pH - pL) := by
      rw [div_le_iff₀ hH]
      linarith [mul_comm pH (Y - κ / (pH - pL))]
    refine ⟨I / pH, div_nonneg hI hH.le, by linarith, (tt_ic_iff pH pL Y _ κ hΔ).2 hR, ?_⟩
    have : pH * (I / pH) = I := by field_simp
    linarith

/-- **The minimum agency rent.** -/
theorem tt_min_rent (pH pL Y R κ : ℝ) (hΔ : pL < pH) (hH : 0 ≤ pH) (h : ttIC pH pL Y R κ) :
    pH * (κ / (pH - pL)) ≤ pH * (Y - R) := by
  have := (tt_ic_iff pH pL Y R κ hΔ).1 h
  exact mul_le_mul_of_nonneg_left (by linarith) hH

/-- **With binary output, limited-liability debt is a profit share.** -/
theorem tt_share_equiv (Y R : ℝ) (hY : 0 < Y) (h0 : 0 ≤ R) (hRY : R ≤ Y) :
    min Y R = R / Y * Y ∧ min 0 R = R / Y * 0 := by
  have hne : Y ≠ 0 := hY.ne'
  refine ⟨?_, ?_⟩
  · rw [min_eq_right hRY]
    field_simp
  · rw [min_eq_left h0, mul_zero]

end Binary

section Example

def exH : Fin 3 → ℝ := ![1/10, 3/10, 6/10]
def exL : Fin 3 → ℝ := ![3/10, 4/10, 3/10]
def exY : Fin 3 → ℝ := ![0, 1, 3]
def exD : Fin 3 → ℝ := ![0, 1, 1]

/-- **With three outcomes, debt can beat profit sharing.**  Debt with face `1` and the profit share
`3/7` both give the lender `9/10`; with effort cost `1/2` debt keeps the borrower working and the
profit share does not. -/
theorem debt_beats_share :
    (∀ s, exD s = min (exY s) 1) ∧ IC exH exL exY exD (1/2) ∧ Ex exH exD = 9/10 ∧
      Ex exH (fun s => 3/7 * exY s) = 9/10 ∧ ¬ IC exH exL exY (fun s => 3/7 * exY s) (1/2) := by
  refine ⟨fun s => ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases s <;> norm_num [exD, exY]
  all_goals norm_num [IC, Ex, Fin.sum_univ_three, exH, exL, exY, exD]

end Example

end MoralHazardLL

end

#print axioms MoralHazardLL.ic_iff
#print axioms MoralHazardLL.rent_lower
#print axioms MoralHazardLL.pledgeable_bound
#print axioms MoralHazardLL.share_ic_iff
#print axioms MoralHazardLL.share_breakeven
#print axioms MoralHazardLL.tt_ic_iff
#print axioms MoralHazardLL.tt_feasible_iff
#print axioms MoralHazardLL.tt_min_rent
#print axioms MoralHazardLL.tt_share_equiv
#print axioms MoralHazardLL.debt_beats_share
