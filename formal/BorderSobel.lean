import Mathlib

/-!
Stage 315: the Border–Sobel optimal audit schedule.

Finitely many states, output `y`, repayment schedule `R` with `R ≤ y`.  A borrower in state `s`
reporting `m` is audited with probability `a m`; a detected lie forfeits everything (maximal
penalty, as in Border–Sobel 1987 and stage 308).  Truth-telling is

  `IC y R a :  ∀ s m, (1 − a m)(y s − R m) ≤ y s − R s`.

Let `astar m = max_s g s m`, with `g s m = (R s − R m)/(y s − R m)` when `R m < R s` and `0` otherwise.

* `ic_iff`: an audit schedule with values in `[0,1]` is incentive compatible iff `astar ≤ a`.
  `astar` is the pointwise least incentive-compatible schedule.
* `astar_ic`: `astar` itself is incentive compatible.
* `cost_min`: for every repayment schedule `R`, `astar` minimizes the expected audit cost
  `Σ π m · c · a m` over all incentive-compatible schedules.
* `top_no_audit`: the report with the highest repayment is never audited.
* `astar_antitone`: audit probability falls as the reported repayment rises.  This is Border–Sobel's
  monotonicity: low reports are audited more.
* `astar_lt_one`: if `R < y` everywhere, no report is audited with certainty.  Randomization strictly
  beats deterministic (Townsend) verification.

Honest limits: the schedule is optimal for a given `R`; the joint optimization over `R` with the
lender's break-even constraint (the full Border–Sobel program) is not proved.  Commitment to audit
and the maximal penalty are assumed.
-/

open Finset BigOperators

noncomputable section

namespace BorderSobel

variable {S : Type*} [Fintype S] [Nonempty S]

def IC (y R a : S → ℝ) : Prop := ∀ s m, (1 - a m) * (y s - R m) ≤ y s - R s

def g (y R : S → ℝ) (s m : S) : ℝ := if R m < R s then (R s - R m) / (y s - R m) else 0

def astar (y R : S → ℝ) (m : S) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun s => g y R s m)

omit [Fintype S] [Nonempty S] in
theorem g_nonneg (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (s m : S) : 0 ≤ g y R s m := by
  unfold g
  split_ifs with h
  · exact div_nonneg (by linarith) (by linarith [hR s])
  · exact le_rfl

omit [Fintype S] [Nonempty S] in
theorem g_le_one (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (s m : S) : g y R s m ≤ 1 := by
  unfold g
  split_ifs with h
  · rw [div_le_one (by linarith [hR s])]; linarith [hR s]
  · exact zero_le_one

omit [Fintype S] [Nonempty S] in
theorem pair_iff (y R a : S → ℝ) (hR : ∀ s, R s ≤ y s) (s m : S) (ha0 : 0 ≤ a m)
    (ha1 : a m ≤ 1) : (1 - a m) * (y s - R m) ≤ y s - R s ↔ g y R s m ≤ a m := by
  unfold g
  split_ifs with h
  · have hd : 0 < y s - R m := by linarith [hR s]
    rw [div_le_iff₀ hd]
    constructor <;> intro h' <;> nlinarith
  · have h' : R s ≤ R m := not_lt.1 h
    simp only [ha0, iff_true]
    rcases le_or_gt 0 (y s - R m) with h2 | h2
    · nlinarith [mul_nonneg ha0 h2]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a m) (by linarith : (0 : ℝ) ≤ -(y s - R m)),
        hR s]

theorem astar_nonneg (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (m : S) : 0 ≤ astar y R m := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  exact (g_nonneg y R hR s m).trans (Finset.le_sup' (fun s => g y R s m) (Finset.mem_univ s))

theorem astar_le_one (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (m : S) : astar y R m ≤ 1 :=
  (Finset.sup'_le_iff _ _).2 fun s _ => g_le_one y R hR s m

/-- **Incentive compatibility is exactly `astar ≤ a`.** -/
theorem ic_iff (y R a : S → ℝ) (hR : ∀ s, R s ≤ y s) (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1) :
    IC y R a ↔ ∀ m, astar y R m ≤ a m := by
  constructor
  · intro h m
    exact (Finset.sup'_le_iff _ _).2 fun s _ => (pair_iff y R a hR s m (ha0 m) (ha1 m)).1 (h s m)
  · intro h s m
    exact (pair_iff y R a hR s m (ha0 m) (ha1 m)).2
      ((Finset.le_sup' (fun s => g y R s m) (Finset.mem_univ s)).trans (h m))

theorem astar_ic (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) : IC y R (astar y R) :=
  (ic_iff y R _ hR (astar_nonneg y R hR) (astar_le_one y R hR)).2 fun _ => le_rfl

/-- **`astar` minimizes expected audit cost.** -/
theorem cost_min (y R a π : S → ℝ) (c : ℝ) (hR : ∀ s, R s ≤ y s) (hπ : ∀ m, 0 ≤ π m)
    (hc : 0 ≤ c) (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1) (hic : IC y R a) :
    ∑ m, π m * c * astar y R m ≤ ∑ m, π m * c * a m :=
  Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
    ((ic_iff y R a hR ha0 ha1).1 hic m) (mul_nonneg (hπ m) hc)

/-- **The top report is not audited.** -/
theorem top_no_audit (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (m : S) (htop : ∀ s, R s ≤ R m) :
    astar y R m = 0 := by
  apply le_antisymm _ (astar_nonneg y R hR m)
  refine (Finset.sup'_le_iff _ _).2 fun s _ => ?_
  unfold g
  rw [ite_eq_right (not_lt.2 (htop s))]

/-- **Border–Sobel monotonicity: lower reports are audited more.** -/
theorem astar_antitone (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (m m' : S) (hmm : R m ≤ R m') :
    astar y R m' ≤ astar y R m := by
  refine (Finset.sup'_le_iff _ _).2 fun s _ => ?_
  refine le_trans ?_ (Finset.le_sup' (fun s => g y R s m) (Finset.mem_univ s))
  show g y R s m' ≤ g y R s m
  unfold g
  by_cases h' : R m' < R s
  · have h : R m < R s := lt_of_le_of_lt hmm h'
    rw [ite_eq_left h', ite_eq_left h]
    have hd' : 0 < y s - R m' := by linarith [hR s]
    have hd : 0 < y s - R m := by linarith [hR s]
    rw [div_le_div_iff₀ hd' hd]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R m' - R m) (by linarith [hR s] : (0 : ℝ) ≤ y s - R s)]
  · rw [ite_eq_right h']
    by_cases h : R m < R s
    · rw [ite_eq_left h]; exact div_nonneg (by linarith) (by linarith [hR s])
    · rw [ite_eq_right h]

/-- **Randomization: no report is audited with certainty when `R < y`.** -/
theorem astar_lt_one (y R : S → ℝ) (hR : ∀ s, R s < y s) (m : S) : astar y R m < 1 := by
  refine (Finset.sup'_lt_iff _).2 fun s _ => ?_
  unfold g
  split_ifs with h
  · rw [div_lt_one (by linarith [hR s])]; linarith [hR s]
  · exact zero_lt_one

end BorderSobel

end

#print axioms BorderSobel.g_nonneg
#print axioms BorderSobel.g_le_one
#print axioms BorderSobel.pair_iff
#print axioms BorderSobel.astar_nonneg
#print axioms BorderSobel.astar_le_one
#print axioms BorderSobel.ic_iff
#print axioms BorderSobel.astar_ic
#print axioms BorderSobel.cost_min
#print axioms BorderSobel.top_no_audit
#print axioms BorderSobel.astar_antitone
#print axioms BorderSobel.astar_lt_one
