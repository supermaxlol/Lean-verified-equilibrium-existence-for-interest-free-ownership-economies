import Mathlib

/-!
Stage 319: the Border–Sobel program with the repayment schedule chosen too.

Stage 315 found the cheapest audit schedule `astar` for a *given* repayment schedule `R`.  Here the
lender also chooses `R`, subject to repayments within output, truth-telling, and breaking even
after audit costs (`Feasible`).

* `reduce`: in any feasible scheme the audits can be replaced by `astar` at no higher cost, so the
  joint problem is a minimization over `R` alone.
* `astar_zero_iff`: a repayment schedule needs no audits iff it is flat.
* `audit_free_iff`: an audit-free feasible scheme exists iff every state's output covers the
  principal `I`.  When it does not, every feasible scheme has positive expected audit cost.
* `two_state_lower`, `two_state_optimum`: with two states the optimum is solved in closed form.
  The bottom state repays **all** its output, the top report is never audited, and the bottom report
  is audited with probability `(I − yL)/(pH (yH − yL) − c pL) ≤ 1`: random, not certain, verification.

Honest limits: the closed-form optimum is for two states; for general finite `S` the monotonicity
of the optimal repayment (Border–Sobel's theorem that `R` rises with output) is not proved, and
existence of an optimum for general `S` is not proved.  Maximal penalty and audit commitment assumed.
-/

open Finset BigOperators

noncomputable section

namespace BorderSobelJoint

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


theorem top_no_audit (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) (m : S) (htop : ∀ s, R s ≤ R m) :
    astar y R m = 0 := by
  apply le_antisymm _ (astar_nonneg y R hR m)
  refine (Finset.sup'_le_iff _ _).2 fun s _ => ?_
  unfold g
  rw [ite_eq_right (not_lt.2 (htop s))]

/-- A financing scheme: repayments within output, audit probabilities in `[0,1]`, truth-telling,
and the lender breaks even after paying audit cost `c` per audit. -/
def Feasible (π y : S → ℝ) (c I : ℝ) (R a : S → ℝ) : Prop :=
  (∀ s, 0 ≤ R s ∧ R s ≤ y s) ∧ (∀ m, 0 ≤ a m ∧ a m ≤ 1) ∧ IC y R a ∧
    I ≤ ∑ s, π s * R s - c * ∑ s, π s * a s

def cost (π : S → ℝ) (c : ℝ) (a : S → ℝ) : ℝ := c * ∑ s, π s * a s

/-- **Reduction**: replacing any audit schedule by `astar` keeps feasibility and lowers cost. -/
theorem reduce (π y : S → ℝ) (c I : ℝ) (R a : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hc : 0 ≤ c)
    (hf : Feasible π y c I R a) :
    Feasible π y c I R (astar y R) ∧ cost π c (astar y R) ≤ cost π c a := by
  obtain ⟨hR, ha, hic, hbe⟩ := hf
  have hR' : ∀ s, R s ≤ y s := fun s => (hR s).2
  have hle := (ic_iff y R a hR' (fun m => (ha m).1) (fun m => (ha m).2)).1 hic
  have hsum : ∑ s, π s * astar y R s ≤ ∑ s, π s * a s :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hle s) (hπ s)
  have hcs := mul_le_mul_of_nonneg_left hsum hc
  refine ⟨⟨hR, fun m => ⟨astar_nonneg y R hR' m, astar_le_one y R hR' m⟩, astar_ic y R hR', ?_⟩,
    hcs⟩
  linarith

/-- **Audit-free schedules are exactly flat repayments.** -/
theorem astar_zero_iff (y R : S → ℝ) (hR : ∀ s, R s ≤ y s) :
    (∀ m, astar y R m = 0) ↔ ∀ s m, R s = R m := by
  constructor
  · intro h
    have key : ∀ s m, R s ≤ R m := by
      intro s m
      by_contra hc
      have hlt : R m < R s := lt_of_not_ge hc
      have hpos : 0 < g y R s m := by
        unfold g; rw [ite_eq_left hlt]; exact div_pos (by linarith) (by linarith [hR s])
      have := Finset.le_sup' (fun s => g y R s m) (Finset.mem_univ s)
      have h0 : astar y R m = 0 := h m
      unfold astar at h0
      linarith
    exact fun s m => le_antisymm (key s m) (key m s)
  · intro h m
    exact top_no_audit y R hR m fun s => (h s m).le

/-- **Audits are unavoidable exactly when some state cannot repay the principal.** -/
theorem audit_free_iff (π y : S → ℝ) (c I : ℝ) (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    (hc : 0 < c) (hI : 0 ≤ I) :
    (∃ R a, Feasible π y c I R a ∧ cost π c a = 0) ↔ ∀ s, I ≤ y s := by
  constructor
  · rintro ⟨R, a, ⟨hR, ha, hic, hbe⟩, h0⟩
    have hsum0 : ∑ s, π s * a s = 0 := by
      unfold cost at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hc.ne'
      · exact h
    have hz : ∀ m, a m = 0 := by
      intro m
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_nonneg (hπ s).le (ha s).1)).1 hsum0 m (Finset.mem_univ m)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hπ m).ne'
      · exact h
    have hflat : ∀ s m, R s ≤ R m := by
      intro s m
      have := hic s m
      rw [hz m] at this
      linarith
    obtain ⟨s0⟩ := (inferInstance : Nonempty S)
    have hRc : ∀ s, R s = R s0 := fun s => le_antisymm (hflat s s0) (hflat s0 s)
    have hrev : ∑ s, π s * R s = R s0 := by
      rw [Finset.sum_congr rfl fun s _ => by rw [hRc s], ← Finset.sum_mul, hπ1, one_mul]
    rw [hrev, hsum0, mul_zero, sub_zero] at hbe
    intro s
    calc I ≤ R s0 := hbe
      _ = R s := (hRc s).symm
      _ ≤ y s := (hR s).2
  · intro h
    refine ⟨fun _ => I, fun _ => 0, ⟨fun s => ⟨hI, h s⟩, fun _ => ⟨le_rfl, zero_le_one⟩,
      fun s m => by simp, ?_⟩, by simp [cost]⟩
    rw [← Finset.sum_mul, hπ1]
    simp

/-- **Two states: lower bound on the bottom audit probability for every feasible scheme.**
`H` reporting `L` must be deterred; `aH` (auditing the top report) only adds cost. -/
theorem two_state_lower (pL pH c yL yH I rL rH aL aH : ℝ) (hp : pL + pH = 1) (hpL : 0 ≤ pL)
    (hpH : 0 ≤ pH) (hc : 0 ≤ c) (hrL : rL ≤ yL) (_haL0 : 0 ≤ aL) (haL1 : aL ≤ 1) (haH : 0 ≤ aH)
    (hic : (1 - aL) * (yH - rL) ≤ yH - rH)
    (hbe : I ≤ pL * rL + pH * rH - c * (pL * aL + pH * aH)) :
    I - yL ≤ aL * (pH * (yH - yL) - c * pL) := by
  have hpL' : pL = 1 - pH := by linarith
  subst hpL'
  have h1 : rH ≤ rL + aL * (yH - rL) := by nlinarith
  have h2 : pH * rH ≤ pH * (rL + aL * (yH - rL)) := mul_le_mul_of_nonneg_left h1 hpH
  have h3 : 0 ≤ c * (pH * aH) := mul_nonneg hc (mul_nonneg hpH haH)
  have hpH1 : pH ≤ 1 := by linarith
  have h5 : aL * pH ≤ 1 := by nlinarith [mul_le_mul haL1 hpH1 hpH zero_le_one]
  have h4 : 0 ≤ (yL - rL) * (1 - aL * pH) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h2, h3, h4, hbe]

/-- **Two states: the Border–Sobel optimum.**  The bottom state repays all its output, the top
report is never audited, the bottom report is audited with probability
`a⋆ = (I − yL)/(pH (yH − yL) − c pL)`, and no feasible scheme has lower expected audit cost. -/
theorem two_state_optimum (pL pH c yL yH I : ℝ) (hp : pL + pH = 1) (hpL : 0 ≤ pL)
    (hpH : 0 ≤ pH) (hc : 0 ≤ c) (hy : yL ≤ yH) (hI : yL ≤ I)
    (hD : 0 < pH * (yH - yL) - c * pL)
    (h1 : (I - yL) / (pH * (yH - yL) - c * pL) ≤ 1) :
    let a := (I - yL) / (pH * (yH - yL) - c * pL)
    let rH := yL + a * (yH - yL)
    (0 ≤ a ∧ rH ≤ yH ∧ yL ≤ rH ∧
      (1 - a) * (yH - yL) ≤ yH - rH ∧ (1 - 0) * (yL - rH) ≤ yL - yL ∧
      I ≤ pL * yL + pH * rH - c * (pL * a + pH * 0)) ∧
    ∀ rL rH' aL aH, rL ≤ yL → 0 ≤ aL → aL ≤ 1 → 0 ≤ aH →
      (1 - aL) * (yH - rL) ≤ yH - rH' →
      I ≤ pL * rL + pH * rH' - c * (pL * aL + pH * aH) →
      c * (pL * a + pH * 0) ≤ c * (pL * aL + pH * aH) := by
  intro a rH
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hD.le
  have haD : a * (pH * (yH - yL) - c * pL) = I - yL := div_mul_cancel₀ _ hD.ne'
  have hΔ : 0 ≤ yH - yL := by linarith
  refine ⟨⟨ha0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show yL + a * (yH - yL) ≤ yH
    nlinarith [mul_le_mul_of_nonneg_right h1 hΔ]
  · show yL ≤ yL + a * (yH - yL)
    nlinarith [mul_nonneg ha0 hΔ]
  · show (1 - a) * (yH - yL) ≤ yH - (yL + a * (yH - yL))
    nlinarith
  · show (1 - 0) * (yL - (yL + a * (yH - yL))) ≤ yL - yL
    nlinarith [mul_nonneg ha0 hΔ]
  · show I ≤ pL * yL + pH * (yL + a * (yH - yL)) - c * (pL * a + pH * 0)
    have hpL' : pL = 1 - pH := by linarith
    subst hpL'
    nlinarith [haD]
  · intro rL rH' aL aH hrL haL0 haL1 haH hic hbe
    have hlow := two_state_lower pL pH c yL yH I rL rH' aL aH hp hpL hpH hc hrL haL0 haL1 haH
      hic hbe
    have haL : a ≤ aL := by
      show (I - yL) / (pH * (yH - yL) - c * pL) ≤ aL
      rw [div_le_iff₀ hD]; linarith
    have : pL * a ≤ pL * aL := mul_le_mul_of_nonneg_left haL hpL
    have : 0 ≤ pH * aH := mul_nonneg hpH haH
    nlinarith [mul_le_mul_of_nonneg_left (show pL * a + pH * 0 ≤ pL * aL + pH * aH by linarith) hc]

end BorderSobelJoint

end

#print axioms BorderSobelJoint.g_nonneg
#print axioms BorderSobelJoint.g_le_one
#print axioms BorderSobelJoint.pair_iff
#print axioms BorderSobelJoint.astar_nonneg
#print axioms BorderSobelJoint.astar_le_one
#print axioms BorderSobelJoint.ic_iff
#print axioms BorderSobelJoint.astar_ic
#print axioms BorderSobelJoint.top_no_audit
#print axioms BorderSobelJoint.reduce
#print axioms BorderSobelJoint.astar_zero_iff
#print axioms BorderSobelJoint.audit_free_iff
#print axioms BorderSobelJoint.two_state_lower
#print axioms BorderSobelJoint.two_state_optimum
