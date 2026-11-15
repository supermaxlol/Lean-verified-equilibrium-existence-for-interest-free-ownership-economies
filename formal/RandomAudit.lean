import Mathlib

/-!
Stage 308: Random audits (Mookherjee–Png) and interest-free contracts.

Finite states `s` with output `y s`.  The borrower reports `m`, repays `R m`, and the lender audits the
report with probability `a m`.  A lie that is caught costs the borrower everything (maximal penalty), so
truth-telling requires `(1 − a m)(y s − R m) ≤ y s − R s` whenever report `m` is affordable in state `s`.

* With deterministic audits (`a ∈ {0,1}`) any report that some higher-paying state could imitate must
  be audited with certainty (`det_full`).
* If the borrower keeps a strictly positive residual in every state, the minimal random audit `astar`
  is incentive compatible and strictly below `1` everywhere (`astar_ic`, `astar_lt_one`), and it never
  exceeds any deterministic IC scheme (`astar_le_det`). So randomisation strictly lowers the expected
  verification cost (`cost_saving`).
* Debt's full surrender in default leaves no residual. Between two full-surrender states, even random
  auditing must be certain (`full_surrender_audit`).
* Profit sharing with share `θ` needs audit probability at most `θ` (`ps_astar_le`). An interest-free
  profit-sharing contract therefore recovers principal `I` whenever `I ≤ θ(E y − c)`
  (`ps_break_even`), and it audits more cheaply than debt once `θ < P(default)` (`ps_beats_debt`).
-/

open Finset BigOperators

noncomputable section

namespace RandomAudit

variable {S : Type*} [Fintype S]

/-- Truth-telling with random audit probability `a` and maximal penalty. -/
def IC (y R a : S → ℝ) : Prop :=
  ∀ s m, R m ≤ y s → (1 - a m) * (y s - R m) ≤ y s - R s

theorem ic_pair_iff (ys Rs Rm am : ℝ) :
    (1 - am) * (ys - Rm) ≤ ys - Rs ↔ Rs - Rm ≤ am * (ys - Rm) := by
  have e : (1 - am) * (ys - Rm) = (ys - Rm) - am * (ys - Rm) := by ring
  rw [e]
  constructor <;> intro h <;> linarith

omit [Fintype S] in
/-- **Deterministic audits must be certain** on any report that a higher-paying state can imitate. -/
theorem det_full (y R a : S → ℝ) (h : IC y R a) (m s : S) (hf : R m ≤ y s) (hg : R m < R s)
    (h01 : a m = 0 ∨ a m = 1) : a m = 1 := by
  rcases h01 with h0 | h1
  · have := h s m hf
    rw [h0, sub_zero, one_mul] at this
    linarith
  · exact h1

omit [Fintype S] in
/-- **Full surrender forces certain audits**, even when audits are random. -/
theorem full_surrender_audit (y R a : S → ℝ) (h : IC y R a) (m s : S) (hs : R s = y s)
    (hg : R m < R s) : 1 ≤ a m := by
  have h1 := h s m (by linarith)
  rw [hs, sub_self] at h1
  have h2 : 0 < y s - R m := by linarith
  by_contra hc
  have : 0 < (1 - a m) * (y s - R m) := mul_pos (by linarith) h2
  linarith

/-- Audit probability needed against the lie "true `s`, report `m`". -/
def need (y R : S → ℝ) (s m : S) : ℝ :=
  if R m < y s then max 0 ((R s - R m) / (y s - R m)) else 0

/-- The minimal random audit of report `m`. -/
def astar [Nonempty S] (y R : S → ℝ) (m : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s => need y R s m)

omit [Fintype S] in
theorem need_nonneg (y R : S → ℝ) (s m : S) : 0 ≤ need y R s m := by
  unfold need; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem astar_nonneg [Nonempty S] (y R : S → ℝ) (m : S) : 0 ≤ astar y R m :=
  le_trans (need_nonneg y R m m) (Finset.le_sup' (fun s => need y R s m) (mem_univ m))

/-- **The minimal random audit is incentive compatible** (repayment never exceeds output). -/
theorem astar_ic [Nonempty S] (y R : S → ℝ) (hLL : ∀ s, R s ≤ y s) : IC y R (astar y R) := by
  intro s m hf
  rw [ic_pair_iff]
  by_cases hlt : R m < y s
  · have hpos : 0 < y s - R m := sub_pos.2 hlt
    have h1 : need y R s m = max 0 ((R s - R m) / (y s - R m)) := by simp [need, hlt]
    have h2 : need y R s m ≤ astar y R m := Finset.le_sup' (fun s => need y R s m) (mem_univ s)
    have h3 : (R s - R m) / (y s - R m) ≤ astar y R m := by
      rw [h1] at h2; exact le_trans (le_max_right _ _) h2
    have h4 := mul_le_mul_of_nonneg_right h3 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at h4
  · have he : R m = y s := le_antisymm hf (not_lt.1 hlt)
    rw [he, sub_self, mul_zero]
    linarith [hLL s]

/-- **Randomisation keeps audits below certainty** when the borrower keeps a residual. -/
theorem astar_lt_one [Nonempty S] (y R : S → ℝ) (hres : ∀ s, R s < y s) (m : S) :
    astar y R m < 1 := by
  unfold astar
  rw [Finset.sup'_lt_iff]
  intro s _
  unfold need
  split_ifs with h
  · exact max_lt one_pos ((div_lt_one (sub_pos.2 h)).2 (by linarith [hres s]))
  · exact one_pos

/-- **Random audit never exceeds a deterministic IC audit.** -/
theorem astar_le_det [Nonempty S] (y R ad : S → ℝ) (hres : ∀ s, R s < y s) (hd : IC y R ad)
    (h01 : ∀ m, ad m = 0 ∨ ad m = 1) (m : S) : astar y R m ≤ ad m := by
  rcases h01 m with h0 | h1
  · rw [h0]
    refine Finset.sup'_le _ _ fun s _ => ?_
    unfold need
    split_ifs with hlt
    · have hic := hd s m hlt.le
      rw [h0, sub_zero, one_mul] at hic
      have hnum : R s - R m ≤ 0 := by linarith
      exact max_le le_rfl (div_nonpos_of_nonpos_of_nonneg hnum (sub_pos.2 hlt).le)
    · exact le_rfl
  · rw [h1]; exact (astar_lt_one y R hres m).le

/-- **Randomisation strictly lowers expected verification cost.** -/
theorem cost_saving [Nonempty S] (y R ad π : S → ℝ) (c : ℝ) (hc : 0 < c) (hπ : ∀ s, 0 ≤ π s)
    (hres : ∀ s, R s < y s) (hd : IC y R ad) (h01 : ∀ m, ad m = 0 ∨ ad m = 1)
    (hex : ∃ m, 0 < π m ∧ ad m = 1) :
    c * ∑ m, π m * astar y R m < c * ∑ m, π m * ad m := by
  refine mul_lt_mul_of_pos_left ?_ hc
  obtain ⟨m0, hm0, hm1⟩ := hex
  refine Finset.sum_lt_sum (fun m _ => mul_le_mul_of_nonneg_left
    (astar_le_det y R ad hres hd h01 m) (hπ m)) ⟨m0, mem_univ _, ?_⟩
  rw [hm1]
  exact mul_lt_mul_of_pos_left (astar_lt_one y R hres m0) hm0

/-- **Profit sharing needs audit probability at most `θ`.** -/
theorem ps_astar_le [Nonempty S] (y : S → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hy : ∀ s, 0 ≤ y s) (m : S) : astar y (fun s => θ * y s) m ≤ θ := by
  refine Finset.sup'_le _ _ fun s _ => ?_
  unfold need
  split_ifs with h
  · refine max_le hθ0 ?_
    rw [div_le_iff₀ (sub_pos.2 h)]
    nlinarith [mul_nonneg (mul_nonneg hθ0 (sub_nonneg.2 hθ1)) (hy m)]
  · exact hθ0

/-- **Interest-free profit sharing breaks even** at principal `I` when `I ≤ θ (E y − c)`. -/
theorem ps_break_even [Nonempty S] (y π : S → ℝ) (θ c I : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc : 0 ≤ c) (hy : ∀ s, 0 ≤ y s) (hπ : ∀ s, 0 ≤ π s) (h1 : ∑ s, π s = 1)
    (hI : I ≤ θ * (∑ s, π s * y s - c)) :
    I ≤ ∑ s, π s * (θ * y s) - c * ∑ m, π m * astar y (fun s => θ * y s) m := by
  have ha : ∑ m, π m * astar y (fun s => θ * y s) m ≤ θ := by
    calc ∑ m, π m * astar y (fun s => θ * y s) m ≤ ∑ m, π m * θ :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (ps_astar_le y θ hθ0 hθ1 hy m) (hπ m)
      _ = θ := by rw [← Finset.sum_mul, h1, one_mul]
  have hs : ∑ s, π s * (θ * y s) = θ * ∑ s, π s * y s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  have := mul_le_mul_of_nonneg_left ha hc
  rw [hs]
  nlinarith

/-- **Random-audit profit sharing audits more cheaply than deterministic debt** once `θ` is below
the default probability. -/
theorem ps_beats_debt [Nonempty S] (y π : S → ℝ) (θ c D : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc : 0 < c) (hy : ∀ s, 0 ≤ y s) (hπ : ∀ s, 0 ≤ π s) (h1 : ∑ s, π s = 1)
    (hlt : θ < ∑ s ∈ Finset.univ.filter (fun s => y s < D), π s) :
    c * ∑ m, π m * astar y (fun s => θ * y s) m <
      c * ∑ s ∈ Finset.univ.filter (fun s => y s < D), π s := by
  have ha : ∑ m, π m * astar y (fun s => θ * y s) m ≤ θ := by
    calc ∑ m, π m * astar y (fun s => θ * y s) m ≤ ∑ m, π m * θ :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (ps_astar_le y θ hθ0 hθ1 hy m) (hπ m)
      _ = θ := by rw [← Finset.sum_mul, h1, one_mul]
  exact mul_lt_mul_of_pos_left (lt_of_le_of_lt ha hlt) hc

end RandomAudit

end

#print axioms RandomAudit.ic_pair_iff
#print axioms RandomAudit.det_full
#print axioms RandomAudit.full_surrender_audit
#print axioms RandomAudit.astar_ic
#print axioms RandomAudit.astar_lt_one
#print axioms RandomAudit.astar_le_det
#print axioms RandomAudit.cost_saving
#print axioms RandomAudit.ps_astar_le
#print axioms RandomAudit.ps_break_even
#print axioms RandomAudit.ps_beats_debt
