import Mathlib

/-!
Stage 303: the price of profit sharing under costly verification (builds on stage 301).

New results at the end: total surplus splits between lender and borrower; debt beats
full-audit profit sharing by exactly `c * P(no default)`; and truthful profit sharing must
verify every state whose output is below the top unverified level.

Stage 301 summary:

A borrower needs `I` from a lender.  Project output `y s ≥ 0` depends on a finite state `s`
seen only by the borrower; the lender can verify the state at cost `c ≥ 0`.  A contract is a
payment `r s` as a function of the reported state and a set `V` of reports that trigger
verification (a lie found by verification is punished).  The lender's outside option is cash,
so it needs expected net receipts of at least `I`: there is no time premium.

Results.
* Truth-telling forces a debt shape: the payment is the same `D` on every unverified state,
  never above `D`, and every state with output below `D` must be verified.
* Townsend / Gale–Hellwig: standard debt `min (y, D)`, verified exactly on default, pays the
  lender at least as much in every state and verifies on a subset, so it dominates every
  truth-telling contract, including profit sharing with an audit in every state.
* Interest-free cap `r ≤ I`: the lender breaks even only if `r = I` and `y ≥ I` in every
  state with positive probability and verification costs nothing in expectation.  So any risk
  of default forces the face above the principal: under costly verification the markup is a
  default-and-verification premium, not a price of time.
* Collateral `K` is an exact substitute: interest-free debt at face `I` with collateral breaks
  even with no verification if and only if `y + K ≥ I` on the support.
-/

noncomputable section

open Finset

namespace ProfitSharingCost

variable {S : Type*}

/-- Truth-telling: in state `s`, reporting an unverified state `s'` whose payment is affordable
is never strictly better than the truth. -/
def IC (y r : S → ℝ) (V : Finset S) : Prop :=
  ∀ s s', s' ∉ V → r s' ≤ y s → r s ≤ r s'

/-- Limited liability: payments are non-negative and at most output. -/
def LL (y r : S → ℝ) : Prop := ∀ s, 0 ≤ r s ∧ r s ≤ y s

/-- Standard debt with face `D`. -/
def dpay (y : S → ℝ) (D : ℝ) (s : S) : ℝ := min (y s) D

theorem ic_cap (y r : S → ℝ) (V : Finset S) (hIC : IC y r V) (hLL : LL y r) (s s' : S)
    (hs' : s' ∉ V) : r s ≤ r s' := by
  by_contra h
  have h' : r s' < r s := lt_of_not_ge h
  exact h (hIC s s' hs' (le_trans h'.le (hLL s).2))

/-- **Truth-telling forces the debt shape.** -/
theorem ic_debt_form (y r : S → ℝ) (V : Finset S) (hIC : IC y r V) (hLL : LL y r) (s0 : S)
    (hs0 : s0 ∉ V) :
    (∀ s, r s ≤ r s0) ∧ (∀ s, s ∉ V → r s = r s0) ∧ (∀ s, y s < r s0 → s ∈ V) := by
  refine ⟨fun s => ic_cap y r V hIC hLL s s0 hs0,
    fun s hs => le_antisymm (ic_cap y r V hIC hLL s s0 hs0) (ic_cap y r V hIC hLL s0 s hs),
    fun s hy => ?_⟩
  by_contra hs
  have e : r s = r s0 :=
    le_antisymm (ic_cap y r V hIC hLL s s0 hs0) (ic_cap y r V hIC hLL s0 s hs)
  have := (hLL s).2
  linarith

theorem debt_ll (y : S → ℝ) (D : ℝ) (hy : ∀ s, 0 ≤ y s) (hD : 0 ≤ D) : LL y (dpay y D) :=
  fun s => ⟨le_min (hy s) hD, min_le_left _ _⟩

variable [Fintype S]

/-- Default set of standard debt: verify exactly when output is below the face. -/
def dver (y : S → ℝ) (D : ℝ) : Finset S := univ.filter fun s => y s < D

/-- Lender's expected receipts net of expected verification cost. -/
def lnet (π : S → ℝ) (c : ℝ) (r : S → ℝ) (V : Finset S) : ℝ :=
  ∑ s, π s * r s - c * ∑ s ∈ V, π s

theorem debt_ic (y : S → ℝ) (D : ℝ) : IC y (dpay y D) (dver y D) := by
  intro s s' hs' _
  have hD : D ≤ y s' := by
    by_contra h
    exact hs' (mem_filter.2 ⟨mem_univ _, lt_of_not_ge h⟩)
  have e : dpay y D s' = D := min_eq_right hD
  rw [e]
  exact min_le_right (y s) D

theorem debt_dominates (y r : S → ℝ) (V : Finset S) (D : ℝ) (hLL : LL y r)
    (hcap : ∀ s, r s ≤ D) (hver : ∀ s, y s < D → s ∈ V) :
    (∀ s, r s ≤ dpay y D s) ∧ dver y D ⊆ V :=
  ⟨fun s => le_min (hLL s).2 (hcap s), fun s hs => hver s (mem_filter.1 hs).2⟩

theorem lnet_mono (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (c : ℝ) (hc : 0 ≤ c) (r r' : S → ℝ)
    (V V' : Finset S) (hr : ∀ s, r s ≤ r' s) (hV : V' ⊆ V) :
    lnet π c r V ≤ lnet π c r' V' := by
  unfold lnet
  have h1 : ∑ s, π s * r s ≤ ∑ s, π s * r' s :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hr s) (hπ s)
  have h2 : ∑ s ∈ V', π s ≤ ∑ s ∈ V, π s :=
    Finset.sum_le_sum_of_subset_of_nonneg hV fun s _ _ => hπ s
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- **Townsend / Gale–Hellwig on a finite state space.**  Every truth-telling contract with
some unverified state is dominated by standard debt with the same face. -/
theorem townsend (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (c : ℝ) (hc : 0 ≤ c) (y r : S → ℝ)
    (V : Finset S) (hy : ∀ s, 0 ≤ y s) (hIC : IC y r V) (hLL : LL y r) (s0 : S)
    (hs0 : s0 ∉ V) :
    IC y (dpay y (r s0)) (dver y (r s0)) ∧ LL y (dpay y (r s0)) ∧
      (∀ s, r s ≤ dpay y (r s0) s) ∧ dver y (r s0) ⊆ V ∧
      lnet π c r V ≤ lnet π c (dpay y (r s0)) (dver y (r s0)) ∧
      ∑ s ∈ dver y (r s0), π s ≤ ∑ s ∈ V, π s := by
  obtain ⟨h1, -, h3⟩ := ic_debt_form y r V hIC hLL s0 hs0
  obtain ⟨d1, d2⟩ := debt_dominates y r V (r s0) hLL h1 h3
  exact ⟨debt_ic _ _, debt_ll y _ hy (hLL s0).1, d1, d2, lnet_mono π hπ c hc _ _ _ _ d1 d2,
    Finset.sum_le_sum_of_subset_of_nonneg d2 fun s _ _ => hπ s⟩

/-- Profit sharing with an audit in every state is dominated by debt with any face that
bounds its payments. -/
theorem full_audit_dominated (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (c : ℝ) (hc : 0 ≤ c)
    (y r : S → ℝ) (hLL : LL y r) (D : ℝ) (hcap : ∀ s, r s ≤ D) :
    (∀ s, r s ≤ dpay y D s) ∧ lnet π c r univ ≤ lnet π c (dpay y D) (dver y D) := by
  obtain ⟨d1, d2⟩ := debt_dominates y r univ D hLL hcap (fun s _ => mem_univ s)
  exact ⟨d1, lnet_mono π hπ c hc _ _ _ _ d1 d2⟩

/-- **Interest-free cap.**  If no payment exceeds the principal, the lender gets at most `I`,
and breaks even only when every positive-probability state pays exactly `I` (so output is at
least `I` there) and expected verification cost is zero. -/
theorem interest_free_bound (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (c : ℝ)
    (hc : 0 ≤ c) (I : ℝ) (y r : S → ℝ) (V : Finset S) (hLL : LL y r) (hcap : ∀ s, r s ≤ I) :
    lnet π c r V ≤ I ∧ (I ≤ lnet π c r V →
      (∀ s, 0 < π s → r s = I ∧ I ≤ y s) ∧ c * ∑ s ∈ V, π s = 0) := by
  have hPV : 0 ≤ ∑ s ∈ V, π s := Finset.sum_nonneg fun s _ => hπ s
  have hcP := mul_nonneg hc hPV
  have hgap : ∑ s, π s * (I - r s) = I - ∑ s, π s * r s := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul]
  have hnn : ∀ s, 0 ≤ π s * (I - r s) := fun s => mul_nonneg (hπ s) (by linarith [hcap s])
  have hsum : 0 ≤ ∑ s, π s * (I - r s) := Finset.sum_nonneg fun s _ => hnn s
  unfold lnet
  refine ⟨by linarith, fun hge => ?_⟩
  have hz : ∑ s, π s * (I - r s) = 0 := le_antisymm (by linarith) hsum
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hnn s).1 hz
  refine ⟨fun s hs => ?_, by linarith⟩
  have h0 := hz' s (mem_univ s)
  have hr : r s = I := by
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  refine ⟨hr, ?_⟩
  rw [← hr]
  exact (hLL s).2

/-- **With default risk the face must exceed the principal.** -/
theorem markup_needed (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (c : ℝ)
    (hc : 0 ≤ c) (y : S → ℝ) (I D : ℝ) (hy0 : ∀ s, 0 ≤ y s) (hD : 0 ≤ D)
    (hrisk : ∃ s, 0 < π s ∧ y s < I) (hbreak : I ≤ lnet π c (dpay y D) (dver y D)) : I < D := by
  by_contra h
  have hDI : D ≤ I := not_lt.1 h
  obtain ⟨s, hs, hys⟩ := hrisk
  have key := ((interest_free_bound π hπ hπ1 c hc I y (dpay y D) (dver y D)
    (debt_ll y D hy0 hD) (fun s => le_trans (min_le_right (y s) D) hDI)).2 hbreak).1 s hs
  have h2 : dpay y D s ≤ y s := min_le_left _ _
  linarith [key.1]

/-- **Riskless projects need no markup and no verification.** -/
theorem riskless_qard (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (c : ℝ)
    (y : S → ℝ) (I : ℝ) (hsafe : ∀ s, 0 < π s → I ≤ y s) :
    lnet π c (dpay y I) (dver y I) = I := by
  unfold lnet
  have h1 : ∑ s, π s * dpay y I s = ∑ s, π s * I := Finset.sum_congr rfl fun s _ => by
    rcases (hπ s).lt_or_eq with h | h
    · rw [show dpay y I s = I from min_eq_right (hsafe s h)]
    · rw [← h]; ring
  have h2 : ∑ s ∈ dver y I, π s = 0 := Finset.sum_eq_zero fun s hs => by
    have hlt : y s < I := (mem_filter.1 hs).2
    rcases (hπ s).lt_or_eq with h | h
    · exact absurd hlt (not_lt.2 (hsafe s h))
    · exact h.symm
  rw [h1, h2, ← Finset.sum_mul, hπ1]
  ring

/-- **Collateral makes interest-free debt work.**  With collateral `K` covering the principal
on the support, debt at face `I` is truth-telling, never pays above `I`, and breaks even. -/
theorem collateral_qard (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (c : ℝ)
    (y : S → ℝ) (K I : ℝ) (hy : ∀ s, 0 ≤ y s) (hK : 0 ≤ K) (hI : 0 ≤ I)
    (hcov : ∀ s, 0 < π s → I ≤ y s + K) :
    IC (fun s => y s + K) (dpay (fun s => y s + K) I) (dver (fun s => y s + K) I) ∧
      LL (fun s => y s + K) (dpay (fun s => y s + K) I) ∧
      (∀ s, dpay (fun s => y s + K) I s ≤ I) ∧
      lnet π c (dpay (fun s => y s + K) I) (dver (fun s => y s + K) I) = I :=
  ⟨debt_ic _ _, debt_ll _ _ (fun s => add_nonneg (hy s) hK) hI, fun _ => min_le_right _ _,
    riskless_qard π hπ hπ1 c _ I hcov⟩

/-- **And collateral coverage is necessary** for any interest-free contract to break even. -/
theorem collateral_necessary (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (c : ℝ)
    (hc : 0 ≤ c) (y r : S → ℝ) (K I : ℝ) (V : Finset S) (hLL : LL (fun s => y s + K) r)
    (hcap : ∀ s, r s ≤ I) (hge : I ≤ lnet π c r V) : ∀ s, 0 < π s → I ≤ y s + K :=
  fun s hs => (((interest_free_bound π hπ hπ1 c hc I _ r V hLL hcap).2 hge).1 s hs).2

/-- Total surplus net of verification cost (before subtracting the advance). -/
def surplus (π : S → ℝ) (c : ℝ) (y : S → ℝ) (V : Finset S) : ℝ :=
  ∑ s, π s * y s - c * ∑ s ∈ V, π s

/-- **Surplus splits** into lender and borrower shares; the contract only moves it around. -/
theorem surplus_split (π : S → ℝ) (c : ℝ) (y r : S → ℝ) (V : Finset S) :
    lnet π c r V + ∑ s, π s * (y s - r s) = surplus π c y V := by
  have h : ∑ s, π s * (y s - r s) = ∑ s, π s * y s - ∑ s, π s * r s := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
  unfold lnet surplus; rw [h]; ring

/-- **Exact cost of auditing every state.**  Debt with face `D` saves the verification cost
on every non-default state: the surplus gap is `c * P(y ≥ D)`. -/
theorem surplus_gap (π : S → ℝ) (c : ℝ) (y : S → ℝ) (D : ℝ) :
    surplus π c y (dver y D) - surplus π c y univ =
      c * ∑ s ∈ univ.filter (fun s => ¬ y s < D), π s := by
  unfold surplus dver
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => y s < D) π]
  ring

/-- **Truthful profit sharing audits almost everywhere.**  With payment `θ * y`, `θ > 0`, an
unverified state must have the top output, all unverified states share that output, and every
state with lower output is verified. -/
theorem profit_share_audits (y : S → ℝ) (θ : ℝ) (hθ : 0 < θ) (V : Finset S)
    (hIC : IC y (fun s => θ * y s) V) (hLL : LL y (fun s => θ * y s)) (s0 : S) (hs0 : s0 ∉ V) :
    (∀ s, y s ≤ y s0) ∧ (univ.filter fun s => y s < y s0) ⊆ V := by
  obtain ⟨h1, h2, -⟩ := ic_debt_form y _ V hIC hLL s0 hs0
  refine ⟨fun s => le_of_mul_le_mul_left (h1 s) hθ, fun s hs => ?_⟩
  have hlt := (mem_filter.1 hs).2
  by_contra hv
  have e := h2 s hv
  have : y s = y s0 := mul_left_cancel₀ hθ.ne' e
  linarith

/-- Hence its verification probability is at least `P(y < top output)`. -/
theorem profit_share_audit_prob (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (y : S → ℝ) (θ : ℝ)
    (hθ : 0 < θ) (V : Finset S) (hIC : IC y (fun s => θ * y s) V)
    (hLL : LL y (fun s => θ * y s)) (s0 : S) (hs0 : s0 ∉ V) :
    ∑ s ∈ univ.filter (fun s => y s < y s0), π s ≤ ∑ s ∈ V, π s :=
  Finset.sum_le_sum_of_subset_of_nonneg (profit_share_audits y θ hθ V hIC hLL s0 hs0).2
    fun s _ _ => hπ s

end ProfitSharingCost

end

#print axioms ProfitSharingCost.ic_debt_form
#print axioms ProfitSharingCost.debt_ic
#print axioms ProfitSharingCost.debt_dominates
#print axioms ProfitSharingCost.lnet_mono
#print axioms ProfitSharingCost.townsend
#print axioms ProfitSharingCost.full_audit_dominated
#print axioms ProfitSharingCost.interest_free_bound
#print axioms ProfitSharingCost.markup_needed
#print axioms ProfitSharingCost.riskless_qard
#print axioms ProfitSharingCost.collateral_qard
#print axioms ProfitSharingCost.collateral_necessary
#print axioms ProfitSharingCost.surplus_split
#print axioms ProfitSharingCost.surplus_gap
#print axioms ProfitSharingCost.profit_share_audits
#print axioms ProfitSharingCost.profit_share_audit_prob
