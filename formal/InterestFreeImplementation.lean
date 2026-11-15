import Mathlib

/-!
Stage 320: every Arrow–Debreu equilibrium can be traded with interest-free contracts only.

Finite states `S`, contracts `J` with state payoffs `D j s`, state prices `q`.  A contract's price
is the value of its payoffs, `aprice q D j = Σ_s q s D j s`.  Households hold portfolios `θ`.

* `cost_eq`: a portfolio costs exactly the state-price value of its payoff.
* `Abudget_subset`, `budget_eq`: if the contracts span the payoff space, the contract budget set
  equals the Arrow–Debreu budget set.
* `implement`: every Arrow–Debreu equilibrium (each household optimal in its AD budget, markets
  clear) is a contract-market equilibrium.  Each household reaches its AD bundle with a portfolio
  that is optimal among all affordable portfolios, and when payoffs are linearly independent the
  contract markets clear (net holdings zero).
* `debt_redundant`, `debt_adds_nothing`: a fixed (debt) claim is replicated by the spanning
  contracts, so adding debt does not enlarge any budget set.
* `arrow_spans`, `arrow_indep`, `arrow_nonneg`: state-contingent claims (pay `1` in one state and
  `0` otherwise, with no fixed obligation) span and are independent.
* `spans_of_indep`: as many ownership claims as states with linearly independent payoffs (for
  example, shares in firms whose outputs are linearly independent) span.  So pure ownership markets
  implement every AD equilibrium.

Link to the existence program: stage 261 proves that an Arrow–Debreu equilibrium exists.  This stage
proves that any such equilibrium is reachable with interest-free contracts only.  The link is at the
level of statements; the two files are not joined by a single Lean import.

Honest limits: one period, complete spanning, no transaction or verification costs.  With costly
verification (stages 301, 315, 319) or moral hazard (stage 309) contracts are not frictionless, and
banning debt is no longer free.  State prices still embed time preference; the claim is that no
contract carries a fixed premium, not that consumption is undiscounted.
-/

open Finset BigOperators

noncomputable section

namespace InterestFreeImpl

variable {J S : Type*} [Fintype J] [Fintype S]

def pay (D : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * D j s

def aprice (q : S → ℝ) (D : J → S → ℝ) (j : J) : ℝ := ∑ s, q s * D j s

def val (q x : S → ℝ) : ℝ := ∑ s, q s * x s

def pcost (q : S → ℝ) (D : J → S → ℝ) (θ : J → ℝ) : ℝ := ∑ j, θ j * aprice q D j

def Spans (D : J → S → ℝ) : Prop := ∀ z : S → ℝ, ∃ θ, pay D θ = z

def Indep (D : J → S → ℝ) : Prop := ∀ θ, pay D θ = 0 → θ = 0

def ADbudget (q ω : S → ℝ) : Set (S → ℝ) := {x | val q x ≤ val q ω}

def Abudget (q : S → ℝ) (D : J → S → ℝ) (ω : S → ℝ) : Set (S → ℝ) :=
  {x | ∃ θ, x = ω + pay D θ ∧ pcost q D θ ≤ 0}

theorem cost_eq (q : S → ℝ) (D : J → S → ℝ) (θ : J → ℝ) :
    pcost q D θ = val q (pay D θ) := by
  unfold pcost aprice val pay
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype J] in
theorem val_add (q x y : S → ℝ) : val q (x + y) = val q x + val q y := by
  unfold val
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by simp only [Pi.add_apply]; ring

omit [Fintype J] in
theorem val_sub (q x y : S → ℝ) : val q (x - y) = val q x - val q y := by
  unfold val
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by simp only [Pi.sub_apply]; ring

theorem Abudget_subset (q : S → ℝ) (D : J → S → ℝ) (ω : S → ℝ) :
    Abudget q D ω ⊆ ADbudget q ω := by
  rintro x ⟨θ, rfl, hθ⟩
  show val q (ω + pay D θ) ≤ val q ω
  rw [val_add, ← cost_eq]
  linarith

/-- **With spanning contracts the two budget sets coincide.** -/
theorem budget_eq (q : S → ℝ) (D : J → S → ℝ) (ω : S → ℝ) (hD : Spans D) :
    Abudget q D ω = ADbudget q ω := by
  apply Set.Subset.antisymm (Abudget_subset q D ω)
  intro x hx
  obtain ⟨θ, hθ⟩ := hD (x - ω)
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ]; funext s; simp
  · rw [cost_eq, hθ, val_sub]
    have : val q x ≤ val q ω := hx
    linarith

omit [Fintype S] in
theorem pay_sum {I : Type*} [Fintype I] (D : J → S → ℝ) (θ : I → J → ℝ) :
    pay D (fun j => ∑ i, θ i j) = fun s => ∑ i, pay D (θ i) s := by
  funext s
  unfold pay
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

/-- **Every Arrow–Debreu equilibrium is an interest-free contract equilibrium.** -/
theorem implement {I : Type*} [Fintype I] (q : S → ℝ) (D : J → S → ℝ) (ω x : I → S → ℝ)
    (U : I → (S → ℝ) → ℝ) (hopt : ∀ i, ∀ x' ∈ ADbudget q (ω i), U i x' ≤ U i (x i))
    (hbud : ∀ i, x i ∈ ADbudget q (ω i)) (hclear : ∀ s, ∑ i, x i s = ∑ i, ω i s)
    (hD : Spans D) (hInd : Indep D) :
    ∃ θ : I → J → ℝ, (∀ i, ω i + pay D (θ i) = x i) ∧ (∀ i, pcost q D (θ i) ≤ 0) ∧
      (∀ i θ', pcost q D θ' ≤ 0 → U i (ω i + pay D θ') ≤ U i (x i)) ∧
      (∀ j, ∑ i, θ i j = 0) := by
  choose θ hθ using fun i => hD (x i - ω i)
  have hreach : ∀ i, ω i + pay D (θ i) = x i := by
    intro i; rw [hθ i]; funext s; simp
  refine ⟨θ, hreach, fun i => ?_, fun i θ' hθ' => ?_, ?_⟩
  · have : x i ∈ Abudget q D (ω i) := by rw [budget_eq q D (ω i) hD]; exact hbud i
    obtain ⟨θ2, h2, hc2⟩ := this
    rw [cost_eq, hθ i, val_sub]
    rw [cost_eq] at hc2
    have : pay D θ2 = x i - ω i := by rw [h2]; funext s; simp
    rw [this, val_sub] at hc2
    exact hc2
  · exact hopt i _ (Abudget_subset q D (ω i) ⟨θ', rfl, hθ'⟩)
  · have h0 : pay D (fun j => ∑ i, θ i j) = 0 := by
      rw [pay_sum]
      funext s
      simp only [hθ, Pi.sub_apply, Finset.sum_sub_distrib, hclear, sub_self, Pi.zero_apply]
    intro j
    exact congrFun (hInd _ h0) j

/-- **A debt claim is redundant.** -/
theorem debt_redundant (q : S → ℝ) (D : J → S → ℝ) (hD : Spans D) (d : ℝ) :
    ∃ θ, pay D θ = (fun _ => d) ∧ pcost q D θ = d * ∑ s, q s := by
  obtain ⟨θ, hθ⟩ := hD fun _ => d
  refine ⟨θ, hθ, ?_⟩
  rw [cost_eq, hθ]
  unfold val
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Adding debt does not enlarge the budget set.** -/
theorem debt_adds_nothing (q : S → ℝ) (D : J → S → ℝ) (ω : S → ℝ) (hD : Spans D) :
    {x | ∃ θ b, x = ω + pay D θ + (fun _ => b) ∧ pcost q D θ + b * ∑ s, q s ≤ 0} =
      Abudget q D ω := by
  rw [budget_eq q D ω hD]
  apply Set.Subset.antisymm
  · rintro x ⟨θ, b, rfl, h⟩
    show val q (ω + pay D θ + fun _ => b) ≤ val q ω
    rw [val_add, val_add, ← cost_eq]
    have : val q (fun _ => b) = b * ∑ s, q s := by
      unfold val; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    linarith
  · intro x hx
    rw [← budget_eq q D ω hD] at hx
    obtain ⟨θ, rfl, h⟩ := hx
    exact ⟨θ, 0, by funext s; simp, by simpa using h⟩

section Arrow

variable [DecidableEq S]

/-- State-contingent claims: pay `1` in state `j`, nothing otherwise. -/
def arrow (j s : S) : ℝ := if j = s then 1 else 0

theorem pay_arrow (θ : S → ℝ) : pay arrow θ = θ := by
  funext s
  simp [pay, arrow]

theorem arrow_spans : Spans (arrow : S → S → ℝ) := fun z => ⟨z, pay_arrow z⟩

theorem arrow_indep : Indep (arrow : S → S → ℝ) := fun θ h => by rwa [pay_arrow] at h

omit [Fintype S] in
theorem arrow_nonneg (j s : S) : 0 ≤ arrow j s := by
  unfold arrow; split_ifs <;> norm_num

end Arrow

/-- `pay D` as a linear map. -/
def payL (D : J → S → ℝ) : (J → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun θ := pay D θ
  map_add' a b := by
    funext s
    simp only [pay, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    funext s
    simp only [pay, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- **As many independent ownership claims as states span.** -/
theorem spans_of_indep (D : J → S → ℝ) (hcard : Fintype.card J = Fintype.card S)
    (hInd : Indep D) : Spans D := by
  have hinj : Function.Injective (payL D) := by
    intro a b h
    have h0 : pay D (a - b) = 0 := by
      funext s
      have := congrFun h s
      simp only [payL, LinearMap.coe_mk, AddHom.coe_mk] at this
      simp only [pay, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply] at this ⊢
      linarith
    exact sub_eq_zero.1 (hInd _ h0)
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_fintype_fun_eq_card, hcard])).1 hinj
  intro z
  obtain ⟨θ, hθ⟩ := hsurj z
  exact ⟨θ, hθ⟩

end InterestFreeImpl

end

#print axioms InterestFreeImpl.cost_eq
#print axioms InterestFreeImpl.val_add
#print axioms InterestFreeImpl.val_sub
#print axioms InterestFreeImpl.Abudget_subset
#print axioms InterestFreeImpl.budget_eq
#print axioms InterestFreeImpl.pay_sum
#print axioms InterestFreeImpl.implement
#print axioms InterestFreeImpl.debt_redundant
#print axioms InterestFreeImpl.debt_adds_nothing
#print axioms InterestFreeImpl.pay_arrow
#print axioms InterestFreeImpl.arrow_spans
#print axioms InterestFreeImpl.arrow_indep
#print axioms InterestFreeImpl.arrow_nonneg
#print axioms InterestFreeImpl.spans_of_indep
