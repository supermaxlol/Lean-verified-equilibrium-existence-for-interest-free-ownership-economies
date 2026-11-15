import Mathlib

/-!
Stage 250 (Study A): initial ownership and distribution.

Households `h : H` hold labour income `L h` and ownership share `θ h` of a firm with
profit `π`.  Demand is taken in the Cobb–Douglas (identical, homothetic) form
`x h s = α s * w h / p s`.  Results:

* capital income is distributed exactly in proportion to ownership;
* an assetless household's expenditure is bounded by its labour income;
* aggregate demand, and therefore any market-clearing price, does not depend on how
  ownership is distributed (the market does not correct the distribution);
* each household's consumption is its wealth share of aggregate consumption.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace OwnershipDistribution

variable {H S : Type*} [Fintype H] [Fintype S]

/-- Household wealth: labour income plus ownership share of profit. -/
def wealth (L θ : H → ℝ) (π : ℝ) (h : H) : ℝ := L h + θ h * π

/-- Cobb–Douglas demand at wealth `w`. -/
def cdDemand (α p : S → ℝ) (w : ℝ) (s : S) : ℝ := α s * w / p s

theorem total_wealth (L θ : H → ℝ) (π : ℝ) (hθ : ∑ h, θ h = 1) :
    ∑ h, wealth L θ π h = (∑ h, L h) + π := by
  simp only [wealth, Finset.sum_add_distrib, ← Finset.sum_mul, hθ, one_mul]

/-- Capital income shares equal ownership shares. -/
theorem capital_income_share (θ : H → ℝ) (π : ℝ) (hπ : π ≠ 0) (hθ : ∑ h, θ h = 1)
    (h : H) : θ h * π / ∑ k, θ k * π = θ h := by
  rw [← Finset.sum_mul, hθ, one_mul]
  field_simp

/-- An assetless household can spend at most its labour income. -/
theorem assetless_bound (L θ : H → ℝ) (π : ℝ) (p : S → ℝ) (x : H → S → ℝ) (h : H)
    (hbud : ∑ s, p s * x h s ≤ wealth L θ π h) (h0 : θ h = 0) :
    ∑ s, p s * x h s ≤ L h := by
  simpa [wealth, h0] using hbud

/-- Cobb–Douglas demand exhausts the budget. -/
theorem cd_budget (α p : S → ℝ) (w : ℝ) (hp : ∀ s, p s ≠ 0) (hα : ∑ s, α s = 1) :
    ∑ s, p s * cdDemand α p w s = w := by
  have h1 : ∀ s, p s * cdDemand α p w s = α s * w := by
    intro s
    have := hp s
    unfold cdDemand
    field_simp
  simp only [h1, ← Finset.sum_mul, hα, one_mul]

/-- Aggregate demand depends only on total wealth. -/
theorem aggregate_demand_eq (α p : S → ℝ) (L θ : H → ℝ) (π : ℝ) (hθ : ∑ h, θ h = 1)
    (s : S) :
    ∑ h, cdDemand α p (wealth L θ π h) s = cdDemand α p ((∑ h, L h) + π) s := by
  unfold cdDemand
  rw [← Finset.sum_div, ← Finset.mul_sum, total_wealth L θ π hθ]

/-- Aggregate demand is the same under any two ownership distributions. -/
theorem aggregate_demand_ownership_neutral (α p : S → ℝ) (L θ θ' : H → ℝ) (π : ℝ)
    (hθ : ∑ h, θ h = 1) (hθ' : ∑ h, θ' h = 1) (s : S) :
    ∑ h, cdDemand α p (wealth L θ π h) s = ∑ h, cdDemand α p (wealth L θ' π h) s := by
  rw [aggregate_demand_eq α p L θ π hθ, aggregate_demand_eq α p L θ' π hθ']

/-- A price that clears markets under one ownership distribution clears them under any
other: redistribution of ownership leaves prices unchanged. -/
theorem clearing_ownership_neutral (α p y : S → ℝ) (L θ θ' : H → ℝ) (π : ℝ)
    (hθ : ∑ h, θ h = 1) (hθ' : ∑ h, θ' h = 1)
    (hclear : ∀ s, ∑ h, cdDemand α p (wealth L θ π h) s = y s) :
    ∀ s, ∑ h, cdDemand α p (wealth L θ' π h) s = y s := by
  intro s
  rw [← hclear s]
  exact aggregate_demand_ownership_neutral α p L θ' θ π hθ' hθ s

/-- Each household consumes its wealth share of aggregate consumption. -/
theorem consumption_share (α p : S → ℝ) (w W : ℝ) (hW : W ≠ 0) (s : S) (hp : p s ≠ 0) :
    cdDemand α p w s = (w / W) * cdDemand α p W s := by
  unfold cdDemand
  field_simp

/-- With no labour income, consumption is the ownership share of aggregate output
demand. -/
theorem pure_capital_consumption (α p : S → ℝ) (θh π : ℝ) (s : S) :
    cdDemand α p (θh * π) s = θh * cdDemand α p π s := by
  unfold cdDemand
  ring

/-- A household with neither labour income nor ownership consumes nothing. -/
theorem assetless_no_labour_zero (α p : S → ℝ) (L θ : H → ℝ) (π : ℝ) (h : H)
    (hL : L h = 0) (h0 : θ h = 0) (s : S) :
    cdDemand α p (wealth L θ π h) s = 0 := by
  simp [cdDemand, wealth, hL, h0]

end OwnershipDistribution

end

#print axioms OwnershipDistribution.total_wealth
#print axioms OwnershipDistribution.capital_income_share
#print axioms OwnershipDistribution.assetless_bound
#print axioms OwnershipDistribution.cd_budget
#print axioms OwnershipDistribution.aggregate_demand_eq
#print axioms OwnershipDistribution.aggregate_demand_ownership_neutral
#print axioms OwnershipDistribution.clearing_ownership_neutral
#print axioms OwnershipDistribution.consumption_share
#print axioms OwnershipDistribution.pure_capital_consumption
#print axioms OwnershipDistribution.assetless_no_labour_zero
