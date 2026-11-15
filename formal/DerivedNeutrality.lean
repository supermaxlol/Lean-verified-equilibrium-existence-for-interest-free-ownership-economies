import Mathlib

/-!
# Stage 352: ownership neutrality from utility maximisation

Stage 250 took the Cobb–Douglas demand rule as given; stage 252 showed it is the unique
maximiser of `∑ α s * log (x s)`. This stage joins the two. Households choose *any*
utility-maximising bundle (`IsBest`); no demand rule is assumed. Results:

* `cd_isBest`: the Cobb–Douglas bundle is a best choice.
* `best_eq`: every best choice *is* the Cobb–Douglas bundle.
* `optimal_aggregate`: aggregate optimal demand depends only on total wealth.
* `optimal_demand_ownership_neutral`, `optimal_clearing_neutral`: aggregate demand and
  market-clearing prices do not depend on the ownership distribution.
* `optimal_consumption_share`: each household consumes its wealth share of the aggregate.

The stage-250 definitions and the stage-252 lemmas are inlined.
-/

open Finset

namespace DerivedNeutrality

variable {H S : Type*} [Fintype H] [Fintype S]

/-! ### Stage 250 definitions -/

def wealth (L θ : H → ℝ) (π : ℝ) (h : H) : ℝ := L h + θ h * π

noncomputable def cdDemand (α p : S → ℝ) (w : ℝ) (s : S) : ℝ := α s * w / p s

theorem total_wealth (L θ : H → ℝ) (π : ℝ) (hθ : ∑ h, θ h = 1) :
    ∑ h, wealth L θ π h = (∑ h, L h) + π := by
  simp only [wealth, Finset.sum_add_distrib, ← Finset.sum_mul, hθ, one_mul]

/-! ### Stage 252 lemmas -/

theorem term_le (a p x w : ℝ) (ha : 0 < a) (hp : 0 < p) (hw : 0 < w) (hx : 0 < x) :
    a * Real.log x - a * Real.log (a * w / p) ≤ p * x / w - a := by
  have hstar : 0 < a * w / p := div_pos (mul_pos ha hw) hp
  have h1 : Real.log (x / (a * w / p)) ≤ x / (a * w / p) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx hstar)
  rw [Real.log_div hx.ne' hstar.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 ha.le
  have h3 : a * (x / (a * w / p) - 1) = p * x / w - a := by
    have := ha.ne'
    have := hp.ne'
    have := hw.ne'
    field_simp
  linarith

theorem term_lt (a p x w : ℝ) (ha : 0 < a) (hp : 0 < p) (hw : 0 < w) (hx : 0 < x)
    (hne : x ≠ a * w / p) :
    a * Real.log x - a * Real.log (a * w / p) < p * x / w - a := by
  have hstar : 0 < a * w / p := div_pos (mul_pos ha hw) hp
  have hne1 : x / (a * w / p) ≠ 1 := fun h => hne ((div_eq_one_iff_eq hstar.ne').1 h)
  have h1 : Real.log (x / (a * w / p)) < x / (a * w / p) - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos hx hstar) hne1
  rw [Real.log_div hx.ne' hstar.ne'] at h1
  have h2 := mul_lt_mul_of_pos_left h1 ha
  have h3 : a * (x / (a * w / p) - 1) = p * x / w - a := by
    have := ha.ne'
    have := hp.ne'
    have := hw.ne'
    field_simp
  linarith

theorem demand_budget (α p : S → ℝ) (w : ℝ) (hp : ∀ s, 0 < p s) (hsum : ∑ s, α s = 1) :
    ∑ s, p s * (α s * w / p s) = w := by
  have h1 : ∀ s, p s * (α s * w / p s) = α s * w := by
    intro s
    have := (hp s).ne'
    field_simp
  simp only [h1, ← Finset.sum_mul, hsum, one_mul]

theorem demand_optimal (α p x : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, p s * x s ≤ w) :
    ∑ s, α s * Real.log (x s) ≤ ∑ s, α s * Real.log (α s * w / p s) := by
  have hs : ∑ s, (α s * Real.log (x s) - α s * Real.log (α s * w / p s))
      ≤ ∑ s, (p s * x s / w - α s) :=
    Finset.sum_le_sum (fun s _ => term_le (α s) (p s) (x s) w (hα s) (hp s) hw (hx s))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hs
  have h1 : (∑ s, p s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

theorem demand_unique (α p x : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, p s * x s ≤ w) (hne : ∃ s, x s ≠ α s * w / p s) :
    ∑ s, α s * Real.log (x s) < ∑ s, α s * Real.log (α s * w / p s) := by
  obtain ⟨t, ht⟩ := hne
  have hs : ∑ s, (α s * Real.log (x s) - α s * Real.log (α s * w / p s))
      < ∑ s, (p s * x s / w - α s) :=
    Finset.sum_lt_sum
      (fun s _ => term_le (α s) (p s) (x s) w (hα s) (hp s) hw (hx s))
      ⟨t, Finset.mem_univ t, term_lt (α t) (p t) (x t) w (hα t) (hp t) hw (hx t) ht⟩
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hs
  have h1 : (∑ s, p s * x s) / w ≤ 1 := (div_le_one hw).2 hbud
  linarith

/-! ### Joining the two -/

/-- `x` is a best choice at prices `p` and wealth `w`: strictly positive, affordable, and
at least as good as every strictly positive affordable bundle. -/
def IsBest (α p : S → ℝ) (w : ℝ) (x : S → ℝ) : Prop :=
  (∀ s, 0 < x s) ∧ ∑ s, p s * x s ≤ w ∧
    ∀ y : S → ℝ, (∀ s, 0 < y s) → ∑ s, p s * y s ≤ w →
      ∑ s, α s * Real.log (y s) ≤ ∑ s, α s * Real.log (x s)

theorem cd_isBest (α p : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) : IsBest α p w (cdDemand α p w) :=
  ⟨fun s => div_pos (mul_pos (hα s) hw) (hp s),
    (demand_budget α p w hp hsum).le,
    fun y hy hb => demand_optimal α p y w hα hsum hp hw hy hb⟩

/-- **Every best choice is the Cobb–Douglas bundle.** -/
theorem best_eq (α p : S → ℝ) (w : ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (hw : 0 < w) (x : S → ℝ) (hx : IsBest α p w x) :
    x = cdDemand α p w := by
  by_contra hne
  have hne' : ∃ s, x s ≠ α s * w / p s := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have h1 := demand_unique α p x w hα hsum hp hw hx.1 hx.2.1 hne'
  have h2 := hx.2.2 (cdDemand α p w) (cd_isBest α p w hα hsum hp hw).1
    (demand_budget α p w hp hsum).le
  unfold cdDemand at h2
  linarith

/-- Aggregate optimal demand depends only on total wealth. -/
theorem optimal_aggregate (α p : S → ℝ) (hα : ∀ s, 0 < α s) (hsum : ∑ s, α s = 1)
    (hp : ∀ s, 0 < p s) (L θ : H → ℝ) (π : ℝ) (hθ : ∑ h, θ h = 1)
    (hw : ∀ h, 0 < wealth L θ π h) (x : H → S → ℝ)
    (hx : ∀ h, IsBest α p (wealth L θ π h) (x h)) (s : S) :
    ∑ h, x h s = cdDemand α p ((∑ h, L h) + π) s := by
  have e : ∀ h, x h s = cdDemand α p (wealth L θ π h) s := fun h => by
    rw [best_eq α p _ hα hsum hp (hw h) (x h) (hx h)]
  simp only [e]
  unfold cdDemand
  rw [← Finset.sum_div, ← Finset.mul_sum, total_wealth L θ π hθ]

/-- **Ownership neutrality of aggregate demand, from utility maximisation.** -/
theorem optimal_demand_ownership_neutral (α p : S → ℝ) (hα : ∀ s, 0 < α s)
    (hsum : ∑ s, α s = 1) (hp : ∀ s, 0 < p s) (L θ θ' : H → ℝ) (π : ℝ)
    (hθ : ∑ h, θ h = 1) (hθ' : ∑ h, θ' h = 1)
    (hw : ∀ h, 0 < wealth L θ π h) (hw' : ∀ h, 0 < wealth L θ' π h)
    (x x' : H → S → ℝ) (hx : ∀ h, IsBest α p (wealth L θ π h) (x h))
    (hx' : ∀ h, IsBest α p (wealth L θ' π h) (x' h)) (s : S) :
    ∑ h, x h s = ∑ h, x' h s := by
  rw [optimal_aggregate α p hα hsum hp L θ π hθ hw x hx s,
    optimal_aggregate α p hα hsum hp L θ' π hθ' hw' x' hx' s]

/-- **Ownership neutrality of clearing prices, from utility maximisation.** A price at
which optimal demands clear the market under one ownership distribution clears it under
every other. -/
theorem optimal_clearing_neutral (α p y : S → ℝ) (hα : ∀ s, 0 < α s)
    (hsum : ∑ s, α s = 1) (hp : ∀ s, 0 < p s) (L θ θ' : H → ℝ) (π : ℝ)
    (hθ : ∑ h, θ h = 1) (hθ' : ∑ h, θ' h = 1)
    (hw : ∀ h, 0 < wealth L θ π h) (hw' : ∀ h, 0 < wealth L θ' π h)
    (x x' : H → S → ℝ) (hx : ∀ h, IsBest α p (wealth L θ π h) (x h))
    (hx' : ∀ h, IsBest α p (wealth L θ' π h) (x' h))
    (hclear : ∀ s, ∑ h, x h s = y s) : ∀ s, ∑ h, x' h s = y s := fun s => by
  rw [← hclear s]
  exact (optimal_demand_ownership_neutral α p hα hsum hp L θ θ' π hθ hθ' hw hw' x x'
    hx hx' s).symm

/-- Each household's optimal consumption is its wealth share of aggregate consumption. -/
theorem optimal_consumption_share (α p : S → ℝ) (hα : ∀ s, 0 < α s)
    (hsum : ∑ s, α s = 1) (hp : ∀ s, 0 < p s) (L θ : H → ℝ) (π : ℝ)
    (hθ : ∑ h, θ h = 1) (hw : ∀ h, 0 < wealth L θ π h) (x : H → S → ℝ)
    (hx : ∀ h, IsBest α p (wealth L θ π h) (x h)) (h : H) (s : S) :
    x h s = (wealth L θ π h / ((∑ k, L k) + π)) * ∑ k, x k s := by
  have hW : (∑ k, L k) + π ≠ 0 := by
    rw [← total_wealth L θ π hθ]
    have : (0:ℝ) < ∑ k, wealth L θ π k := by
      obtain ⟨k⟩ : Nonempty H := ⟨h⟩
      exact Finset.sum_pos (fun k _ => hw k) ⟨k, Finset.mem_univ _⟩
    exact this.ne'
  rw [optimal_aggregate α p hα hsum hp L θ π hθ hw x hx s,
    best_eq α p _ hα hsum hp (hw h) (x h) (hx h)]
  unfold cdDemand
  have := (hp s).ne'
  field_simp

end DerivedNeutrality

#print axioms DerivedNeutrality.total_wealth
#print axioms DerivedNeutrality.term_le
#print axioms DerivedNeutrality.term_lt
#print axioms DerivedNeutrality.demand_budget
#print axioms DerivedNeutrality.demand_optimal
#print axioms DerivedNeutrality.demand_unique
#print axioms DerivedNeutrality.cd_isBest
#print axioms DerivedNeutrality.best_eq
#print axioms DerivedNeutrality.optimal_aggregate
#print axioms DerivedNeutrality.optimal_demand_ownership_neutral
#print axioms DerivedNeutrality.optimal_clearing_neutral
#print axioms DerivedNeutrality.optimal_consumption_share
