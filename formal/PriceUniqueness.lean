import Mathlib

/-!
Stage 276: the ownership state prices are the only supporting prices.

States `S`, probabilities `π`, a differentiable felicity `u` with derivative `m` on the
positive reals.

* `foc` — if a strictly positive bundle `x` is optimal among strictly positive bundles
  costing no more than itself at strictly positive prices `p`, then
  `π s * m (x s) / p s` is the same in every state;
* `price_proportional` — if the optimal bundle is a share `w * Y s` of output and `m` is
  homogeneous, then `p` is proportional to `π s * m (Y s)`.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace PriceUniqueness

variable {S : Type*} [Fintype S]

/-- **First-order condition.** -/
theorem foc (π p x : S → ℝ) (u m : ℝ → ℝ) (hp : ∀ s, 0 < p s) (hx : ∀ s, 0 < x s)
    (hu : ∀ y : ℝ, 0 < y → HasDerivAt u (m y) y)
    (hopt : ∀ x' : S → ℝ, (∀ r, 0 < x' r) → ∑ r, p r * x' r ≤ ∑ r, p r * x r →
      ∑ r, π r * u (x' r) ≤ ∑ r, π r * u (x r))
    (s t : S) : π s * m (x s) / p s = π t * m (x t) / p t := by
  classical
  set d : S → ℝ := fun r => (if r = s then 1 / p s else 0) - (if r = t then 1 / p t else 0)
    with hd
  have hcost0 : ∑ r, p r * d r = 0 := by
    simp only [hd, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [mul_one_div_cancel (hp s).ne', mul_one_div_cancel (hp t).ne', sub_self]
  have hcost : ∀ ε : ℝ, ∑ r, p r * (x r + ε * d r) = ∑ r, p r * x r := by
    intro ε
    have e : ∀ r, p r * (x r + ε * d r) = p r * x r + ε * (p r * d r) := fun r => by ring
    rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_add_distrib, ← Finset.mul_sum,
      hcost0, mul_zero, add_zero]
  have hterm : ∀ r, HasDerivAt (fun ε : ℝ => π r * u (x r + ε * d r))
      (π r * (m (x r) * d r)) 0 := by
    intro r
    have hin : HasDerivAt (fun ε : ℝ => x r + ε * d r) (d r) 0 := by
      have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (d r)).const_add (x r)
      simpa using h1
    have hout : HasDerivAt u (m (x r)) (x r + 0 * d r) := by
      have h2 := hu (x r) (hx r)
      simpa using h2
    exact (hout.comp 0 hin).const_mul (π r)
  have hderiv : HasDerivAt (fun ε : ℝ => ∑ r, π r * u (x r + ε * d r))
      (∑ r, π r * (m (x r) * d r)) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hterm r)
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, ∀ r, 0 < x r + ε * d r := by
    rw [Filter.eventually_all]
    intro r
    have hc : ContinuousAt (fun ε : ℝ => x r + ε * d r) 0 := by fun_prop
    have h0 : (0 : ℝ) < x r + 0 * d r := by simpa using hx r
    exact hc.tendsto.eventually (lt_mem_nhds h0)
  have hmax : IsLocalMax (fun ε : ℝ => ∑ r, π r * u (x r + ε * d r)) 0 := by
    filter_upwards [hpos] with ε hε
    have h1 := hopt (fun r => x r + ε * d r) hε (hcost ε).le
    simpa using h1
  have hzero := hmax.hasDerivAt_eq_zero hderiv
  simp only [hd, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hzero
  linear_combination hzero

/-- **The supporting prices are the ownership prices up to scale.** -/
theorem price_proportional (π p Y : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ)
    (hp : ∀ s, 0 < p s) (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hu : ∀ y : ℝ, 0 < y → HasDerivAt u (m y) y)
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : h w ≠ 0)
    (hopt : ∀ x' : S → ℝ, (∀ r, 0 < x' r) → ∑ r, p r * x' r ≤ ∑ r, p r * (w * Y r) →
      ∑ r, π r * u (x' r) ≤ ∑ r, π r * u (w * Y r))
    (s t : S) : p s * (π t * m (Y t)) = p t * (π s * m (Y s)) := by
  have h1 : π s * m (w * Y s) / p s = π t * m (w * Y t) / p t :=
    foc π p (fun r => w * Y r) u m hp (fun r => mul_pos hw (hY r)) hu hopt s t
  rw [hhom (Y s) (hY s), hhom (Y t) (hY t), div_eq_div_iff (hp s).ne' (hp t).ne'] at h1
  apply mul_left_cancel₀ hh
  linear_combination -h1

end PriceUniqueness

end

#print axioms PriceUniqueness.foc
#print axioms PriceUniqueness.price_proportional
