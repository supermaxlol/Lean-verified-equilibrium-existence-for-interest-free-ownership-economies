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


/-!
Stage 282: heterogeneous risk attitudes.

Two results that mark the boundary of the pure-ownership theorems (stages 268-281).

1. Shifted homothetic felicities (the HARA class with a common slope).  Household `i` has
   felicity `v (c + a i)`, where `v` has a homogeneous marginal utility `M`.  Then the
   bundle `w i * (Y s + A) - a i`, `A = ∑ a`, is optimal at the prices `π s * M (Y s + A)`,
   these bundles clear the market, and each is a share of output plus a state-independent
   payment; the payments sum to zero.

2. Different exponents.  If two households have marginal utilities `y ^ a` and `y ^ b`
   with `a ≠ b` and output differs across two states, there are NO prices at which both
   optimally hold a pure share of output.
-/

noncomputable section

open Finset BigOperators

namespace HeterogeneousSharing

variable {I S : Type*} [Fintype I] [Fintype S]

/-- A share of `Y + A` less the shift is optimal on its budget set. -/
theorem hara_optimal (π Y x' : S → ℝ) (v M h : ℝ → ℝ) (w a A : ℝ)
    (hπ : ∀ s, 0 < π s) (hYA : ∀ s, 0 < Y s + A) (hw : 0 < w)
    (hsg : ∀ c b : ℝ, 0 < c → 0 < b → v c ≤ v b + M b * (c - b))
    (hhom : ∀ y : ℝ, 0 < y → M (w * y) = h w * M y) (hh : 0 ≤ h w)
    (hx' : ∀ s, 0 < x' s + a)
    (hbud : ∑ s, π s * M (Y s + A) * x' s
      ≤ ∑ s, π s * M (Y s + A) * (w * (Y s + A) - a)) :
    ∑ s, π s * v (x' s + a) ≤ ∑ s, π s * v (w * (Y s + A)) := by
  have hterm : ∀ s, π s * v (x' s + a) ≤ π s * v (w * (Y s + A))
      + h w * (π s * M (Y s + A) * x' s - π s * M (Y s + A) * (w * (Y s + A) - a)) := by
    intro s
    have h1 := hsg (x' s + a) (w * (Y s + A)) (hx' s) (mul_pos hw (hYA s))
    rw [hhom _ (hYA s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    calc π s * v (x' s + a)
        ≤ π s * (v (w * (Y s + A)) + h w * M (Y s + A) * (x' s + a - w * (Y s + A))) := h2
      _ = _ := by ring
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  have h3 := mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.2 hbud)
  linarith

omit [Fintype S] in
/-- The bundles use exactly output. -/
theorem hara_clears (Y : S → ℝ) (w a : I → ℝ) (hw1 : ∑ i, w i = 1) (s : S) :
    ∑ i, (w i * (Y s + ∑ j, a j) - a i) = Y s := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
  ring

/-- Each bundle is a share of output plus a state-independent payment. -/
theorem linear_rule (w a A y : ℝ) : w * (y + A) - a = w * y + (w * A - a) := by ring

/-- The state-independent payments sum to zero. -/
theorem side_payments_cancel (w a : I → ℝ) (hw1 : ∑ i, w i = 1) :
    ∑ i, (w i * (∑ j, a j) - a i) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1]
  ring

/-- **Pure ownership fails with different risk aversion.** -/
theorem ownership_fails_heterogeneous (π q Y : S → ℝ) (u₁ u₂ : ℝ → ℝ) (a b w₁ w₂ : ℝ)
    (hπ : ∀ s, 0 < π s) (hq : ∀ s, 0 < q s) (hY : ∀ s, 0 < Y s)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hu₁ : ∀ y : ℝ, 0 < y → HasDerivAt u₁ (y ^ a) y)
    (hu₂ : ∀ y : ℝ, 0 < y → HasDerivAt u₂ (y ^ b) y)
    (hopt₁ : ∀ x' : S → ℝ, (∀ r, 0 < x' r) → ∑ r, q r * x' r ≤ ∑ r, q r * (w₁ * Y r) →
      ∑ r, π r * u₁ (x' r) ≤ ∑ r, π r * u₁ (w₁ * Y r))
    (hopt₂ : ∀ x' : S → ℝ, (∀ r, 0 < x' r) → ∑ r, q r * x' r ≤ ∑ r, q r * (w₂ * Y r) →
      ∑ r, π r * u₂ (x' r) ≤ ∑ r, π r * u₂ (w₂ * Y r))
    (s t : S) (hst : Y s ≠ Y t) : a = b := by
  have key : ∀ (u : ℝ → ℝ) (c w : ℝ), 0 < w →
      (∀ y : ℝ, 0 < y → HasDerivAt u (y ^ c) y) →
      (∀ x' : S → ℝ, (∀ r, 0 < x' r) → ∑ r, q r * x' r ≤ ∑ r, q r * (w * Y r) →
        ∑ r, π r * u (x' r) ≤ ∑ r, π r * u (w * Y r)) →
      π s * q t * Y s ^ c = π t * q s * Y t ^ c := by
    intro u c w hw hu hopt
    have h1 : π s * (w * Y s) ^ c / q s = π t * (w * Y t) ^ c / q t :=
      PriceUniqueness.foc π q (fun r => w * Y r) u (fun y => y ^ c) hq
        (fun r => mul_pos hw (hY r)) hu hopt s t
    rw [div_eq_div_iff (hq s).ne' (hq t).ne', Real.mul_rpow hw.le (hY s).le,
      Real.mul_rpow hw.le (hY t).le] at h1
    have hW : 0 < w ^ c := Real.rpow_pos_of_pos hw c
    apply mul_left_cancel₀ hW.ne'
    linear_combination h1
  have E1 := key u₁ a w₁ hw₁ hu₁ hopt₁
  have E2 := key u₂ b w₂ hw₂ hu₂ hopt₂
  have hK1 : 0 < π s * q t := mul_pos (hπ s) (hq t)
  have hK2 : 0 < π t * q s := mul_pos (hπ t) (hq s)
  have hx : Y s ^ a * Y t ^ b = Y t ^ a * Y s ^ b := by
    apply mul_left_cancel₀ (mul_pos hK1 hK2).ne'
    linear_combination (π t * q s * Y t ^ b) * E1 - (π t * q s * Y t ^ a) * E2
  have hsa := (Real.rpow_pos_of_pos (hY s) a).ne'
  have hsb := (Real.rpow_pos_of_pos (hY s) b).ne'
  have hta := (Real.rpow_pos_of_pos (hY t) a).ne'
  have htb := (Real.rpow_pos_of_pos (hY t) b).ne'
  have hl := congrArg Real.log hx
  rw [Real.log_mul hsa htb, Real.log_mul hta hsb, Real.log_rpow (hY s), Real.log_rpow (hY t),
    Real.log_rpow (hY t), Real.log_rpow (hY s)] at hl
  have hprod : (a - b) * (Real.log (Y s) - Real.log (Y t)) = 0 := by linear_combination hl
  rcases mul_eq_zero.1 hprod with h0 | h0
  · linarith
  · exact absurd (Real.log_injOn_pos (Set.mem_Ioi.2 (hY s)) (Set.mem_Ioi.2 (hY t))
      (by linarith)) hst

end HeterogeneousSharing

end

#print axioms HeterogeneousSharing.hara_optimal
#print axioms HeterogeneousSharing.hara_clears
#print axioms HeterogeneousSharing.linear_rule
#print axioms HeterogeneousSharing.side_payments_cancel
#print axioms HeterogeneousSharing.ownership_fails_heterogeneous
