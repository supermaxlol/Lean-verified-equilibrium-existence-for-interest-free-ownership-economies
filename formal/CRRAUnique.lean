import Mathlib

/-!
Stage 268: ownership implements the complete-markets equilibrium for homothetic utility.

Generalises stage 266 from log utility to any felicity `u` with a marginal-utility function
`m` that is a supergradient (`u a ≤ u b + m b * (a - b)`) and homogeneous
(`m (w * y) = h w * m y`).  State prices are `π s * m (Y s)`.

* `share_optimal` — the share bundle `w * Y s` maximises expected utility in the budget set;
* `ownership_equilibrium` — shares are positive, sum to one, each household's share bundle
  costs exactly its endowment, is optimal, and every state market clears exactly;
* `log_supergradient`, `log_homogeneous` — log utility satisfies the hypotheses.

The hypotheses are not verified here for power utility.
-/

noncomputable section

open Finset BigOperators

namespace HomotheticOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

theorem share_optimal (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * (w * Y s)) :
    ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w * Y s) := by
  have hterm : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
    intro s
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s))
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - π s * m (Y s) * (w * Y s)) := by
      ring
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have h3 := mul_nonneg hh (sub_nonneg.2 hbud)
  linarith

/-- **Ownership implements the complete-markets equilibrium.** -/
theorem ownership_equilibrium [Nonempty S] (π Y : S → ℝ) (ω : I → S → ℝ) (u m h : ℝ → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s * m (Y s) * (w i * Y s) = ∑ s, π s * m (Y s) * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s * m (Y s) * x s ≤ ∑ s, π s * m (Y s) * ω i s →
        ∑ s, π s * u (x s) ≤ ∑ s, π s * u (w i * Y s)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s := by
  have hp : ∀ s, 0 < π s * m (Y s) := fun s => mul_pos (hπ s) (hm _ (hY s))
  have hT : 0 < ∑ s, π s * m (Y s) * Y s :=
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hY s)) Finset.univ_nonempty
  have hWi : ∀ i, 0 < ∑ s, π s * m (Y s) * ω i s := fun i =>
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hωpos i s)) Finset.univ_nonempty
  have hwpos : ∀ i, 0 < (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s :=
    fun i => div_pos (hWi i) hT
  have htot : ∑ i, ∑ s, π s * m (Y s) * ω i s = ∑ s, π s * m (Y s) * Y s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, hω s])
  have hsum : ∑ i, (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s = 1 := by
    rw [← Finset.sum_div, htot, div_self hT.ne']
  have hcost : ∀ i, ∑ s, π s * m (Y s)
        * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
      = ∑ s, π s * m (Y s) * ω i s := by
    intro i
    have e : ∀ s, π s * m (Y s)
          * ((∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s) * Y s)
        = (∑ s, π s * m (Y s) * ω i s) / (∑ s, π s * m (Y s) * Y s)
          * (π s * m (Y s) * Y s) := fun s => by ring
    rw [Finset.sum_congr rfl (fun s _ => e s), ← Finset.mul_sum, div_mul_cancel₀ _ hT.ne']
  refine ⟨fun i => (∑ s, π s * m (Y s) * ω i s) / ∑ s, π s * m (Y s) * Y s, hwpos, hsum,
    hcost, fun i x hx hbud => ?_, fun s => ?_⟩
  · refine share_optimal π Y x u m h _ (fun s => (hπ s).le) hY (hwpos i) hsg
      (fun y hy => hhom _ y (hwpos i) hy) (hh _ (hwpos i)) hx ?_
    rw [hcost i]
    exact hbud
  · rw [← Finset.sum_mul, hsum, one_mul, hω s]

theorem log_supergradient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ Real.log b + 1 / b * (a - b) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have e : 1 / b * (a - b) = a / b - 1 := by
    have := hb.ne'
    field_simp
  rw [e]
  linarith

theorem log_homogeneous (w y : ℝ) (hw : 0 < w) (hy : 0 < y) :
    1 / (w * y) = 1 / w * (1 / y) := by
  have := hw.ne'
  have := hy.ne'
  field_simp

end HomotheticOwnership

end


/-!
Stage 270: with strictly concave homothetic utility the ownership bundle is the unique
optimum, and a fixed claim layered on it is strictly costly.

Setting of stage 268 with the supergradient inequality strict off the diagonal
(`u a < u b + m b * (a - b)` for `a ≠ b`).

* `share_strictly_optimal` — any affordable bundle that differs from the share bundle in
  some state gives strictly lower expected utility;
* `fixed_claim_strictly_worse` — a bundle `a * Y s - b` with `b ≠ 0` (a share of output
  plus or minus a fixed amount), when output varies across two states, is strictly worse
  than the share bundle of the same cost;
* `log_strict_supergradient` — log utility satisfies the strict hypothesis.
-/

noncomputable section

open Finset BigOperators

namespace HomotheticFixedClaim

variable {S : Type*} [Fintype S]

theorem share_strictly_optimal (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (hx : ∀ s, 0 < x s)
    (hbud : ∑ s, π s * m (Y s) * x s ≤ w * ∑ s, π s * m (Y s) * Y s)
    (s0 : S) (hne : x s0 ≠ w * Y s0) :
    ∑ s, π s * u (x s) < ∑ s, π s * u (w * Y s) := by
  have hstrict : ∀ s, x s ≠ w * Y s → π s * u (x s) < π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
    intro s hs
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s)) hs
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_lt_mul_of_pos_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
      ring
    linarith
  have hweak : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
    intro s
    by_cases hs : x s = w * Y s
    · have e : h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) = 0 := by
        rw [hs]; ring
      rw [e, hs, add_zero]
    · exact (hstrict s hs).le
  have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hweak s)
    ⟨s0, Finset.mem_univ s0, hstrict s0 hne⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  have := mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.2 hbud)
  linarith

/-- **A fixed claim on top of ownership is strictly costly.** -/
theorem fixed_claim_strictly_worse (π Y : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hh : 0 ≤ h w)
    (a b : ℝ) (hb : b ≠ 0) (s1 s2 : S) (hvar : Y s1 ≠ Y s2)
    (hpos : ∀ s, 0 < a * Y s - b)
    (hbud : ∑ s, π s * m (Y s) * (a * Y s - b) ≤ w * ∑ s, π s * m (Y s) * Y s) :
    ∑ s, π s * u (a * Y s - b) < ∑ s, π s * u (w * Y s) := by
  have hex : ∃ s0, a * Y s0 - b ≠ w * Y s0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon s1
    have h2 := hcon s2
    have h3 : (a - w) * (Y s1 - Y s2) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with hz | hz
    · apply hb
      have haw : a = w := by linarith
      rw [haw] at h1
      linarith
    · exact hvar (by linarith)
  obtain ⟨s0, hs0⟩ := hex
  exact share_strictly_optimal π Y (fun s => a * Y s - b) u m h w hπ hY hw hsg hhom hh
    hpos hbud s0 hs0

theorem log_strict_supergradient (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log a < Real.log b + 1 / b * (a - b) := by
  have h1 : a / b ≠ 1 := fun hc => hab ((div_eq_one_iff_eq hb.ne').1 hc)
  have h2 := Real.log_lt_sub_one_of_pos (div_pos ha hb) h1
  rw [Real.log_div ha.ne' hb.ne'] at h2
  have e : 1 / b * (a - b) = a / b - 1 := by field_simp
  linarith

end HomotheticFixedClaim

end


/-!
Stage 275: every Pareto-efficient interior allocation is a division of ownership.

Converse of stage 269, under the strict hypotheses of stage 270.  If a strictly positive
allocation `x` uses exactly output and is Pareto efficient, there are shares `w i > 0`
summing to one with `x i s = w i * Y s` in every state.

Proof: take `x` itself as the endowment.  Stage 268 gives a share allocation that every
household weakly prefers; efficiency rules out a strict gain; strict optimality (stage 270)
then forces `x i` to be the share bundle.
-/

noncomputable section

open Finset BigOperators

namespace EfficientIsOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Efficient allocations are divisions of ownership.** -/
theorem efficient_is_ownership [Nonempty S] (π Y : S → ℝ) (u m h : ℝ → ℝ)
    (x : I → S → ℝ) (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s)
    (hx : ∀ i s, 0 < x i s) (hsum : ∀ s, ∑ i, x i s = Y s)
    (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w)
    (heff : ∀ x' : I → S → ℝ, (∀ i s, 0 < x' i s) → (∀ s, ∑ i, x' i s ≤ Y s) →
      (∀ i, ∑ s, π s * u (x i s) ≤ ∑ s, π s * u (x' i s)) →
      ∀ k, ¬ ∑ s, π s * u (x k s) < ∑ s, π s * u (x' k s)) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ i s, x i s = w i * Y s := by
  have hweaksg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b) := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab, sub_self, mul_zero, add_zero]
    · exact (hsg a b ha hb hab).le
  obtain ⟨w, hw, hw1, hcost, hopt, hclear⟩ :=
    HomotheticOwnership.ownership_equilibrium π Y x u m h hπ hY hx hsum hm hweaksg hhom hh
  refine ⟨w, hw, hw1, fun i s0 => ?_⟩
  by_contra hne
  have hbud : ∑ s, π s * m (Y s) * x i s ≤ w i * ∑ s, π s * m (Y s) * Y s := by
    rw [← hcost i, Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl (fun s _ => by ring))
  have hstrict := HomotheticFixedClaim.share_strictly_optimal π Y (x i) u m h (w i) hπ hY
    (hw i) hsg (fun y hy => hhom (w i) y (hw i) hy) (hh _ (hw i)) (hx i) hbud s0 hne
  exact heff (fun i s => w i * Y s) (fun i s => mul_pos (hw i) (hY s))
    (fun s => le_of_eq ((hclear s).trans (hsum s)))
    (fun i => hopt i (x i) (hx i) le_rfl) i hstrict

end EfficientIsOwnership

end


/-!
Stage 280: every interior competitive equilibrium is a division of ownership.

Stage 268 exhibited one equilibrium in which each household holds a share of output.
Here: at ANY strictly positive prices, if a strictly positive allocation uses exactly
output and each household's bundle is optimal among bundles costing no more, then the
allocation is a division of ownership.  The equilibrium allocation is therefore unique
in kind: there is nothing else an equilibrium can be.

Proof: first welfare theorem (felicity is increasing because marginal utility is positive),
then stage 275.
-/

noncomputable section

open Finset BigOperators

namespace EquilibriumIsOwnership

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Any interior equilibrium is a division of ownership.** -/
theorem equilibrium_is_ownership [Nonempty S] (π Y p : S → ℝ) (u m h : ℝ → ℝ)
    (x : I → S → ℝ) (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hp : ∀ s, 0 < p s)
    (hx : ∀ i s, 0 < x i s) (hsum : ∀ s, ∑ i, x i s = Y s)
    (hm : ∀ y : ℝ, 0 < y → 0 < m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → u a < u b + m b * (a - b))
    (hhom : ∀ w y : ℝ, 0 < w → 0 < y → m (w * y) = h w * m y)
    (hh : ∀ w : ℝ, 0 < w → 0 ≤ h w)
    (hopt : ∀ i (x' : S → ℝ), (∀ s, 0 < x' s) →
      ∑ s, p s * x' s ≤ ∑ s, p s * x i s →
      ∑ s, π s * u (x' s) ≤ ∑ s, π s * u (x i s)) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ i s, x i s = w i * Y s := by
  classical
  apply EfficientIsOwnership.efficient_is_ownership π Y u m h x hπ hY hx hsum hm hsg hhom hh
  intro x' hx' hfeas hweak k hstrict
  have hmono : ∀ a b : ℝ, 0 < a → a < b → u a < u b := by
    intro a b ha hab
    have h1 := hsg a b ha (ha.trans hab) hab.ne
    have h2 := mul_neg_of_pos_of_neg (hm b (ha.trans hab)) (sub_neg.2 hab)
    linarith
  have hk : ∑ s, p s * x k s < ∑ s, p s * x' k s := by
    by_contra hc
    exact absurd (hopt k (x' k) (hx' k) (not_lt.1 hc)) (not_le.2 hstrict)
  have hall : ∀ i, ∑ s, p s * x i s ≤ ∑ s, p s * x' i s := by
    intro i
    by_contra hc
    have hc' : ∑ s, p s * x' i s < ∑ s, p s * x i s := not_le.1 hc
    obtain ⟨s0⟩ := ‹Nonempty S›
    set ε : ℝ := (∑ s, p s * x i s - ∑ s, p s * x' i s) / p s0 with hε
    have hεpos : 0 < ε := div_pos (sub_pos.2 hc') (hp s0)
    have hpε : p s0 * ε = ∑ s, p s * x i s - ∑ s, p s * x' i s := by
      rw [hε, mul_comm]
      exact div_mul_cancel₀ _ (hp s0).ne'
    have hcost : ∑ s, p s * (x' i s + if s = s0 then ε else 0) = ∑ s, p s * x i s := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      linarith
    have hpos'' : ∀ s, 0 < x' i s + if s = s0 then ε else 0 := by
      intro s
      have := hx' i s
      split_ifs <;> linarith
    have hle := hopt i (fun s => x' i s + if s = s0 then ε else 0) hpos'' hcost.le
    have hlt : ∑ s, π s * u (x' i s)
        < ∑ s, π s * u (x' i s + if s = s0 then ε else 0) := by
      apply Finset.sum_lt_sum
      · intro s _
        apply mul_le_mul_of_nonneg_left _ (hπ s).le
        split_ifs with hs
        · exact (hmono _ _ (hx' i s) (by linarith)).le
        · rw [add_zero]
      · refine ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left ?_ (hπ s0)⟩
        simp only [↓reduceIte]
        exact hmono _ _ (hx' i s0) (by linarith)
    linarith [hweak i]
  have hsumlt : ∑ i, ∑ s, p s * x i s < ∑ i, ∑ s, p s * x' i s :=
    Finset.sum_lt_sum (fun i _ => hall i) ⟨k, Finset.mem_univ _, hk⟩
  have e1 : ∑ i, ∑ s, p s * x i s = ∑ s, p s * Y s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, hsum s])
  have e2 : ∑ i, ∑ s, p s * x' i s ≤ ∑ s, p s * Y s := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun s _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hfeas s) (hp s).le)
  linarith

end EquilibriumIsOwnership

end


/-!
Stage 279: every constant-relative-risk-aversion utility satisfies the hypotheses.

For any exponent `p < 1`, `p ≠ 0` (relative risk aversion `1 - p`), the felicity
`u c = (1 / p) * c ^ p` has marginal utility `m y = y ^ (p - 1)`, which is homogeneous with
`h w = w ^ (p - 1)`, and satisfies the supergradient inequality on the positive reals.
Stage 268 therefore applies to the whole CRRA class (the log case is stage 266).
-/

noncomputable section

open Finset BigOperators

namespace GeneralCRRA

/-- Bernoulli from below, negative exponent. -/
theorem bernoulli_neg (p t : ℝ) (hp : p < 0) (ht : 0 < t) : 1 + p * (t - 1) ≤ t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_le_sub_one_of_pos ht
  have h3 : p * (t - 1) ≤ p * Real.log t := mul_le_mul_of_nonpos_left h2 hp.le
  linarith

/-- Strict version away from `t = 1`. -/
theorem bernoulli_neg_strict (p t : ℝ) (hp : p < 0) (ht : 0 < t) (hne : t ≠ 1) :
    1 + p * (t - 1) < t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_lt_sub_one_of_pos ht hne
  have h3 : p * (t - 1) < p * Real.log t := mul_lt_mul_of_neg_left h2 hp
  linarith

/-- Bernoulli from above, exponent between zero and one. -/
theorem bernoulli_pos (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    t ^ p ≤ 1 + p * (t - 1) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hp.le (by linarith : (0 : ℝ) ≤ 1 - p)
    ht.le zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- **Supergradient inequality for CRRA utility.** -/
theorem crra_supergradient (p a b : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    1 / p * a ^ p ≤ 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  have ht : 0 < a / b := div_pos ha hb
  have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hA : a ^ p = (a / b) ^ p * b ^ p := by
    rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
  have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp
  have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp0
  have hkey : (a / b) ^ p * (1 / p) ≤ 1 / p + (a / b - 1) := by
    rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · have hk := bernoulli_neg p (a / b) hneg ht
      have hc : 1 / p < 0 := one_div_neg.2 hneg
      have h := mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
    · have hk := bernoulli_pos p (a / b) hpos hp1 ht
      have hc : 0 < 1 / p := one_div_pos.2 hpos
      have h := mul_nonneg hc.le (sub_nonneg.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
  have h2 := mul_le_mul_of_nonneg_left hkey hB.le
  rw [hA, hm]
  linarith

/-- Strict supergradient when relative risk aversion exceeds one. -/
theorem crra_strict_supergradient (p a b : ℝ) (hp : p < 0) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) : 1 / p * a ^ p < 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  have ht : 0 < a / b := div_pos ha hb
  have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hA : a ^ p = (a / b) ^ p * b ^ p := by
    rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
  have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp
  have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp.ne
  have hne' : a / b ≠ 1 := fun h => hne ((div_eq_one_iff_eq hb.ne').1 h)
  have hk := bernoulli_neg_strict p (a / b) hp ht hne'
  have hc : 1 / p < 0 := one_div_neg.2 hp
  have h := mul_pos_of_neg_of_neg hc (sub_neg.2 hk)
  have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
      = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
  rw [e, hpc, one_mul] at h
  have h2 := mul_lt_mul_of_pos_left (by linarith : (a / b) ^ p * (1 / p) < 1 / p + (a / b - 1)) hB
  rw [hA, hm]
  linarith

theorem crra_homogeneous (p w y : ℝ) (hw : 0 < w) (hy : 0 < y) :
    (w * y) ^ (p - 1) = w ^ (p - 1) * y ^ (p - 1) := Real.mul_rpow hw.le hy.le

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **Ownership equilibrium for every CRRA utility.** -/
theorem crra_ownership_equilibrium [Nonempty S] (p : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0)
    (π Y : S → ℝ) (ω : I → S → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hωpos : ∀ i s, 0 < ω i s)
    (hω : ∀ s, ∑ i, ω i s = Y s) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ i, ∑ s, π s * Y s ^ (p - 1) * (w i * Y s) = ∑ s, π s * Y s ^ (p - 1) * ω i s) ∧
      (∀ i (x : S → ℝ), (∀ s, 0 < x s) →
        ∑ s, π s * Y s ^ (p - 1) * x s ≤ ∑ s, π s * Y s ^ (p - 1) * ω i s →
        ∑ s, π s * (1 / p * x s ^ p) ≤ ∑ s, π s * (1 / p * (w i * Y s) ^ p)) ∧
      ∀ s, ∑ i, w i * Y s = ∑ i, ω i s :=
  HomotheticOwnership.ownership_equilibrium π Y ω (fun c => 1 / p * c ^ p)
    (fun y => y ^ (p - 1)) (fun w => w ^ (p - 1)) hπ hY hωpos hω
    (fun _ hy => Real.rpow_pos_of_pos hy _)
    (fun a b ha hb => crra_supergradient p a b hp1 hp0 ha hb)
    (fun w y hw hy => crra_homogeneous p w y hw hy)
    (fun _ hw => (Real.rpow_pos_of_pos hw _).le)

end GeneralCRRA

end


/-!
Stage 281: with any CRRA utility, every interior equilibrium is a division of ownership.

The strict supergradient inequality is proved for every exponent `p < 1`, `p ≠ 0`
(stage 279 had it only for `p < 0`), and stage 280 is applied.
-/

noncomputable section

open Finset BigOperators

namespace CRRAUnique

/-- Strict Bernoulli, exponent between zero and one. -/
theorem bernoulli_pos_strict (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hne : t ≠ 1) :
    t ^ p < 1 + p * (t - 1) := by
  have hq : 0 < 1 + p * (t - 1) := by nlinarith
  have hc := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 ht) (Set.mem_Ioi.2 one_pos) hne hp
    (by linarith : (0 : ℝ) < 1 - p) (by ring : p + (1 - p) = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at hc
  have e : p * t + (1 - p) = 1 + p * (t - 1) := by ring
  rw [e] at hc
  rw [Real.rpow_def_of_pos ht, ← Real.exp_log hq]
  apply Real.exp_lt_exp.2
  linarith

/-- **Strict supergradient inequality for every CRRA utility.** -/
theorem crra_strict_supergradient_all (p a b : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    1 / p * a ^ p < 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · exact GeneralCRRA.crra_strict_supergradient p a b hneg ha hb hne
  · have ht : 0 < a / b := div_pos ha hb
    have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
    have hA : a ^ p = (a / b) ^ p * b ^ p := by
      rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
    have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
      rw [Real.rpow_sub_one hb.ne']
      field_simp
    have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp0
    have hne' : a / b ≠ 1 := fun h => hne ((div_eq_one_iff_eq hb.ne').1 h)
    have hk := bernoulli_pos_strict p (a / b) hpos hp1 ht hne'
    have hc : 0 < 1 / p := one_div_pos.2 hpos
    have h := mul_pos hc (sub_pos.2 hk)
    have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
        = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
    rw [e, hpc, one_mul] at h
    have h2 := mul_lt_mul_of_pos_left
      (by linarith : (a / b) ^ p * (1 / p) < 1 / p + (a / b - 1)) hB
    rw [hA, hm]
    linarith

variable {I S : Type*} [Fintype I] [Fintype S]

/-- **With CRRA utility every interior equilibrium is a division of ownership.** -/
theorem crra_equilibrium_is_ownership [Nonempty S] (p : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0)
    (π Y q : S → ℝ) (x : I → S → ℝ)
    (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) (hq : ∀ s, 0 < q s)
    (hx : ∀ i s, 0 < x i s) (hsum : ∀ s, ∑ i, x i s = Y s)
    (hopt : ∀ i (x' : S → ℝ), (∀ s, 0 < x' s) →
      ∑ s, q s * x' s ≤ ∑ s, q s * x i s →
      ∑ s, π s * (1 / p * x' s ^ p) ≤ ∑ s, π s * (1 / p * x i s ^ p)) :
    ∃ w : I → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∀ i s, x i s = w i * Y s :=
  EquilibriumIsOwnership.equilibrium_is_ownership π Y q (fun c => 1 / p * c ^ p)
    (fun y => y ^ (p - 1)) (fun w => w ^ (p - 1)) x hπ hY hq hx hsum
    (fun _ hy => Real.rpow_pos_of_pos hy _)
    (fun a b ha hb hne => crra_strict_supergradient_all p a b hp1 hp0 ha hb hne)
    (fun w y hw hy => GeneralCRRA.crra_homogeneous p w y hw hy)
    (fun _ hw => (Real.rpow_pos_of_pos hw _).le) hopt

end CRRAUnique

end

#print axioms CRRAUnique.bernoulli_pos_strict
#print axioms CRRAUnique.crra_strict_supergradient_all
#print axioms CRRAUnique.crra_equilibrium_is_ownership
