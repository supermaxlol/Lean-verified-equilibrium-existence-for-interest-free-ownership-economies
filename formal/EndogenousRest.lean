import FixedPointTheorems.brouwer
import Mathlib

/-!
# Stage 365: a long-run distribution with wealth-dependent patience and access

Continues stages 356, 363 and 364 (definitions restated). Ownership shares `x` lie in the simplex.
Each period a household keeps the saved part of its ownership, `post h = s h x h / B` with
`B = ∑ s k x k`, and new units are issued at rate `g`: a fraction `σ` equally (`c` each,
`N c = 1`), the rest pro rata among households with access, weighted by an access intensity
`a h ∈ [0, 1]` (stage 356 with weights in place of a set):

`step h = (post h + g (σ c + (1 − σ) a h post h / W)) / (1 + g)`,  `W = ∑ a k post k`.

Here both the saving rate `s` and the access intensity `a` are functions of the whole current
distribution `x` (`Ψ`). This covers patience that depends on a household's own wealth (stage 363,
`s h = φ (x h)`), on its rank, or on the distribution as a whole, and access that depends on
wealth through any continuous rule.

* **Existence** (`exists_rest`): if the saving rule and the access rule are continuous on the
  simplex, saving rates are positive, access intensities are non-negative and some household with
  saved ownership has access (`W > 0`), then a long-run distribution exists: a point of the
  simplex mapped to itself. Every household holds at least `g σ c / (1 + g)` in it. The proof
  applies Brouwer's fixed-point theorem (`FixedPointTheorems.brouwer`) to the simplex.
* `exists_rest_patience`: full access, patience `φ (x h)` for any continuous positive `φ`.
* `exists_rest_access`: access intensities bounded below by some `α0 > 0`.
* **Forward-looking saving** (`exists_stationary_forward`): patience `β x h` may depend on the
  distribution; at a constant return `Q` the infinite-horizon rule of stage 364 saves the
  fraction `b Q ^ ((1 − γ) / γ)` (`stationary_rule`). A distribution together with the return
  `Q = (∑ β x k x k) ^ (−γ)` exists at which this saving rate is used, the return is the one the
  issuance step produces (`Q = 1 / B`), and the distribution reproduces itself.
* **No uniqueness** (`two_rest_continuous`): with a continuous, increasing patience rule
  (`φc`, linear between `1/5` and `4/5` and flat outside) both the equal distribution and
  `(1/5, 4/5)` are long-run distributions. Continuity alone does not restore uniqueness.

Limits: existence only; neither uniqueness nor convergence to a long-run distribution is proved
(the example rules out uniqueness in general). Discontinuous rules (the threshold patience of
stage 363, the all-or-nothing access sets of stage 356) are not covered. In
`exists_stationary_forward` the saving rate equals the stationary infinite-horizon rule only when
`b Q ^ ((1 − γ) / γ) < 1`, which is not checked by the theorem; optimality and the transition path
to the stationary state are not proved.
-/

noncomputable section

open Finset BigOperators

namespace EndogenousRest

variable {H : Type*} [Fintype H]

/-- The simplex of ownership distributions. -/
def Simp (H : Type*) [Fintype H] : Set (H → ℝ) := {x | (∀ h, 0 ≤ x h) ∧ ∑ h, x h = 1}

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def post (s x : H → ℝ) (h : H) : ℝ := s h * x h / B s x

def W (a s x : H → ℝ) : ℝ := ∑ k, a k * post s x k

/-- The issuance step with access intensities `a` (stage 356 with weights). -/
def stepA (g σ c : ℝ) (a s x : H → ℝ) (h : H) : ℝ :=
  (post s x h + g * (σ * c + (1 - σ) * (a h * post s x h / W a s x))) / (1 + g)

/-- The step with saving and access read off the current distribution. -/
def Ψ (g σ c : ℝ) (α sv : (H → ℝ) → H → ℝ) (x : H → ℝ) : H → ℝ :=
  stepA g σ c (α x) (sv x) x

theorem convex_Simp : Convex ℝ (Simp H) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun h => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 h)) (mul_nonneg hb (hy.1 h))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    linarith

theorem compact_Simp : IsCompact (Simp H) := by
  have hsub : Simp H ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
    intro x hx h _
    refine ⟨hx.1 h, ?_⟩
    rw [← hx.2]
    exact Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ h)
  have hcl : IsClosed (Simp H) := by
    have e : Simp H = (⋂ h, {x : H → ℝ | 0 ≤ x h}) ∩ {x | ∑ h, x h = 1} := by
      ext x
      simp [Simp]
    rw [e]
    exact (isClosed_iInter fun h => isClosed_le continuous_const (continuous_apply h)).inter
      (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

theorem B_pos (s x : H → ℝ) (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) : 0 < B s x := by
  obtain ⟨k, hk⟩ : ∃ k, 0 < x k := by
    by_contra hne
    push Not at hne
    have : ∑ h, x h ≤ 0 := Finset.sum_nonpos fun h _ => hne h
    linarith [hx.2]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hs j).le (hx.1 j))
    ⟨k, Finset.mem_univ _, mul_pos (hs k) hk⟩

theorem post_nonneg (s x : H → ℝ) (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) (h : H) :
    0 ≤ post s x h :=
  div_nonneg (mul_nonneg (hs h).le (hx.1 h)) (B_pos s x hs hx).le

theorem post_sum (s x : H → ℝ) (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) : ∑ h, post s x h = 1 := by
  unfold post
  rw [← Finset.sum_div]
  exact div_self (B_pos s x hs hx).ne'

theorem step_sum (g σ c : ℝ) (a s x : H → ℝ) (hg : 0 < g) (hc : (Fintype.card H : ℝ) * c = 1)
    (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) (hW : 0 < W a s x) :
    ∑ h, stepA g σ c a s x h = 1 := by
  have h1 : ∑ h, a h * post s x h / W a s x = 1 := by
    rw [← Finset.sum_div]
    exact div_self hW.ne'
  have h2 : ∑ _h : H, c = 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have e : ∑ h, (post s x h + g * (σ * c + (1 - σ) * (a h * post s x h / W a s x))) =
      ∑ h, post s x h + g * σ * ∑ _h : H, c +
        g * (1 - σ) * ∑ h, a h * post s x h / W a s x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  unfold stepA
  rw [← Finset.sum_div, e, post_sum s x hs hx, h1, h2,
    div_eq_one_iff_eq (by linarith : (0 : ℝ) < 1 + g).ne']
  ring

theorem step_floor (g σ c : ℝ) (a s x : H → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (ha : ∀ k, 0 ≤ a k) (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) (hW : 0 < W a s x) (h : H) :
    g * σ * c / (1 + g) ≤ stepA g σ c a s x h := by
  have hp := post_nonneg s x hs hx h
  have hq : 0 ≤ a h * post s x h / W a s x := div_nonneg (mul_nonneg (ha h) hp) hW.le
  have hr : 0 ≤ g * ((1 - σ) * (a h * post s x h / W a s x)) :=
    mul_nonneg hg.le (mul_nonneg (by linarith) hq)
  unfold stepA
  exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)

/-- **Existence of a long-run distribution** with saving and access rules that depend on the
whole distribution. -/
theorem exists_rest (g σ c : ℝ) (α sv : (H → ℝ) → H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1)
    (hsv : ∀ k, ContinuousOn (fun x => sv x k) (Simp H))
    (hspos : ∀ x ∈ Simp H, ∀ k, 0 < sv x k)
    (hα : ∀ k, ContinuousOn (fun x => α x k) (Simp H))
    (hα0 : ∀ x ∈ Simp H, ∀ k, 0 ≤ α x k)
    (hW : ∀ x ∈ Simp H, 0 < W (α x) (sv x) x) :
    ∃ x ∈ Simp H, Ψ g σ c α sv x = x ∧ ∀ h, g * σ * c / (1 + g) ≤ x h := by
  have hmaps : ∀ x ∈ Simp H, Ψ g σ c α sv x ∈ Simp H := fun x hx =>
    ⟨fun h => (div_nonneg (mul_nonneg (mul_nonneg hg.le hσ0) hc0) (by linarith)).trans
      (step_floor g σ c _ _ x hg hσ1 (hα0 x hx) (hspos x hx) hx (hW x hx) h),
     step_sum g σ c _ _ x hg hc (hspos x hx) hx (hW x hx)⟩
  have cv : Continuous (Subtype.val : Simp H → H → ℝ) := continuous_subtype_val
  have cs : ∀ k, Continuous fun p : Simp H => sv p.1 k := fun k =>
    (hsv k).comp_continuous cv fun p => p.2
  have ca : ∀ k, Continuous fun p : Simp H => α p.1 k := fun k =>
    (hα k).comp_continuous cv fun p => p.2
  have cx : ∀ k, Continuous fun p : Simp H => p.1 k := fun k => (continuous_apply k).comp cv
  have cB : Continuous fun p : Simp H => B (sv p.1) p.1 := by
    show Continuous fun p : Simp H => ∑ k, sv p.1 k * p.1 k
    exact continuous_finsetSum _ fun k _ => (cs k).mul (cx k)
  have cp : ∀ k, Continuous fun p : Simp H => post (sv p.1) p.1 k := fun k => by
    show Continuous fun p : Simp H => sv p.1 k * p.1 k / B (sv p.1) p.1
    exact ((cs k).mul (cx k)).div cB fun p => (B_pos _ _ (hspos p.1 p.2) p.2).ne'
  have cW : Continuous fun p : Simp H => W (α p.1) (sv p.1) p.1 := by
    show Continuous fun p : Simp H => ∑ k, α p.1 k * post (sv p.1) p.1 k
    exact continuous_finsetSum _ fun k _ => (ca k).mul (cp k)
  have cΨ : Continuous fun p : Simp H => Ψ g σ c α sv p.1 := by
    refine continuous_pi fun h => ?_
    show Continuous fun p : Simp H => (post (sv p.1) p.1 h + g * (σ * c + (1 - σ) *
      (α p.1 h * post (sv p.1) p.1 h / W (α p.1) (sv p.1) p.1))) / (1 + g)
    exact ((cp h).add (continuous_const.mul (continuous_const.add (continuous_const.mul
      (((ca h).mul (cp h)).div cW fun p => (hW p.1 p.2).ne'))))).div_const _
  let f : C(Simp H, Simp H) := ⟨fun p => ⟨Ψ g σ c α sv p.1, hmaps p.1 p.2⟩, cΨ.subtype_mk _⟩
  have hne : (Simp H).Nonempty := ⟨fun _ => c, fun _ => hc0, by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]⟩
  obtain ⟨p, hp⟩ := brouwer_fixed_point (Simp H) convex_Simp compact_Simp hne f
  have hfix : Ψ g σ c α sv p.1 = p.1 := congrArg Subtype.val hp
  refine ⟨p.1, p.2, hfix, fun h => ?_⟩
  rw [← hfix]
  exact step_floor g σ c _ _ p.1 hg hσ1 (hα0 p.1 p.2) (hspos p.1 p.2) p.2 (hW p.1 p.2) h

theorem W_full (s x : H → ℝ) (hs : ∀ k, 0 < s k) (hx : x ∈ Simp H) :
    W (fun _ => 1) s x = 1 := by
  unfold W
  simp only [one_mul]
  exact post_sum s x hs hx

/-- **Wealth-dependent patience, full access**: for any continuous positive `φ`, a long-run
distribution of the stage-363 step `x ↦ T (φ ∘ x) x` exists. -/
theorem exists_rest_patience (g σ c : ℝ) (φ : ℝ → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hφ : Continuous φ) (hφ0 : ∀ z, 0 < φ z) :
    ∃ x ∈ Simp H, Ψ g σ c (fun _ _ => 1) (fun x h => φ (x h)) x = x ∧
      ∀ h, g * σ * c / (1 + g) ≤ x h :=
  exists_rest g σ c _ _ hg hσ0 hσ1 hc0 hc
    (fun k => (hφ.comp (continuous_apply k)).continuousOn) (fun x _ k => hφ0 _)
    (fun k => continuousOn_const) (fun _ _ _ => zero_le_one)
    (fun x hx => by rw [W_full _ x (fun k => hφ0 _) hx]; exact one_pos)

/-- **Endogenous access**: access intensities that depend continuously on the distribution and
never fall below `α0 > 0`. -/
theorem exists_rest_access (g σ c α0 : ℝ) (α sv : (H → ℝ) → H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hα00 : 0 < α0)
    (hsv : ∀ k, ContinuousOn (fun x => sv x k) (Simp H))
    (hspos : ∀ x ∈ Simp H, ∀ k, 0 < sv x k)
    (hα : ∀ k, ContinuousOn (fun x => α x k) (Simp H))
    (hαl : ∀ x ∈ Simp H, ∀ k, α0 ≤ α x k) :
    ∃ x ∈ Simp H, Ψ g σ c α sv x = x ∧ ∀ h, g * σ * c / (1 + g) ≤ x h := by
  refine exists_rest g σ c α sv hg hσ0 hσ1 hc0 hc hsv hspos hα
    (fun x hx k => hα00.le.trans (hαl x hx k)) fun x hx => ?_
  have hsum := post_sum (sv x) x (hspos x hx) hx
  have : α0 ≤ W (α x) (sv x) x := by
    calc α0 = ∑ k, α0 * post (sv x) x k := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ W (α x) (sv x) x := Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hαl x hx k) (post_nonneg _ x (hspos x hx) hx k)
  linarith

/-! ## Forward-looking saving in a stationary state -/

def ex (γ : ℝ) : ℝ := (1 - γ) / γ

/-- **The stationary infinite-horizon rule.** At a constant return the stage-364 series is
`F = q / (1 − q)` with `q = b Q ^ ((1 − γ) / γ) < 1`; it satisfies the recursion
`F = q (1 + F)` and gives the saving rate `F / (1 + F) = q`. -/
theorem stationary_rule (q : ℝ) (hq : q < 1) :
    q / (1 - q) = q * (1 + q / (1 - q)) ∧ q / (1 - q) / (1 + q / (1 - q)) = q := by
  have h : 1 - q ≠ 0 := by linarith
  constructor
  · field_simp
    ring
  · rw [show 1 + q / (1 - q) = 1 / (1 - q) by field_simp; ring]
    field_simp

def D (β : (H → ℝ) → H → ℝ) (x : H → ℝ) : ℝ := ∑ k, β x k * x k

/-- The stationary saving rate `β x h · Q ^ ((1 − γ) / γ)` written in terms of `D`. -/
def sF (γ : ℝ) (β : (H → ℝ) → H → ℝ) (x : H → ℝ) (h : H) : ℝ := β x h * D β x ^ (γ - 1)

/-- The stationary return. -/
def QF (γ : ℝ) (β : (H → ℝ) → H → ℝ) (x : H → ℝ) : ℝ := D β x ^ (-γ)

/-- **A stationary equilibrium with forward-looking saving and distribution-dependent
patience.** -/
theorem exists_stationary_forward (g σ c γ : ℝ) (β : (H → ℝ) → H → ℝ) (hg : 0 < g)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hγ : 0 < γ)
    (hβ : ∀ k, ContinuousOn (fun x => β x k) (Simp H)) (hβ0 : ∀ x ∈ Simp H, ∀ k, 0 < β x k) :
    ∃ x ∈ Simp H, Ψ g σ c (fun _ _ => 1) (sF γ β) x = x ∧
      (∀ h, sF γ β x h = β x h * QF γ β x ^ ex γ) ∧
      QF γ β x = 1 / B (sF γ β x) x ∧ ∀ h, g * σ * c / (1 + g) ≤ x h := by
  have hD : ∀ x ∈ Simp H, 0 < D β x := fun x hx => B_pos (β x) x (hβ0 x hx) hx
  have hspos : ∀ x ∈ Simp H, ∀ k, 0 < sF γ β x k := fun x hx k =>
    mul_pos (hβ0 x hx k) (Real.rpow_pos_of_pos (hD x hx) _)
  have cD : ContinuousOn (D β) (Simp H) := by
    show ContinuousOn (fun x => ∑ k, β x k * x k) (Simp H)
    exact continuousOn_finsetSum _ fun k _ => (hβ k).mul (continuous_apply k).continuousOn
  have hsv : ∀ k, ContinuousOn (fun x => sF γ β x k) (Simp H) := fun k =>
    (hβ k).mul (cD.rpow_const fun x hx => Or.inl (hD x hx).ne')
  obtain ⟨x, hx, hfix, hfl⟩ := exists_rest g σ c (fun _ _ => 1) (sF γ β) hg hσ0 hσ1 hc0 hc hsv
    hspos (fun k => continuousOn_const) (fun _ _ _ => zero_le_one)
    (fun x hx => by rw [W_full _ x (hspos x hx) hx]; exact one_pos)
  have hDx := hD x hx
  refine ⟨x, hx, hfix, fun h => ?_, ?_, hfl⟩
  · unfold sF QF
    rw [← Real.rpow_mul hDx.le]
    congr 2
    unfold ex
    field_simp
    ring
  · have hB : B (sF γ β x) x = D β x ^ γ := by
      unfold B sF
      have e : ∑ k, β x k * D β x ^ (γ - 1) * x k = D β x ^ (γ - 1) * D β x := by
        unfold D
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e, Real.rpow_sub_one hDx.ne', div_mul_cancel₀ _ hDx.ne']
    unfold QF
    rw [hB, Real.rpow_neg hDx.le, one_div]

/-! ## No uniqueness, even with continuous patience -/

/-- Patience rising continuously with wealth: `2/5` up to `1/5`, linear in between, `1/2` from
`4/5` on. -/
def φc (z : ℝ) : ℝ := max (2 / 5) (min (1 / 2) (2 / 5 + (z - 1 / 5) / 6))

theorem φc_cont : Continuous φc := by
  unfold φc
  fun_prop

theorem φc_mono : Monotone φc := fun a b hab => by
  unfold φc
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

set_option linter.unusedSimpArgs false in
/-- **Two long-run distributions** under continuous, increasing patience: with `g = 1`,
`σ = 1/5`, `c = 1/2` and full access, both the equal distribution and `(1/5, 4/5)` reproduce
themselves. -/
theorem two_rest_continuous (h : Fin 2) :
    Ψ 1 (1 / 5) (1 / 2) (fun _ _ => 1) (fun x k => φc (x k)) (fun _ => 1 / 2) h = 1 / 2 ∧
    Ψ 1 (1 / 5) (1 / 2) (fun _ _ => 1) (fun x k => φc (x k)) ![1 / 5, 4 / 5] h =
      ![1 / 5, 4 / 5] h := by
  have e1 : φc (1 / 5) = 2 / 5 := by norm_num [φc]
  have e2 : φc (4 / 5) = 1 / 2 := by norm_num [φc]
  have e3 : φc (1 / 2) = 9 / 20 := by norm_num [φc]
  have e1' : φc 5⁻¹ = 2 / 5 := by norm_num [φc]
  have e3' : φc 2⁻¹ = 9 / 20 := by norm_num [φc]
  fin_cases h <;>
    simp [Ψ, stepA, W, post, B, Fin.sum_univ_two, e1, e2, e3, e1', e3'] <;> norm_num

end EndogenousRest

end

#print axioms EndogenousRest.convex_Simp
#print axioms EndogenousRest.compact_Simp
#print axioms EndogenousRest.step_sum
#print axioms EndogenousRest.step_floor
#print axioms EndogenousRest.exists_rest
#print axioms EndogenousRest.exists_rest_patience
#print axioms EndogenousRest.exists_rest_access
#print axioms EndogenousRest.stationary_rule
#print axioms EndogenousRest.exists_stationary_forward
#print axioms EndogenousRest.φc_cont
#print axioms EndogenousRest.φc_mono
#print axioms EndogenousRest.two_rest_continuous
