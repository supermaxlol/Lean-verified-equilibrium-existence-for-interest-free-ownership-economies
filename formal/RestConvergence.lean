import Mathlib

/-!
# Stage 367: uniqueness of the rest point and convergence to it, when the update is a contraction

Stage 365 proved that the ownership dynamics have a rest point for every continuous
wealth-dependent patience or access rule, and gave a continuous rule with two rest points, so
existence alone says nothing about uniqueness or convergence. This file isolates a condition
under which both hold, and checks it in the basic economic case.

* `contraction_rest`: if a self-map `f` of a closed nonempty subset `s` of a complete metric space
  satisfies `dist (f x) (f y) ≤ K · dist x y` on `s` with `0 ≤ K < 1`, then it has exactly one
  rest point `x⋆` in `s`, and from every starting point in `s` the path `f^[n] x` converges to
  `x⋆` with `dist (f^[n] x) x⋆ ≤ K ^ n · dist x x⋆` (Banach fixed point theorem, used through
  Mathlib's `ContractingWith`; the rate is proved directly).
* `affine_rest`: the affine update `x' h = ρ h · x h + a h` with retention `0 ≤ ρ h ≤ K < 1`
  (sup distance on `H → ℝ`) is such a contraction on all of `H → ℝ`; its unique rest point is
  `a h / (1 − ρ h)` and every path converges to it at rate `K ^ n`.
* `step_common`: with common saving rate `s₀ > 0` and full access, the stage 356/365 issuance step
  restricted to the simplex is exactly the affine update with common retention
  `ρ = (1 + g (1 − σ)) / (1 + g)` and intercept `g σ c / (1 + g)`.
* **`common_patience_converges`**: in that case, for `g > 0`, `0 < σ ≤ 1` and `H · c = 1`, the
  equal distribution `x h = c` is the only rest point on the simplex, and from every initial
  distribution the ownership path converges to it, with
  `dist (x_n) c ≤ ((1 + g (1 − σ)) / (1 + g)) ^ n · dist (x_0) c`.

Reading: when everyone saves at the same rate and has the same access, issuance of new claims
pulls every distribution geometrically to equal ownership, at a speed set by the issuance rate
`g` and the issued share `σ`.

Limits: the economic sufficient condition is only the common-saving, full-access case (and the
affine update with fixed household retention rates). For wealth-dependent saving or access the
contraction hypothesis is not verified here, and by stage 365 it can fail (two rest points).
Discontinuous threshold rules are not covered.
-/

noncomputable section

open Filter Topology Set Finset

namespace RestConvergence

/-- The geometric rate along iterates, for a map that contracts on an invariant set. -/
theorem iterate_rate {α : Type*} [MetricSpace α] (f : α → α) (s : Set α) (hmap : MapsTo f s s)
    (K : ℝ) (hK0 : 0 ≤ K) (hc : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y)
    (xs : α) (hxs : xs ∈ s) (hfix : f xs = xs) (x : α) (hx : x ∈ s) (n : ℕ) :
    dist (f^[n] x) xs ≤ K ^ n * dist x xs := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc dist (f (f^[n] x)) xs = dist (f (f^[n] x)) (f xs) := by rw [hfix]
      _ ≤ K * dist (f^[n] x) xs := hc _ (hmap.iterate n hx) _ hxs
      _ ≤ K * (K ^ n * dist x xs) := mul_le_mul_of_nonneg_left ih hK0
      _ = K ^ (n + 1) * dist x xs := by ring

/-- **Contraction mapping**: unique rest point, global convergence, geometric rate. -/
theorem contraction_rest {α : Type*} [MetricSpace α] [CompleteSpace α] (f : α → α) (s : Set α)
    (hs : IsClosed s) (hne : s.Nonempty) (hmap : MapsTo f s s) (K : ℝ) (hK0 : 0 ≤ K)
    (hK1 : K < 1) (hc : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    ∃ xs ∈ s, f xs = xs ∧ (∀ y ∈ s, f y = y → y = xs) ∧
      ∀ x ∈ s, (∀ n : ℕ, dist (f^[n] x) xs ≤ K ^ n * dist x xs) ∧
        Tendsto (fun n => f^[n] x) atTop (𝓝 xs) := by
  obtain ⟨x0, hx0⟩ := hne
  have hcon : ContractingWith ⟨K, hK0⟩ (hmap.restrict f s s) := by
    refine ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact hK1), ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
    exact hc _ a.2 _ b.2
  obtain ⟨xs, hxs, hfix, -, -⟩ :=
    hcon.exists_fixedPoint' hs.isComplete hmap hx0 (edist_ne_top _ _)
  have hfix' : f xs = xs := hfix
  refine ⟨xs, hxs, hfix', fun y hy hfy => ?_, fun x hx => ?_⟩
  · have h := hc y hy xs hxs
    rw [hfy, hfix'] at h
    have hd : dist y xs ≤ 0 := by nlinarith [dist_nonneg (x := y) (y := xs)]
    exact dist_le_zero.1 hd
  · have hr := iterate_rate f s hmap K hK0 hc xs hxs hfix' x hx
    refine ⟨hr, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have hK : Tendsto (fun n : ℕ => K ^ n * dist x xs) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const (dist x xs)
    exact squeeze_zero (fun n => dist_nonneg) hr hK

variable {H : Type*} [Fintype H]

/-- The affine update with household retention `ρ` and intercept `a`. -/
def affR (ρ a : H → ℝ) (x : H → ℝ) : H → ℝ := fun h => ρ h * x h + a h

theorem affR_dist (ρ a : H → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hρ0 : ∀ h, 0 ≤ ρ h) (hρK : ∀ h, ρ h ≤ K)
    (x y : H → ℝ) : dist (affR ρ a x) (affR ρ a y) ≤ K * dist x y := by
  refine (dist_pi_le_iff (mul_nonneg hK0 dist_nonneg)).2 fun h => ?_
  rw [affR, affR, Real.dist_eq]
  have e : ρ h * x h + a h - (ρ h * y h + a h) = ρ h * (x h - y h) := by ring
  rw [e, abs_mul, abs_of_nonneg (hρ0 h), ← Real.dist_eq]
  exact mul_le_mul (hρK h) (dist_le_pi_dist x y h) dist_nonneg hK0

/-- **Affine update with retention below one**: unique rest point `a h / (1 − ρ h)`, and every
path converges to it at rate `K ^ n`. -/
theorem affine_rest (ρ a : H → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hρ0 : ∀ h, 0 ≤ ρ h)
    (hρK : ∀ h, ρ h ≤ K) :
    affR ρ a (fun h => a h / (1 - ρ h)) = (fun h => a h / (1 - ρ h)) ∧
      (∀ y, affR ρ a y = y → y = fun h => a h / (1 - ρ h)) ∧
      ∀ x (n : ℕ), dist ((affR ρ a)^[n] x) (fun h => a h / (1 - ρ h)) ≤
        K ^ n * dist x (fun h => a h / (1 - ρ h)) := by
  have hfix : affR ρ a (fun h => a h / (1 - ρ h)) = (fun h => a h / (1 - ρ h)) := by
    funext h
    have : 1 - ρ h ≠ 0 := by linarith [hρK h]
    simp only [affR]
    field_simp
    ring
  obtain ⟨xs, -, hxs, huniq, -⟩ := contraction_rest (affR ρ a) univ isClosed_univ univ_nonempty
    (mapsTo_univ _ _) K hK0 hK1 (fun x _ y _ => affR_dist ρ a K hK0 hρ0 hρK x y)
  have he : (fun h => a h / (1 - ρ h)) = xs := huniq _ (mem_univ _) hfix
  refine ⟨hfix, fun y hy => (huniq y (mem_univ _) hy).trans he.symm, fun x n => ?_⟩
  exact iterate_rate (affR ρ a) univ (mapsTo_univ _ _) K hK0
    (fun x _ y _ => affR_dist ρ a K hK0 hρ0 hρK x y) _ (mem_univ _) hfix x (mem_univ _) n

/-! ## The issuance step with common saving and full access -/

/-- The simplex of ownership distributions (as in stage 365). -/
def Simp (H : Type*) [Fintype H] : Set (H → ℝ) := {x | (∀ h, 0 ≤ x h) ∧ ∑ h, x h = 1}

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def post (s x : H → ℝ) (h : H) : ℝ := s h * x h / B s x

def W (a s x : H → ℝ) : ℝ := ∑ k, a k * post s x k

/-- The issuance step with access intensities `a` (stage 365). -/
def stepA (g σ c : ℝ) (a s x : H → ℝ) (h : H) : ℝ :=
  (post s x h + g * (σ * c + (1 - σ) * (a h * post s x h / W a s x))) / (1 + g)

theorem isClosed_Simp : IsClosed (Simp H) := by
  have e : Simp H = (⋂ h, {x : H → ℝ | 0 ≤ x h}) ∩ {x | ∑ h, x h = 1} := by
    ext x
    simp [Simp]
  rw [e]
  exact (isClosed_iInter fun h => isClosed_le continuous_const (continuous_apply h)).inter
    (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)

/-- **With common saving rate and full access the step is affine** on the simplex. -/
theorem step_common (g σ c s0 : ℝ) (hs0 : 0 < s0) (x : H → ℝ) (hx : x ∈ Simp H) :
    stepA g σ c (fun _ => 1) (fun _ => s0) x =
      affR (fun _ => (1 + g * (1 - σ)) / (1 + g)) (fun _ => g * σ * c / (1 + g)) x := by
  have hB : B (fun _ => s0) x = s0 := by
    rw [B, ← Finset.mul_sum, hx.2, mul_one]
  have hp : ∀ h, post (fun _ => s0) x h = x h := fun h => by
    rw [post, hB]
    field_simp
  have hW : W (fun _ => 1) (fun _ => s0) x = 1 := by
    rw [W]
    simp only [hp, one_mul]
    exact hx.2
  funext h
  simp only [stepA, affR, hp, hW, one_mul, div_one]
  ring

theorem affR_maps (g σ c : ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) :
    MapsTo (affR (fun _ : H => (1 + g * (1 - σ)) / (1 + g)) (fun _ => g * σ * c / (1 + g)))
      (Simp H) (Simp H) := by
  intro x hx
  refine ⟨fun h => ?_, ?_⟩
  · have : 0 ≤ 1 + g * (1 - σ) := by nlinarith
    exact add_nonneg (mul_nonneg (div_nonneg this (by linarith)) (hx.1 h))
      (div_nonneg (mul_nonneg (mul_nonneg hg.le hσ0) hc0) (by linarith))
  · simp only [affR]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have h1 : (1 + g) ≠ 0 := by linarith
    field_simp
    linear_combination (g * σ) * hc

/-- **Common patience: global convergence to equal ownership.** With common saving rate, full
access, `g > 0`, `0 < σ ≤ 1` and `H · c = 1`, the issuance dynamics on the simplex have the
equal distribution as their only rest point, and every path converges to it geometrically. -/
theorem common_patience_converges [Nonempty H] (g σ c s0 : ℝ) (hg : 0 < g) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hs0 : 0 < s0) (hc : (Fintype.card H : ℝ) * c = 1) :
    let F := fun x : H → ℝ => stepA g σ c (fun _ => 1) (fun _ => s0) x
    let ρ := (1 + g * (1 - σ)) / (1 + g)
    ρ < 1 ∧ (fun _ => c) ∈ Simp H ∧ F (fun _ => c) = (fun _ => c) ∧
      (∀ y ∈ Simp H, F y = y → y = fun _ => c) ∧
      ∀ x ∈ Simp H, (∀ n : ℕ, dist (F^[n] x) (fun _ => c) ≤ ρ ^ n * dist x (fun _ => c)) ∧
        Tendsto (fun n => F^[n] x) atTop (𝓝 (fun _ => c)) := by
  intro F ρ
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hc0 : 0 < c := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hρ1 : ρ < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by nlinarith) (by linarith)
  set A := affR (fun _ : H => ρ) (fun _ => g * σ * c / (1 + g)) with hA
  have hmapA := affR_maps (H := H) g σ c hg hσ0.le hσ1 hc0.le hc
  have hFA : ∀ x ∈ Simp H, F x = A x := fun x hx => step_common g σ c s0 hs0 x hx
  have hmapF : MapsTo F (Simp H) (Simp H) := fun x hx => by rw [hFA x hx]; exact hmapA hx
  have hcF : ∀ x ∈ Simp H, ∀ y ∈ Simp H, dist (F x) (F y) ≤ ρ * dist x y := by
    intro x hx y hy
    rw [hFA x hx, hFA y hy]
    exact affR_dist _ _ ρ hρ0 (fun _ => hρ0) (fun _ => le_rfl) x y
  have hcS : (fun _ => c) ∈ Simp H := by
    refine ⟨fun _ => hc0.le, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have hfixc : F (fun _ => c) = fun _ => c := by
    rw [hFA _ hcS, hA]
    funext h
    simp only [affR, ρ]
    have h1 : (1 + g) ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨xs, hxs, -, huniq, hconv⟩ := contraction_rest F (Simp H) isClosed_Simp ⟨_, hcS⟩
    hmapF ρ hρ0 hρ1 hcF
  have he : (fun _ : H => c) = xs := huniq _ hcS hfixc
  subst he
  exact ⟨hρ1, hcS, hfixc, huniq, hconv⟩

end RestConvergence

end

#print axioms RestConvergence.iterate_rate
#print axioms RestConvergence.contraction_rest
#print axioms RestConvergence.affR_dist
#print axioms RestConvergence.affine_rest
#print axioms RestConvergence.isClosed_Simp
#print axioms RestConvergence.step_common
#print axioms RestConvergence.affR_maps
#print axioms RestConvergence.common_patience_converges
