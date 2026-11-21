import Mathlib

/-!
# Stage 376: wealth-dependent saving that still gives a unique, globally stable rest point

Stage 365 proved that the ownership dynamics have a rest point for any continuous rule that makes
saving depend on wealth, and gave such a rule with two rest points. Stage 367 proved uniqueness
and geometric convergence when everyone saves at the same rate. This file covers the case in
between: saving that depends on the household's own wealth share, with an explicit condition
on how strongly it may depend on it.

Setting (full access, as in stage 365 with `α = 1`): household `h` with share `x h` saves at
rate `φ (x h)`; its post-saving share is `p h = φ (x h) x h / Σ φ (x k) x k`, and issuance gives
`x' h = ((1 + g (1 − σ)) p h + g σ c) / (1 + g)` (`T`; `step_eq` checks that this is the
stage 365 step). Assume on `[0, 1]`: `A ≤ φ ≤ A + δ` with `A > 0`, and `φ` is `L`-Lipschitz.
Distances are measured by `d1 x y = Σ |x h − y h|`.

* `post_lip`: the saving-reweighting map `x ↦ p` is Lipschitz on the simplex with constant
  `1 + 2 (δ + L) / A` (for constant saving, `δ = L = 0`, the constant is `1`).
* `T_lip`: the whole update is Lipschitz with constant
  `K = (1 + g (1 − σ)) / (1 + g) · (1 + 2 (δ + L) / A)`.
* **`wealth_saving_contraction`**: if `K < 1`, there is exactly one rest point on the simplex,
  and from every initial distribution the ownership path converges to it, with
  `d1 (x_n) x⋆ ≤ K ^ n · d1 (x_0) x⋆`. (Existence comes from the Banach fixed point theorem in
  Mathlib's `ℓ¹` space `PiLp 1`; uniqueness, the rate and the convergence are proved directly.)
* `example_converges`: the condition is not empty: saving `φ z = 1/2 + z/20`, rising with
  wealth, with `g = 1` and `σ = 3/5` gives `K = 49/50 < 1`.
* `no_contraction_of_two_rest`, `stage365_rule_fails`: if the update has two different rest
  points, no choice of `A, δ, L` meets the condition; in particular the stage 365 rule with two
  rest points fails it for every choice of constants, as it must.

Reading: saving may rise with wealth and the long-run distribution is still unique and reached
from every starting point, provided the dispersion of saving rates `δ` and their sensitivity to
wealth `L` are small relative to the lowest saving rate `A` and the issued share `σ` is large
enough. The condition `K < 1` is sufficient, not necessary.

Limits: full access only (no access rule); saving depends on the household's own share only;
the condition is sufficient and is likely conservative (the constant `2` in `post_lip` comes from
a crude bound); between the condition and the stage 365 two-rest-point example, uniqueness is
not settled; threshold rules are not covered.
-/

noncomputable section

open Filter Topology Set Finset

namespace WealthSavingContraction

variable {H : Type*} [Fintype H]

/-- The simplex of ownership distributions (as in stage 365). -/
def Simp (H : Type*) [Fintype H] : Set (H → ℝ) := {x | (∀ h, 0 ≤ x h) ∧ ∑ h, x h = 1}

/-- The `ℓ¹` distance. -/
def d1 (x y : H → ℝ) : ℝ := ∑ h, |x h - y h|

/-- Aggregate saving with wealth-dependent rate `φ`. -/
def Bφ (φ : ℝ → ℝ) (x : H → ℝ) : ℝ := ∑ k, φ (x k) * x k

/-- Post-saving shares. -/
def pφ (φ : ℝ → ℝ) (x : H → ℝ) (h : H) : ℝ := φ (x h) * x h / Bφ φ x

/-- The update with wealth-dependent saving and full access. -/
def T (g σ c : ℝ) (φ : ℝ → ℝ) (x : H → ℝ) (h : H) : ℝ :=
  ((1 + g * (1 - σ)) * pφ φ x h + g * σ * c) / (1 + g)

/-- The contraction modulus. -/
def Kmod (g σ A δ L : ℝ) : ℝ := (1 + g * (1 - σ)) / (1 + g) * (1 + 2 * (δ + L) / A)

/-! ## The stage 365 step (copied definitions) -/

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def post (s x : H → ℝ) (h : H) : ℝ := s h * x h / B s x

def W (a s x : H → ℝ) : ℝ := ∑ k, a k * post s x k

def stepA (g σ c : ℝ) (a s x : H → ℝ) (h : H) : ℝ :=
  (post s x h + g * (σ * c + (1 - σ) * (a h * post s x h / W a s x))) / (1 + g)

theorem mem_Icc_of_Simp (x : H → ℝ) (hx : x ∈ Simp H) (h : H) : x h ∈ Icc (0 : ℝ) 1 :=
  ⟨hx.1 h, hx.2 ▸ Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ h)⟩

theorem B_ge (φ : ℝ → ℝ) (A : ℝ) (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) (x : H → ℝ)
    (hx : x ∈ Simp H) : A ≤ Bφ φ x := by
  calc A = ∑ k, A * x k := by rw [← Finset.mul_sum, hx.2, mul_one]
    _ ≤ Bφ φ x := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (hφl _ (mem_Icc_of_Simp x hx k)) (hx.1 k)

theorem sum_p (φ : ℝ → ℝ) (x : H → ℝ) (hB : Bφ φ x ≠ 0) : ∑ h, pφ φ x h = 1 := by
  unfold pφ
  rw [← Finset.sum_div]
  exact div_self hB

theorem p_nonneg (φ : ℝ → ℝ) (A : ℝ) (hA : 0 < A) (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z)
    (x : H → ℝ) (hx : x ∈ Simp H) (h : H) : 0 ≤ pφ φ x h := by
  have hB := (hA.trans_le (B_ge φ A hφl x hx))
  have := hφl _ (mem_Icc_of_Simp x hx h)
  exact div_nonneg (mul_nonneg (by linarith) (hx.1 h)) hB.le

/-- With full access, `T` is the stage 365 step. -/
theorem step_eq (g σ c A : ℝ) (φ : ℝ → ℝ) (hA : 0 < A) (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z)
    (x : H → ℝ) (hx : x ∈ Simp H) :
    stepA g σ c (fun _ => 1) (fun k => φ (x k)) x = T g σ c φ x := by
  have hB := (hA.trans_le (B_ge φ A hφl x hx))
  have hp : ∀ h, post (fun k => φ (x k)) x h = pφ φ x h := fun h => rfl
  have hW : W (fun _ => 1) (fun k => φ (x k)) x = 1 := by
    unfold W
    simp only [hp, one_mul]
    exact sum_p φ x hB.ne'
  funext h
  simp only [stepA, T, hp, hW, one_mul, div_one]
  ring

/-! ## The Lipschitz bounds -/

theorem chi_lip (φ : ℝ → ℝ) (A δ L : ℝ) (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z)
    (hφu : ∀ z ∈ Icc (0 : ℝ) 1, φ z ≤ A + δ)
    (hφL : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φ a - φ b| ≤ L * |a - b|)
    (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |(φ a - A) * a - (φ b - A) * b| ≤ (δ + L) * |a - b| := by
  have e : (φ a - A) * a - (φ b - A) * b = (φ a - A) * (a - b) + b * (φ a - φ b) := by ring
  rw [e]
  have h1 : |(φ a - A) * (a - b)| ≤ δ * |a - b| := by
    rw [abs_mul, abs_of_nonneg (by linarith [hφl a ha])]
    exact mul_le_mul_of_nonneg_right (by linarith [hφu a ha]) (abs_nonneg _)
  have h2 : |b * (φ a - φ b)| ≤ L * |a - b| := by
    rw [abs_mul, abs_of_nonneg hb.1]
    calc b * |φ a - φ b| ≤ 1 * |φ a - φ b| :=
          mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)
      _ ≤ L * |a - b| := by rw [one_mul]; exact hφL a ha b hb
  calc _ ≤ |(φ a - A) * (a - b)| + |b * (φ a - φ b)| := abs_add_le _ _
    _ ≤ δ * |a - b| + L * |a - b| := add_le_add h1 h2
    _ = (δ + L) * |a - b| := by ring

theorem abs_split (a p S Bx : ℝ) (hB : 0 < Bx) (hp : 0 ≤ p) :
    |a / Bx - p * S / Bx| ≤ |a| / Bx + p * |S| / Bx := by
  rw [← sub_div, abs_div, abs_of_pos hB, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hB.le
  calc |a - p * S| ≤ |a| + |p * S| := abs_sub _ _
    _ = |a| + p * |S| := by rw [abs_mul, abs_of_nonneg hp]

/-- **The saving-reweighting map is Lipschitz** on the simplex. -/
theorem post_lip (φ : ℝ → ℝ) (A δ L : ℝ) (hA : 0 < A) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) (hφu : ∀ z ∈ Icc (0 : ℝ) 1, φ z ≤ A + δ)
    (hφL : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φ a - φ b| ≤ L * |a - b|)
    (x y : H → ℝ) (hx : x ∈ Simp H) (hy : y ∈ Simp H) :
    d1 (pφ φ x) (pφ φ y) ≤ (1 + 2 * (δ + L) / A) * d1 x y := by
  set m := δ + L with hm
  have hm0 : 0 ≤ m := by linarith
  set D := d1 x y with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun h _ => abs_nonneg _
  have hBx : A ≤ Bφ φ x := B_ge φ A hφl x hx
  have hBx0 : 0 < Bφ φ x := hA.trans_le hBx
  have hBy0 : 0 < Bφ φ y := hA.trans_le (B_ge φ A hφl y hy)
  set w : H → ℝ := fun k => (φ (x k) - A) * x k - (φ (y k) - A) * y k with hw
  have hwb : ∀ k, |w k| ≤ m * |x k - y k| := fun k =>
    chi_lip φ A δ L hφl hφu hφL _ _ (mem_Icc_of_Simp x hx k) (mem_Icc_of_Simp y hy k)
  have hdiff : Bφ φ x - Bφ φ y = ∑ k, w k := by
    have e : ∀ k, w k = (φ (x k) * x k - φ (y k) * y k) - A * (x k - y k) := fun k => by
      simp only [hw]
      ring
    have hxy : ∑ k, (x k - y k) = 0 := by rw [Finset.sum_sub_distrib, hx.2, hy.2, sub_self]
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_sub_distrib, ← Finset.mul_sum, hxy,
      Bφ, Bφ, Finset.sum_sub_distrib]
    ring
  have hSw : |∑ k, w k| ≤ m * D := by
    calc |∑ k, w k| ≤ ∑ k, |w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, m * |x k - y k| := Finset.sum_le_sum fun k _ => hwb k
      _ = m * D := by rw [hD]; unfold d1; rw [Finset.mul_sum]
  have hpt : ∀ h, pφ φ x h - pφ φ y h =
      (A * (x h - y h) + w h) / Bφ φ x - pφ φ y h * (∑ k, w k) / Bφ φ x := by
    intro h
    rw [← hdiff]
    unfold pφ
    simp only [hw]
    field_simp
    ring
  have hbound : ∀ h, |pφ φ x h - pφ φ y h| ≤
      (A + m) * |x h - y h| / Bφ φ x + pφ φ y h * (m * D) / Bφ φ x := by
    intro h
    rw [hpt]
    have hp0 := p_nonneg φ A hA hφl y hy h
    refine (abs_split _ _ _ _ hBx0 hp0).trans (add_le_add ?_ ?_)
    · refine div_le_div_of_nonneg_right ?_ hBx0.le
      calc |A * (x h - y h) + w h| ≤ |A * (x h - y h)| + |w h| := abs_add_le _ _
        _ ≤ A * |x h - y h| + m * |x h - y h| := by
            rw [abs_mul, abs_of_pos hA]
            linarith [hwb h]
        _ = (A + m) * |x h - y h| := by ring
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSw hp0) hBx0.le
  have hs1 := sum_p φ y hBy0.ne'
  calc d1 (pφ φ x) (pφ φ y)
      ≤ ∑ h, ((A + m) * |x h - y h| / Bφ φ x + pφ φ y h * (m * D) / Bφ φ x) :=
        Finset.sum_le_sum fun h _ => hbound h
    _ = (A + m) * D / Bφ φ x + m * D / Bφ φ x := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
          ← Finset.sum_mul, hs1, one_mul]
        rfl
    _ = (A + 2 * m) * D / Bφ φ x := by ring
    _ ≤ (A + 2 * m) * D / A :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) hD0) hA hBx
    _ = (1 + 2 * m / A) * D := by field_simp

/-- **The update is Lipschitz** with constant `Kmod`. -/
theorem T_lip (g σ c A δ L : ℝ) (φ : ℝ → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) (hA : 0 < A)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) (hφu : ∀ z ∈ Icc (0 : ℝ) 1, φ z ≤ A + δ)
    (hφL : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φ a - φ b| ≤ L * |a - b|)
    (x y : H → ℝ) (hx : x ∈ Simp H) (hy : y ∈ Simp H) :
    d1 (T g σ c φ x) (T g σ c φ y) ≤ Kmod g σ A δ L * d1 x y := by
  have hρ : 0 ≤ (1 + g * (1 - σ)) / (1 + g) :=
    div_nonneg (by nlinarith) (by linarith)
  have e : ∀ h, |T g σ c φ x h - T g σ c φ y h| =
      (1 + g * (1 - σ)) / (1 + g) * |pφ φ x h - pφ φ y h| := fun h => by
    rw [← abs_of_nonneg hρ, ← abs_mul]
    congr 1
    unfold T
    field_simp
    ring
  unfold d1
  simp only [e]
  rw [← Finset.mul_sum, Kmod, mul_assoc]
  exact mul_le_mul_of_nonneg_left (post_lip φ A δ L hA hδ hL hφl hφu hφL x y hx hy) hρ

/-- The update maps the simplex into itself. -/
theorem T_maps (g σ c A : ℝ) (φ : ℝ → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hA : 0 < A)
    (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) (x : H → ℝ) (hx : x ∈ Simp H) :
    T g σ c φ x ∈ Simp H := by
  have hB := hA.trans_le (B_ge φ A hφl x hx)
  refine ⟨fun h => ?_, ?_⟩
  · unfold T
    have := p_nonneg φ A hA hφl x hx h
    have h1 : 0 ≤ 1 + g * (1 - σ) := by nlinarith
    positivity
  · unfold T
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_p φ x hB.ne',
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_one_iff_eq (by linarith)]
    linear_combination (g * σ) * hc

/-! ## Unique rest point and geometric convergence -/

theorem d1_nonneg (x y : H → ℝ) : 0 ≤ d1 x y := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem eq_of_d1 (x y : H → ℝ) (h : d1 x y ≤ 0) : x = y := by
  have h0 : d1 x y = 0 := le_antisymm h (d1_nonneg x y)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg (x k - y k)).1 h0
  funext k
  exact sub_eq_zero.1 (abs_eq_zero.1 (this k (Finset.mem_univ k)))

theorem coord_le_d1 (x y : H → ℝ) (h : H) : |x h - y h| ≤ d1 x y :=
  Finset.single_le_sum (f := fun k => |x k - y k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ h)

/-- **Unique rest point and global geometric convergence** under wealth-dependent saving. -/
theorem wealth_saving_contraction (g σ c A δ L : ℝ) (φ : ℝ → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hA : 0 < A)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hφl : ∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) (hφu : ∀ z ∈ Icc (0 : ℝ) 1, φ z ≤ A + δ)
    (hφL : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φ a - φ b| ≤ L * |a - b|)
    (hK : Kmod g σ A δ L < 1) :
    ∃ xs ∈ Simp H, T g σ c φ xs = xs ∧ (∀ y ∈ Simp H, T g σ c φ y = y → y = xs) ∧
      ∀ x ∈ Simp H, (∀ n : ℕ, d1 ((T g σ c φ)^[n] x) xs ≤ Kmod g σ A δ L ^ n * d1 x xs) ∧
        Tendsto (fun n => (T g σ c φ)^[n] x) atTop (𝓝 xs) := by
  set K := Kmod g σ A δ L with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (div_nonneg (by nlinarith) (by linarith))
    (by have : 0 ≤ 2 * (δ + L) / A := div_nonneg (by linarith) hA.le
        linarith)
  have hmap := T_maps (H := H) g σ c A φ hg hσ0 hσ1 hc0 hc hA hφl
  have hlip := T_lip (H := H) g σ c A δ L φ hg hσ1 hA hδ hL hφl hφu hφL
  -- existence: Banach fixed point theorem in `ℓ¹`
  have hdist : ∀ x y : PiLp 1 (fun _ : H => ℝ),
      dist x y = d1 (WithLp.ofLp x) (WithLp.ofLp y) := fun x y => by
    rw [PiLp.dist_eq_of_L1]
    simp only [d1, Real.dist_eq]
  set F : PiLp 1 (fun _ : H => ℝ) → PiLp 1 (fun _ : H => ℝ) :=
    fun x => WithLp.toLp 1 (T g σ c φ (WithLp.ofLp x)) with hF
  set s : Set (PiLp 1 (fun _ : H => ℝ)) := {x | WithLp.ofLp x ∈ Simp H} with hs
  have hsc : IsClosed s := by
    have hcl : IsClosed (Simp H) := by
      have e : Simp H = (⋂ h, {x : H → ℝ | 0 ≤ x h}) ∩ {x | ∑ h, x h = 1} := by
        ext x
        simp [Simp]
      rw [e]
      exact (isClosed_iInter fun h => isClosed_le continuous_const (continuous_apply h)).inter
        (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)
    exact hcl.preimage (PiLp.continuous_ofLp _ _)
  have hcS : (fun _ : H => c) ∈ Simp H := ⟨fun _ => hc0, by simp [hc]⟩
  obtain ⟨x0, hx0⟩ : s.Nonempty := ⟨WithLp.toLp 1 (fun _ => c), hcS⟩
  have hFmap : MapsTo F s s := fun x hx => hmap _ hx
  have hFc : ∀ x ∈ s, ∀ y ∈ s, dist (F x) (F y) ≤ K * dist x y := fun x hx y hy => by
    rw [hdist, hdist]
    exact hlip _ _ hx hy
  have hcon : ContractingWith ⟨K, hK0⟩ (hFmap.restrict F s s) := by
    refine ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact hK), ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
    exact hFc _ a.2 _ b.2
  obtain ⟨z, hz, hfix, -, -⟩ :=
    hcon.exists_fixedPoint' hsc.isComplete hFmap hx0 (edist_ne_top _ _)
  set xs := WithLp.ofLp z with hxs
  have hTfix : T g σ c φ xs = xs := congrArg WithLp.ofLp (show F z = z from hfix)
  have hxsS : xs ∈ Simp H := hz
  -- uniqueness
  have huniq : ∀ y ∈ Simp H, T g σ c φ y = y → y = xs := fun y hy hfy => by
    have h := hlip y xs hy hxsS
    rw [hfy, hTfix] at h
    have := d1_nonneg y xs
    exact eq_of_d1 _ _ (by nlinarith)
  -- rate
  have hrate : ∀ x ∈ Simp H, ∀ n : ℕ, d1 ((T g σ c φ)^[n] x) xs ≤ K ^ n * d1 x xs := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hxn : (T g σ c φ)^[n] x ∈ Simp H := by
        clear ih
        induction n with
        | zero => exact hx
        | succ k ihk => rw [Function.iterate_succ_apply']; exact hmap _ ihk
      calc d1 (T g σ c φ ((T g σ c φ)^[n] x)) xs
          = d1 (T g σ c φ ((T g σ c φ)^[n] x)) (T g σ c φ xs) := by rw [hTfix]
        _ ≤ K * d1 ((T g σ c φ)^[n] x) xs := hlip _ _ hxn hxsS
        _ ≤ K * (K ^ n * d1 x xs) := mul_le_mul_of_nonneg_left ih hK0
        _ = K ^ (n + 1) * d1 x xs := by ring
  refine ⟨xs, hxsS, hTfix, huniq, fun x hx => ⟨hrate x hx, ?_⟩⟩
  have hKn : Tendsto (fun n : ℕ => K ^ n * d1 x xs) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const (d1 x xs)
  refine tendsto_pi_nhds.2 fun h => ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hKn
  rw [Real.dist_eq]
  exact (coord_le_d1 _ _ h).trans (hrate x hx n)

/-! ## The condition is not empty, and it fails where uniqueness fails -/

/-- Saving rising with wealth: `1/2` at zero wealth, `11/20` at the whole stock. -/
def φe (z : ℝ) : ℝ := 1 / 2 + z / 20

/-- **A wealth-dependent saving rule meeting the condition**: `g = 1`, `σ = 3/5`. -/
theorem example_converges (c : ℝ) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) :
    ∃ xs ∈ Simp H, T 1 (3 / 5) c φe xs = xs ∧ (∀ y ∈ Simp H, T 1 (3 / 5) c φe y = y → y = xs) ∧
      ∀ x ∈ Simp H, (∀ n : ℕ, d1 ((T 1 (3 / 5) c φe)^[n] x) xs ≤ (49 / 50) ^ n * d1 x xs) ∧
        Tendsto (fun n => (T 1 (3 / 5) c φe)^[n] x) atTop (𝓝 xs) := by
  have hK : Kmod 1 (3 / 5) (1 / 2) (1 / 20) (1 / 20) = 49 / 50 := by norm_num [Kmod]
  have h := wealth_saving_contraction (H := H) 1 (3 / 5) c (1 / 2) (1 / 20) (1 / 20) φe one_pos
    (by norm_num) (by norm_num) hc0 hc (by norm_num) (by norm_num) (by norm_num)
    (fun z hz => by unfold φe; linarith [hz.1])
    (fun z hz => by unfold φe; linarith [hz.2])
    (fun a _ b _ => by
      unfold φe
      rw [show 1 / 2 + a / 20 - (1 / 2 + b / 20) = (1 / 20) * (a - b) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)])
    (by rw [hK]; norm_num)
  rw [hK] at h
  exact h

/-- **Two rest points rule the condition out**, for every choice of constants. -/
theorem no_contraction_of_two_rest (g σ c : ℝ) (φ : ℝ → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (x y : H → ℝ) (hx : x ∈ Simp H) (hy : y ∈ Simp H) (hxy : x ≠ y)
    (hfx : T g σ c φ x = x) (hfy : T g σ c φ y = y) :
    ¬ ∃ A δ L : ℝ, 0 < A ∧ 0 ≤ δ ∧ 0 ≤ L ∧ (∀ z ∈ Icc (0 : ℝ) 1, A ≤ φ z) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, φ z ≤ A + δ) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φ a - φ b| ≤ L * |a - b|) ∧
      Kmod g σ A δ L < 1 := by
  rintro ⟨A, δ, L, hA, hδ, hL, hφl, hφu, hφL, hK⟩
  have h := T_lip g σ c A δ L φ hg hσ1 hA hδ hL hφl hφu hφL x y hx hy
  rw [hfx, hfy] at h
  have h0 := d1_nonneg x y
  exact hxy (eq_of_d1 _ _ (by nlinarith))

/-- The stage 365 patience rule with two rest points. -/
def φc (z : ℝ) : ℝ := max (2 / 5) (min (1 / 2) (2 / 5 + (z - 1 / 5) / 6))

set_option linter.unusedSimpArgs false in
/-- **The stage 365 rule fails the condition** (`g = 1`, `σ = 1/5`, two households), for every
choice of `A, δ, L`, because it has the two rest points `(1/2, 1/2)` and `(1/5, 4/5)`. -/
theorem stage365_rule_fails :
    ¬ ∃ A δ L : ℝ, 0 < A ∧ 0 ≤ δ ∧ 0 ≤ L ∧ (∀ z ∈ Icc (0 : ℝ) 1, A ≤ φc z) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, φc z ≤ A + δ) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |φc a - φc b| ≤ L * |a - b|) ∧
      Kmod 1 (1 / 5) A δ L < 1 := by
  have e1 : φc (1 / 5) = 2 / 5 := by norm_num [φc]
  have e2 : φc (4 / 5) = 1 / 2 := by norm_num [φc]
  have e3 : φc (1 / 2) = 9 / 20 := by norm_num [φc]
  have e1' : φc 5⁻¹ = 2 / 5 := by norm_num [φc]
  have e3' : φc 2⁻¹ = 9 / 20 := by norm_num [φc]
  refine no_contraction_of_two_rest (H := Fin 2) 1 (1 / 5) (1 / 2) φc one_pos (by norm_num)
    (fun _ => 1 / 2) ![1 / 5, 4 / 5] ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two]⟩
    ⟨fun h => by fin_cases h <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩ ?_ ?_ ?_
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext h
    fin_cases h <;> simp [T, pφ, Bφ, Fin.sum_univ_two, e1, e2, e3, e1', e3'] <;> norm_num
  · funext h
    fin_cases h <;> simp [T, pφ, Bφ, Fin.sum_univ_two, e1, e2, e3, e1', e3'] <;> norm_num

end WealthSavingContraction

end

#print axioms WealthSavingContraction.step_eq
#print axioms WealthSavingContraction.post_lip
#print axioms WealthSavingContraction.T_lip
#print axioms WealthSavingContraction.T_maps
#print axioms WealthSavingContraction.wealth_saving_contraction
#print axioms WealthSavingContraction.example_converges
#print axioms WealthSavingContraction.no_contraction_of_two_rest
#print axioms WealthSavingContraction.stage365_rule_fails
