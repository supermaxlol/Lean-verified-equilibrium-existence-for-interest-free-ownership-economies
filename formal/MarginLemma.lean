import Mathlib

/-!
# Stage 346: a quantitative margin for the weight `p_k`, and Debreu's weights `Z_k + A p_k`

Stage 339 proved the one-variable inequality of stage 336 for

    L a = sin α cos α e^{−Kα},   F a = ∫₀^α (sin t cos t)² e^{−Kt} dt   (a = cos α).

Stage 342 showed that a weight `w₀ (1 + δ)` keeps Afriat numbers when the base inequality
holds with a margin proportional to `d(p,q) · λ₀ w₀ |c|` and `δ` is small and Lipschitz.

This file proves that margin. With `K σ ≥ 14` (twice the stage-339 exponent) and `μ ≤ 1/40`:

* `scalar_margin` (angles): `G θ − G α + μ ℓ(α) sin θ cos θ (θ − α)² ≤ ℓ(α) sin θ cos θ sin(θ − α)`.
* `margin_ab` (one variable): the stage-336 inequality with spare `μ σ L(a) b (1 − cos h)`.
* `margin_nd` (`n` goods, unit prices, Euclidean distance `d`): with `ν ≤ μσ/2` and `3ν ≤ ε`,

      F(p_k) − F(q_k) + ν d(p,q) L(q_k) p_k |c| ≤ L(q_k) p_k c,   c = q_k − p_k (q·p).

* `pk_perturbed_afriat`: hence every weight `p_k (1 + δ)` with `|δ| ≤ δ0 < 1` and
  `|δ p − δ q| ≤ κ d(p,q)`, `κ ≤ ν (1 − δ0)`, has the Afriat numbers `F(q_k)`, `L(q_k)/(1 + δ q)`.
* `debreu_weight_afriat`: in particular Debreu's weight `A p_k + Z_k = A p_k (1 + Z_k/(A p_k))`
  for every `A` large enough that `M/(Aε) ≤ δ0` and `Lz/(Aε) + M/(Aε²) ≤ ν (1 − δ0)`, where
  `|Z_k| ≤ M` and `Z_k` is `Lz`-Lipschitz on the cap.

Limits: this gives the continuum Afriat *inequalities* for each Debreu consumer. Turning them
into a continuous, concave, strictly monotone utility uses the stage-330/336 infimum
construction with the bounds of `lam_bounds`; that assembly is not repeated here. Uniqueness
of demand is not addressed.
-/

noncomputable section

open Real Set

namespace MarginLemma


/-- The integrand `(sin t cos t)² e^{−K t}`. -/
def g (K t : ℝ) : ℝ := (sin t * cos t) ^ 2 * exp (-K * t)

/-- `G K α = ∫₀^α g`. -/
def G (K α : ℝ) : ℝ := ∫ t in (0:ℝ)..α, g K t

/-- The multiplier in angle coordinates. -/
def ell (K α : ℝ) : ℝ := sin α * cos α * exp (-K * α)

theorem g_continuous (K : ℝ) : Continuous (g K) := by
  unfold g; fun_prop

theorem G_hasDerivAt (K α : ℝ) : HasDerivAt (G K) (g K α) α :=
  ((g_continuous K).integral_hasStrictDerivAt 0 α).hasDerivAt

/-- Pointwise sign, `θ ≥ α`. -/
theorem core_pos (K σ α θ : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hα : σ ≤ sin (2 * α))
    (hθ : σ ≤ sin (2 * θ)) (hd0 : 0 ≤ θ - α) (hd1 : θ - α ≤ π / 2) :
    sin (2 * α) ^ 2 ≤ sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) := by
  have hdiff : sin (2 * α) - sin (2 * θ) ≤ 2 * (θ - α) := by
    have h := abs_sin_sub_sin_le (2 * α) (2 * θ)
    have e : |2 * α - 2 * θ| = 2 * (θ - α) := by
      rw [show 2 * α - 2 * θ = -(2 * (θ - α)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hcos : 1 - (θ - α) ^ 2 / 2 ≤ cos (θ - α) := one_sub_sq_div_two_le_cos
  have hsin : 2 / π * (θ - α) ≤ sin (θ - α) := mul_le_sin hd0 hd1
  set d := θ - α with hd
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hsa1 : sa ≤ 1 := sin_le_one _
  have hst1 : st ≤ 1 := sin_le_one _
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hpi3 := pi_gt_three
  have hpi4 := pi_lt_d2
  have hpos := pi_pos
  have h3 : 3 * d ≤ 5 * (2 / π * d) := by
    rw [show 5 * (2 / π * d) = 10 * d / π by ring, le_div_iff₀ hpos]
    nlinarith
  have hdle : d ≤ 2 := by linarith
  have hkσ : 5 * sa ≤ σ * k := by
    have h1 : 7 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk5 : 5 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have hA : sa - 2 * d - d ^ 2 / 2 ≤ st * cos d := by
    have h1 : st * (1 - d ^ 2 / 2) ≤ st * cos d := mul_le_mul_of_nonneg_left hcos hst0
    nlinarith [mul_nonneg (sub_nonneg.mpr hst1) (sq_nonneg d)]
  have hB : 3 * sa * d ≤ st * k * sin d := by
    have h1 : 5 * sa ≤ st * k := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (by linarith : (0:ℝ) ≤ k)]
    have h2 : 0 ≤ 2 / π * d := by positivity
    have h3' : 5 * sa * (2 / π * d) ≤ st * k * sin d :=
      calc 5 * sa * (2 / π * d) ≤ st * k * (2 / π * d) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ st * k * sin d := mul_le_mul_of_nonneg_left hsin (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left h3 hsa0]
  nlinarith [mul_le_mul_of_nonneg_left hA hsa0, mul_nonneg hsa0 (mul_nonneg hd0 (by linarith : (0:ℝ) ≤ 2 - d))]

/-- Pointwise sign, `θ ≤ α`. -/
theorem core_neg (K σ α θ : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hα : σ ≤ sin (2 * α))
    (hθ : σ ≤ sin (2 * θ)) (hd0 : θ - α ≤ 0) (hd1 : -(π / 2) ≤ θ - α) :
    sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) ≤ sin (2 * α) ^ 2 := by
  have hc : cos (θ - α) = cos (α - θ) := by rw [show α - θ = -(θ - α) by ring, cos_neg]
  have hs : sin (θ - α) = - sin (α - θ) := by rw [show α - θ = -(θ - α) by ring, sin_neg, neg_neg]
  rw [hc, hs]
  have he0 : 0 ≤ α - θ := by linarith
  have hdiff : sin (2 * θ) - sin (2 * α) ≤ 2 * (α - θ) := by
    have h := abs_sin_sub_sin_le (2 * θ) (2 * α)
    have e : |2 * θ - 2 * α| = 2 * (α - θ) := by
      rw [show 2 * θ - 2 * α = -(2 * (α - θ)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hsin : 2 / π * (α - θ) ≤ sin (α - θ) := mul_le_sin he0 (by linarith)
  have hce : cos (α - θ) ≤ 1 := cos_le_one _
  set e := α - θ with he
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hpi4 := pi_lt_d2
  have hpos := pi_pos
  have h3 : 3 * e ≤ 5 * (2 / π * e) := by
    rw [show 5 * (2 / π * e) = 10 * e / π by ring, le_div_iff₀ hpos]
    nlinarith
  have hkσ : 5 * sa ≤ σ * k := by
    have h1 : 7 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk5 : 5 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have h2pe : 0 ≤ 2 / π * e := by positivity
  have hse : 0 ≤ sin e := le_trans h2pe hsin
  have hks : 3 * e ≤ k * sin e := by
    have h1 : 5 * sin e ≤ k * sin e := mul_le_mul_of_nonneg_right hk5 hse
    linarith
  by_cases hX : sa * cos e - k * sin e ≤ 0
  · have : st * (sa * cos e + k * -sin e) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hst0 (by linarith)
    nlinarith [sq_nonneg sa]
  · push Not at hX
    have h1 : st * (sa * cos e - k * sin e) ≤ (sa + 2 * e) * (sa * cos e - k * sin e) :=
      mul_le_mul_of_nonneg_right (by linarith) hX.le
    have h2 : (sa + 2 * e) * (sa * cos e - k * sin e) ≤ (sa + 2 * e) * (sa - k * sin e) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hce hsa0]) (by linarith)
    have h3'' : (sa + 2 * e) * (3 * e) ≤ (sa + 2 * e) * (k * sin e) :=
      mul_le_mul_of_nonneg_left hks (by linarith)
    nlinarith [mul_nonneg hsa0 he0, sq_nonneg e]

/-- The difference whose sign we need, for fixed `θ`. -/
def phi (K θ x : ℝ) : ℝ :=
  sin x * cos x * exp (-K * x) * (sin θ * cos θ) * sin (θ - x) - G K θ + G K x

/-- Its derivative. -/
def phid (K θ x : ℝ) : ℝ :=
  exp (-K * x) / 4 * (sin (2 * x) ^ 2 - sin (2 * θ) * (sin (2 * x) * cos (θ - x) +
      (K * sin (2 * x) - 2 * cos (2 * x)) * sin (θ - x)))

theorem phi_deriv (K θ x : ℝ) : HasDerivAt (phi K θ) (phid K θ x) x := by
  have he : HasDerivAt (fun y => exp (-K * y)) (exp (-K * x) * (-K * 1)) x :=
    ((hasDerivAt_id' x).const_mul (-K)).exp
  have hS : HasDerivAt (fun y => sin (θ - y)) (cos (θ - x) * (0 - 1)) x :=
    ((hasDerivAt_const x θ).sub (hasDerivAt_id' x)).sin
  have h : HasDerivAt (phi K θ) _ x :=
    ((((((hasDerivAt_sin x).mul (hasDerivAt_cos x)).mul he).mul_const
      (sin θ * cos θ)).mul hS).sub_const (G K θ)).add (G_hasDerivAt K x)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold phid g
  rw [sin_two_mul, sin_two_mul, cos_two_mul]
  have hx := sin_sq_add_cos_sq x
  linear_combination (-(sin θ * cos θ) * sin (θ - x) * exp (-K * x)) * hx

theorem phi_self (K θ : ℝ) : phi K θ θ = 0 := by simp [phi]

/-- **The scalar inequality in angle coordinates.** -/
theorem scalar_angle (K σ α0 α1 : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (h0 : 0 ≤ α0)
    (h1 : α1 ≤ π / 2) (hS : ∀ x, α0 ≤ x → x ≤ α1 → σ ≤ sin (2 * x)) (α θ : ℝ)
    (hα0 : α0 ≤ α) (hα1 : α ≤ α1) (hθ0 : α0 ≤ θ) (hθ1 : θ ≤ α1) :
    G K θ - G K α ≤ ell K α * (sin θ * cos θ) * sin (θ - α) := by
  have hcont : Continuous (phi K θ) :=
    continuous_iff_continuousAt.2 fun x => (phi_deriv K θ x).continuousAt
  suffices h : 0 ≤ phi K θ α by unfold phi at h; unfold ell; linarith
  rcases le_total α θ with hle | hle
  · have hanti : AntitoneOn (phi K θ) (Icc α θ) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := phid K θ) (convex_Icc α θ)
        hcont.continuousOn (fun x _ => (phi_deriv K θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_pos K σ x θ hσ hK (hS x (by linarith [hx.1]) (by linarith [hx.2]))
        (hS θ hθ0 hθ1) (by linarith [hx.2]) (by linarith [hx.1])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold phid
      nlinarith
    have := hanti ⟨le_refl α, hle⟩ ⟨hle, le_refl θ⟩ hle
    rw [phi_self] at this; exact this
  · have hmono : MonotoneOn (phi K θ) (Icc θ α) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := phid K θ) (convex_Icc θ α)
        hcont.continuousOn (fun x _ => (phi_deriv K θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_neg K σ x θ hσ hK (hS x (by linarith [hx.1]) (by linarith [hx.2]))
        (hS θ hθ0 hθ1) (by linarith [hx.1]) (by linarith [hx.2])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold phid
      nlinarith
    have := hmono ⟨le_refl θ, hle⟩ ⟨hle, le_refl α⟩ hle
    rw [phi_self] at this; exact this

/-- `F` and `L` in the coordinate `a = q_k = cos α`. -/
def F (K a : ℝ) : ℝ := G K (arccos a)
def L (K a : ℝ) : ℝ := ell K (arccos a)

/-- `sin 2α ≥ σ` on the angle range, from `σ² ≤ 4 a² (1 − a²)` on `[ε, β]`. -/
theorem sin_two_ge (σ ε β : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (x : ℝ)
    (hx0 : arccos β ≤ x) (hx1 : x ≤ arccos ε) : σ ≤ sin (2 * x) := by
  have hx0' : 0 ≤ x := (arccos_nonneg β).trans hx0
  have hx1' : x ≤ π / 2 := hx1.trans (arccos_le_pi_div_two.mpr hε)
  have hpos := pi_pos
  have hc1 : cos x ≤ β := by
    have := cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg β) (by linarith) hx0
    rwa [cos_arccos (by linarith) hβ] at this
  have hc0 : ε ≤ cos x := by
    have := cos_le_cos_of_nonneg_of_le_pi hx0' (arccos_le_pi ε) hx1
    rwa [cos_arccos (by linarith) (by linarith)] at this
  have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx0' (by linarith)
  have hy : (2 * sin x * cos x) ^ 2 = 4 * cos x ^ 2 * (1 - cos x ^ 2) := by
    linear_combination (4 * cos x ^ 2) * sin_sq_add_cos_sq x
  have hb := hσa (cos x) hc0 hc1
  rw [← hy] at hb
  have hy0 : 0 ≤ 2 * sin x * cos x := by
    have := hε.trans hc0; positivity
  rw [sin_two_mul]
  by_contra hlt; push Not at hlt
  nlinarith

/-- **Stage 339: the scalar inequality of stage 336, explicitly.** -/
theorem scalar_ab (K σ ε β : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β)
    (hβ : β ≤ 1) (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (a b : ℝ)
    (ha0 : ε ≤ a) (ha1 : a ≤ β) (hb0 : ε ≤ b) (hb1 : b ≤ β) :
    F K b - F K a ≤ L K a * (b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2))))) := by
  have key := scalar_angle K σ (arccos β) (arccos ε) hσ hK (arccos_nonneg _)
    (arccos_le_pi_div_two.mpr hε) (sin_two_ge σ ε β hσ hε hεβ hβ hσa) (arccos a) (arccos b)
    (arccos_le_arccos ha1) (arccos_le_arccos ha0) (arccos_le_arccos hb1) (arccos_le_arccos hb0)
  have hca : cos (arccos a) = a := cos_arccos (by linarith) (by linarith)
  have hcb : cos (arccos b) = b := cos_arccos (by linarith) (by linarith)
  have hsa : sin (arccos a) = √(1 - a ^ 2) := sin_arccos a
  have hsb : sin (arccos b) = √(1 - b ^ 2) := sin_arccos b
  have hid : b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2)))) =
      sin (arccos b) * cos (arccos b) * sin (arccos b - arccos a) := by
    rw [sin_sub, hca, hcb, hsa, hsb, Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 1 - a ^ 2)]
    have hsb2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
    linear_combination (-(a * b)) * hsb2
  rw [hid]
  unfold F L
  linarith [key]

/-- Bounds on `L`, as required by stage 336 (`ℓ ≤ L ≤ Λ`). -/
theorem L_bounds (K σ ε β : ℝ) (hK0 : 0 ≤ K) (hσ : 0 < σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β)
    (hβ : β ≤ 1) (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (a : ℝ)
    (ha0 : ε ≤ a) (ha1 : a ≤ β) :
    σ / 2 * exp (-K * (π / 2)) ≤ L K a ∧ L K a ≤ 1 := by
  have hα0 : 0 ≤ arccos a := arccos_nonneg a
  have hα1 : arccos a ≤ π / 2 := arccos_le_pi_div_two.mpr (by linarith)
  have hpos := pi_pos
  have hs := sin_two_ge σ ε β hσ hε hεβ hβ hσa (arccos a) (arccos_le_arccos ha1)
    (arccos_le_arccos ha0)
  rw [sin_two_mul] at hs
  have hsn : 0 ≤ sin (arccos a) := sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith)
  have hcn : 0 ≤ cos (arccos a) := cos_nonneg_of_mem_Icc ⟨by linarith, hα1⟩
  have hs1 := sin_le_one (arccos a)
  have hc1 := cos_le_one (arccos a)
  have he1 : exp (-K * arccos a) ≤ 1 := by
    rw [← exp_zero]; exact exp_le_exp.mpr (by nlinarith)
  have he2 : exp (-K * (π / 2)) ≤ exp (-K * arccos a) := exp_le_exp.mpr (by nlinarith)
  have hep := exp_pos (-K * (π / 2))
  unfold L ell
  constructor
  · have hsc : σ / 2 ≤ sin (arccos a) * cos (arccos a) := by linarith
    exact mul_le_mul hsc he2 hep.le (mul_nonneg hsn hcn)
  · have hsc : sin (arccos a) * cos (arccos a) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul hsc he1 (exp_pos _).le zero_le_one]

/-- The symmetric range `β² ≤ 1 − ε²` with `σ = 2 ε √(1 − ε²)`. -/
theorem sigma_symmetric (ε β : ℝ) (hε : 0 < ε) (hεβ : ε ≤ β) (hβ : β ^ 2 ≤ 1 - ε ^ 2) :
    0 < 2 * ε * √(1 - ε ^ 2) ∧ β ≤ 1 ∧
      ∀ a, ε ≤ a → a ≤ β → (2 * ε * √(1 - ε ^ 2)) ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2) := by
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have hs : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : √(1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨by positivity, by nlinarith, fun a ha0 ha1 => ?_⟩
  have e : (2 * ε * √(1 - ε ^ 2)) ^ 2 = 4 * ε ^ 2 * (1 - ε ^ 2) := by
    rw [mul_pow, hs2]; ring
  rw [e]
  have h1 : ε ^ 2 ≤ a ^ 2 := by nlinarith
  have h2 : a ^ 2 ≤ 1 - ε ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]


/-! ### Stage 346: the quantitative margin -/

set_option maxHeartbeats 1600000 in
/-- The bracket with margin, `θ ≥ α`. -/
theorem core_pos_m (K σ μ α θ : ℝ) (hσ : 0 < σ) (hK : 14 ≤ K * σ) (_hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / 40) (hα : σ ≤ sin (2 * α)) (hθ : σ ≤ sin (2 * θ)) (hd0 : 0 ≤ θ - α)
    (hd1 : θ - α ≤ π / 2) :
    sin (2 * α) ^ 2 + μ * sin (2 * θ) * ((K * sin (2 * α) - 2 * cos (2 * α)) * (θ - α) ^ 2 +
      2 * sin (2 * α) * (θ - α)) ≤ sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) := by
  have hdiff : sin (2 * α) - sin (2 * θ) ≤ 2 * (θ - α) := by
    have h := abs_sin_sub_sin_le (2 * α) (2 * θ)
    have e : |2 * α - 2 * θ| = 2 * (θ - α) := by
      rw [show 2 * α - 2 * θ = -(2 * (θ - α)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hcos : 1 - (θ - α) ^ 2 / 2 ≤ cos (θ - α) := one_sub_sq_div_two_le_cos
  have hsin : 2 / π * (θ - α) ≤ sin (θ - α) := mul_le_sin hd0 hd1
  have hpos := pi_pos
  have hpi4 := pi_lt_d2
  have hdD : θ - α ≤ 8 / 5 * (2 / π * (θ - α)) := by
    have e : θ - α = π / 2 * (2 / π * (θ - α)) := by field_simp
    have h0 : 0 ≤ 2 / π * (θ - α) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpi4.le h0]
  set d := θ - α with hd
  set D := 2 / π * d with hDdef
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hsa1 : sa ≤ 1 := sin_le_one _
  have hst1 : st ≤ 1 := sin_le_one _
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hD0 : 0 ≤ D := by positivity
  have hd16 : d ≤ 8 / 5 := by linarith
  have hkσ : 12 * sa ≤ σ * k := by
    have h1 : 14 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk12 : 12 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have hk0 : 0 ≤ k := by linarith
  have hsk : 12 * sa ≤ st * k := by nlinarith [mul_le_mul_of_nonneg_right hθ hk0]
  have hstk0 : 0 ≤ st * k := mul_nonneg hst0 hk0
  have hT : st * k * D ≤ st * k * sin d := mul_le_mul_of_nonneg_left hsin hstk0
  have hA : sa - 2 * d - d ^ 2 / 2 ≤ st * cos d := by
    have h1 : st * (1 - d ^ 2 / 2) ≤ st * cos d := mul_le_mul_of_nonneg_left hcos hst0
    nlinarith [mul_nonneg (sub_nonneg.mpr hst1) (sq_nonneg d)]
  have hA' : sa * (sa - 2 * d - d ^ 2 / 2) ≤ sa * (st * cos d) :=
    mul_le_mul_of_nonneg_left hA hsa0
  have hd2 : d ^ 2 ≤ 64 / 25 * D := by nlinarith
  have h1 : st * k * d ^ 2 ≤ st * k * (64 / 25 * D) := mul_le_mul_of_nonneg_left hd2 hstk0
  have h2 : sa * d ≤ sa * (8 / 5 * D) := mul_le_mul_of_nonneg_left hdD hsa0
  have h3 : 12 * sa * D ≤ st * k * D := mul_le_mul_of_nonneg_right hsk hD0
  have h4 : st * sa * d ≤ sa * d := by
    nlinarith [mul_le_mul_of_nonneg_left hst1 (mul_nonneg hsa0 hd0)]
  have h5 : sa * d ^ 2 ≤ 8 / 5 * (sa * d) := by
    nlinarith [mul_le_mul_of_nonneg_left hd16 (mul_nonneg hsa0 hd0)]
  have h6 : μ * (st * k * d ^ 2) ≤ 1 / 40 * (st * k * d ^ 2) :=
    mul_le_mul_of_nonneg_right hμ (mul_nonneg hstk0 (sq_nonneg d))
  have h7 : μ * (st * sa * d) ≤ 1 / 40 * (st * sa * d) :=
    mul_le_mul_of_nonneg_right hμ (mul_nonneg (mul_nonneg hst0 hsa0) hd0)
  have e : μ * st * (k * d ^ 2 + 2 * sa * d) = μ * (st * k * d ^ 2) + 2 * (μ * (st * sa * d)) := by
    ring
  rw [e]
  nlinarith [mul_nonneg hsa0 hD0]

/-- A sign lemma, extracted from stage 339's `core_neg`. -/
theorem neg_core_gen (sa st k e ce se : ℝ) (hsa0 : 0 ≤ sa) (hst0 : 0 ≤ st)
    (hdiff : st - sa ≤ 2 * e) (he0 : 0 ≤ e) (hks : 3 * e ≤ k * se) (hce : ce ≤ 1) :
    st * (sa * ce - k * se) ≤ sa ^ 2 := by
  by_cases hX : sa * ce - k * se ≤ 0
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hst0 hX, sq_nonneg sa]
  · push Not at hX
    have h1 : st * (sa * ce - k * se) ≤ (sa + 2 * e) * (sa * ce - k * se) :=
      mul_le_mul_of_nonneg_right (by linarith) hX.le
    have h2 : (sa + 2 * e) * (sa * ce - k * se) ≤ (sa + 2 * e) * (sa - k * se) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hce hsa0]) (by linarith)
    have h3 : (sa + 2 * e) * (3 * e) ≤ (sa + 2 * e) * (k * se) :=
      mul_le_mul_of_nonneg_left hks (by linarith)
    nlinarith [mul_nonneg hsa0 he0, sq_nonneg e]

/-- The bracket with margin, `θ ≤ α`. -/
theorem core_neg_m (K σ μ α θ : ℝ) (hσ : 0 < σ) (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / 40) (hα : σ ≤ sin (2 * α)) (hθ : σ ≤ sin (2 * θ)) (hd0 : θ - α ≤ 0)
    (hd1 : -(π / 2) ≤ θ - α) :
    sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) ≤
    sin (2 * α) ^ 2 + μ * sin (2 * θ) * ((K * sin (2 * α) - 2 * cos (2 * α)) * (θ - α) ^ 2 +
      2 * sin (2 * α) * (θ - α)) := by
  have he0 : 0 ≤ α - θ := by linarith
  have hdiff : sin (2 * θ) - sin (2 * α) ≤ 2 * (α - θ) := by
    have h := abs_sin_sub_sin_le (2 * θ) (2 * α)
    have e : |2 * θ - 2 * α| = 2 * (α - θ) := by
      rw [show 2 * θ - 2 * α = -(2 * (α - θ)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hsin : 2 / π * (α - θ) ≤ sin (α - θ) := mul_le_sin he0 (by linarith)
  have hce : cos (α - θ) ≤ 1 := cos_le_one _
  have hpos := pi_pos
  have hpi4 := pi_lt_d2
  have hes : α - θ ≤ 8 / 5 * sin (α - θ) := by
    have e : α - θ = π / 2 * (2 / π * (α - θ)) := by field_simp
    have h0 : 0 ≤ 2 / π * (α - θ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpi4.le h0]
  rw [show θ - α = -(α - θ) by ring, cos_neg, sin_neg]
  set e := α - θ with he
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hsa1 : sa ≤ 1 := sin_le_one _
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hse0 : 0 ≤ sin e := by linarith
  have hkσ : 12 * sa ≤ σ * k := by
    have h1 : 14 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk12 : 12 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have hks : 3 * e ≤ (k - 1) * sin e := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (11:ℝ) ≤ k - 1) hse0]
  have hgen := neg_core_gen sa st (k - 1) e (cos e) (sin e) hsa0 hst0 (by linarith) he0 hks hce
  have h1 : 0 ≤ μ * (st * k * e ^ 2) :=
    mul_nonneg hμ0 (mul_nonneg (mul_nonneg hst0 (by linarith)) (sq_nonneg e))
  have hsse : st * sa * e ≤ st * e := by
    nlinarith [mul_le_mul_of_nonneg_left hsa1 (mul_nonneg hst0 he0)]
  have h2 : μ * (st * sa * e) ≤ 1 / 40 * (st * e) :=
    mul_le_mul hμ hsse (mul_nonneg (mul_nonneg hst0 hsa0) he0) (by norm_num)
  have h3 : st * e ≤ 8 / 5 * (st * sin e) := by nlinarith [mul_le_mul_of_nonneg_left hes hst0]
  have e2 : μ * st * (k * (-e) ^ 2 + 2 * sa * -e) =
      μ * (st * k * e ^ 2) - 2 * (μ * (st * sa * e)) := by ring
  rw [e2]
  nlinarith [mul_nonneg hst0 hse0]

/-- `φ` minus the margin term. -/
def psi (K μ θ x : ℝ) : ℝ :=
  phi K θ x - μ * (sin x * cos x * exp (-K * x)) * (sin θ * cos θ) * ((θ - x) * (θ - x))

def psid (K μ θ x : ℝ) : ℝ :=
  phid K θ x + exp (-K * x) / 4 * (μ * sin (2 * θ) *
    ((K * sin (2 * x) - 2 * cos (2 * x)) * (θ - x) ^ 2 + 2 * sin (2 * x) * (θ - x)))

theorem psi_deriv (K μ θ x : ℝ) : HasDerivAt (psi K μ θ) (psid K μ θ x) x := by
  have he : HasDerivAt (fun y => exp (-K * y)) (exp (-K * x) * (-K * 1)) x :=
    ((hasDerivAt_id' x).const_mul (-K)).exp
  have hS : HasDerivAt (fun y => θ - y) (0 - 1) x :=
    (hasDerivAt_const x θ).sub (hasDerivAt_id' x)
  have h : HasDerivAt (psi K μ θ) _ x :=
    (phi_deriv K θ x).sub (((((((hasDerivAt_sin x).mul (hasDerivAt_cos x)).mul he).const_mul
      μ).mul_const (sin θ * cos θ))).mul (hS.mul hS))
  refine h.congr_deriv ?_
  try simp only [Pi.mul_apply]
  unfold psid
  rw [sin_two_mul, sin_two_mul, cos_two_mul]
  have hx := sin_sq_add_cos_sq x
  linear_combination (μ * exp (-K * x) * (sin θ * cos θ) * (θ - x) ^ 2) * hx

theorem psi_self (K μ θ : ℝ) : psi K μ θ θ = 0 := by simp [psi, phi]

/-- **The scalar inequality with a quadratic margin, in angles.** -/
theorem scalar_margin (K σ μ α0 α1 : ℝ) (hσ : 0 < σ) (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / 40) (h0 : 0 ≤ α0) (h1 : α1 ≤ π / 2)
    (hS : ∀ x, α0 ≤ x → x ≤ α1 → σ ≤ sin (2 * x)) (α θ : ℝ)
    (hα0 : α0 ≤ α) (hα1 : α ≤ α1) (hθ0 : α0 ≤ θ) (hθ1 : θ ≤ α1) :
    G K θ - G K α + μ * ell K α * (sin θ * cos θ) * (θ - α) ^ 2 ≤
      ell K α * (sin θ * cos θ) * sin (θ - α) := by
  have hcont : Continuous (psi K μ θ) :=
    continuous_iff_continuousAt.2 fun x => (psi_deriv K μ θ x).continuousAt
  suffices h : 0 ≤ psi K μ θ α by unfold psi phi at h; unfold ell; nlinarith [h]
  rcases le_total α θ with hle | hle
  · have hanti : AntitoneOn (psi K μ θ) (Icc α θ) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := psid K μ θ) (convex_Icc α θ)
        hcont.continuousOn (fun x _ => (psi_deriv K μ θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_pos_m K σ μ x θ hσ hK hμ0 hμ
        (hS x (by linarith [hx.1]) (by linarith [hx.2])) (hS θ hθ0 hθ1) (by linarith [hx.2])
        (by linarith [hx.1])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold psid phid
      nlinarith [mul_le_mul_of_nonneg_left (sub_nonpos.mpr hcore) he.le]
    have := hanti ⟨le_refl α, hle⟩ ⟨hle, le_refl θ⟩ hle
    rw [psi_self] at this; exact this
  · have hmono : MonotoneOn (psi K μ θ) (Icc θ α) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := psid K μ θ) (convex_Icc θ α)
        hcont.continuousOn (fun x _ => (psi_deriv K μ θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_neg_m K σ μ x θ hσ hK hμ0 hμ
        (hS x (by linarith [hx.1]) (by linarith [hx.2])) (hS θ hθ0 hθ1) (by linarith [hx.1])
        (by linarith [hx.2])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold psid phid
      nlinarith [mul_nonneg he.le (sub_nonneg.mpr hcore)]
    have := hmono ⟨le_refl θ, hle⟩ ⟨hle, le_refl α⟩ hle
    rw [psi_self] at this; exact this

theorem L_nonneg (K a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ L K a := by
  unfold L ell
  have h1 : 0 ≤ sin (arccos a) := by rw [sin_arccos]; exact Real.sqrt_nonneg _
  have h2 : 0 ≤ cos (arccos a) := by rw [cos_arccos (by linarith) ha1]; exact ha0
  positivity

/-- **The stage-336 inequality with a margin, in the coordinate `a = q_k`, `b = p_k`.** -/
theorem margin_ab (K σ μ ε β : ℝ) (hσ : 0 < σ) (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / 40) (hε : 0 ≤ ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (a b : ℝ)
    (ha0 : ε ≤ a) (ha1 : a ≤ β) (hb0 : ε ≤ b) (hb1 : b ≤ β) :
    F K b - F K a + μ * σ * (L K a * b * (1 - (a * b + √((1 - a ^ 2) * (1 - b ^ 2))))) ≤
      L K a * (b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2))))) := by
  have hS := sin_two_ge σ ε β hσ hε hεβ hβ hσa
  have key := scalar_margin K σ μ (arccos β) (arccos ε) hσ hK hμ0 hμ (arccos_nonneg _)
    (arccos_le_pi_div_two.mpr hε) hS (arccos a) (arccos b)
    (arccos_le_arccos ha1) (arccos_le_arccos ha0) (arccos_le_arccos hb1) (arccos_le_arccos hb0)
  have hθs := hS (arccos b) (arccos_le_arccos hb1) (arccos_le_arccos hb0)
  have hca : cos (arccos a) = a := cos_arccos (by linarith) (by linarith)
  have hcb : cos (arccos b) = b := cos_arccos (by linarith) (by linarith)
  have hsa : sin (arccos a) = √(1 - a ^ 2) := sin_arccos a
  have hsb : sin (arccos b) = √(1 - b ^ 2) := sin_arccos b
  have hsb2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hC : cos (arccos b - arccos a) = a * b + √((1 - a ^ 2) * (1 - b ^ 2)) := by
    rw [cos_sub, hca, hcb, hsa, hsb, Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 1 - a ^ 2)]
    ring
  have hid : b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2)))) =
      sin (arccos b) * cos (arccos b) * sin (arccos b - arccos a) := by
    rw [sin_sub, hca, hcb, hsa, hsb, Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 1 - a ^ 2)]
    linear_combination (-(a * b)) * hsb2
  have hcosb : 1 - (arccos b - arccos a) ^ 2 / 2 ≤ cos (arccos b - arccos a) :=
    one_sub_sq_div_two_le_cos
  have hc1 : cos (arccos b - arccos a) ≤ 1 := cos_le_one _
  have hsθ0 : 0 ≤ sin (arccos b) := by rw [hsb]; exact Real.sqrt_nonneg _
  have hsθ : σ / 2 ≤ sin (arccos b) := by
    rw [sin_two_mul, hcb] at hθs
    nlinarith [mul_nonneg hsθ0 (by linarith : (0:ℝ) ≤ 1 - b)]
  have hpos := pi_pos
  have hα0 : 0 ≤ arccos a := arccos_nonneg a
  have hα1 : arccos a ≤ π / 2 := arccos_le_pi_div_two.mpr (by linarith)
  have hL0 : 0 ≤ L K a := L_nonneg K a (by linarith) (by linarith)
  have hb0' : 0 ≤ b := by linarith
  have hm : σ * (1 - cos (arccos b - arccos a)) ≤ sin (arccos b) * (arccos b - arccos a) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hsθ (by linarith : (0:ℝ) ≤ 1 - cos (arccos b - arccos a)),
      mul_nonneg hsθ0 (by linarith [hcosb] :
        (0:ℝ) ≤ (arccos b - arccos a) ^ 2 - 2 * (1 - cos (arccos b - arccos a)))]
  have hLb : 0 ≤ μ * L K a * b := mul_nonneg (mul_nonneg hμ0 hL0) hb0'
  have h2 := mul_le_mul_of_nonneg_left hm hLb
  rw [hid, ← hC]
  have eF : F K b - F K a = G K (arccos b) - G K (arccos a) := rfl
  have eL : L K a = ell K (arccos a) := rfl
  rw [eF]
  rw [eL] at h2 hLb ⊢
  rw [hcb] at key ⊢
  nlinarith [key, h2]


/-- **Perturbation with a margin.** -/
theorem perturb_afriat {X : Type*} (P : Set X) (V lam0 w0 δ : X → ℝ) (c m : X → X → ℝ)
    (hδ : ∀ q ∈ P, -1 < δ q) (hlam0 : ∀ q ∈ P, 0 ≤ lam0 q) (hw0 : ∀ p ∈ P, 0 ≤ w0 p)
    (hmargin : ∀ p ∈ P, ∀ q ∈ P, V p - V q + m p q ≤ lam0 q * w0 p * c p q)
    (hsmall : ∀ p ∈ P, ∀ q ∈ P,
      |δ p - δ q| * lam0 q * w0 p * |c p q| ≤ m p q * (1 + δ q)) :
    ∀ p ∈ P, ∀ q ∈ P,
      V p - V q ≤ lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q := by
  intro p hp q hq
  have h1 := hmargin p hp q hq
  have h2 := hsmall p hp q hq
  have hq1 : 0 < 1 + δ q := by linarith [hδ q hq]
  have hl := hlam0 q hq
  have hw := hw0 p hp
  have e : lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q =
      lam0 q * w0 p * c p q + (δ p - δ q) * (lam0 q * w0 p * c p q) / (1 + δ q) := by
    field_simp
    ring
  have h3 : -(m p q * (1 + δ q)) ≤ (δ p - δ q) * (lam0 q * w0 p * c p q) := by
    have h4 := neg_abs_le ((δ p - δ q) * (lam0 q * w0 p * c p q))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg hw] at h4
    linarith
  have h5 : -m p q ≤ (δ p - δ q) * (lam0 q * w0 p * c p q) / (1 + δ q) := by
    rw [le_div_iff₀ hq1]
    linarith
  rw [e]
  linarith

/-- **Lipschitz perturbations.**  If the margin is `μ · d(p,q) · λ₀ w₀ |c|`, the
perturbation satisfies `|δ| ≤ δ₀ < 1` and `|δ p − δ q| ≤ κ d(p,q)`, and `κ ≤ μ (1 − δ₀)`,
then the perturbed weight has Afriat numbers. -/
theorem perturb_afriat_lip {X : Type*} (P : Set X) (V lam0 w0 δ : X → ℝ) (c d : X → X → ℝ)
    (μ κ δ0 : ℝ) (hδ0 : δ0 < 1) (hμ : 0 ≤ μ)
    (hδ : ∀ q ∈ P, |δ q| ≤ δ0) (hlam0 : ∀ q ∈ P, 0 ≤ lam0 q) (hw0 : ∀ p ∈ P, 0 ≤ w0 p)
    (hd : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ d p q)
    (hmargin : ∀ p ∈ P, ∀ q ∈ P,
      V p - V q + μ * d p q * (lam0 q * w0 p * |c p q|) ≤ lam0 q * w0 p * c p q)
    (hlip : ∀ p ∈ P, ∀ q ∈ P, |δ p - δ q| ≤ κ * d p q) (hκ : κ ≤ μ * (1 - δ0)) :
    ∀ p ∈ P, ∀ q ∈ P,
      V p - V q ≤ lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q := by
  refine perturb_afriat P V lam0 w0 δ c (fun p q => μ * d p q * (lam0 q * w0 p * |c p q|))
    (fun q hq => ?_) hlam0 hw0 hmargin fun p hp q hq => ?_
  · have := neg_abs_le (δ q)
    linarith [hδ q hq]
  · have hA : 0 ≤ lam0 q * w0 p * |c p q| :=
      mul_nonneg (mul_nonneg (hlam0 q hq) (hw0 p hp)) (abs_nonneg _)
    have hq1 : 1 - δ0 ≤ 1 + δ q := by
      have := neg_abs_le (δ q)
      linarith [hδ q hq]
    have h1 : |δ p - δ q| * (lam0 q * w0 p * |c p q|) ≤ κ * d p q * (lam0 q * w0 p * |c p q|) :=
      mul_le_mul_of_nonneg_right (hlip p hp q hq) hA
    have h2 : κ * d p q * (lam0 q * w0 p * |c p q|) ≤
        μ * (1 - δ0) * d p q * (lam0 q * w0 p * |c p q|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (hd p hp q hq)) hA
    have h3 : μ * (1 - δ0) * d p q * (lam0 q * w0 p * |c p q|) ≤
        μ * d p q * (lam0 q * w0 p * |c p q|) * (1 + δ q) := by
      have h4 : 0 ≤ μ * d p q * (lam0 q * w0 p * |c p q|) :=
        mul_nonneg (mul_nonneg hμ (hd p hp q hq)) hA
      have h5 := mul_le_mul_of_nonneg_left hq1 h4
      linarith
    have e : |δ p - δ q| * lam0 q * w0 p * |c p q| =
        |δ p - δ q| * (lam0 q * w0 p * |c p q|) := by ring
    rw [e]
    linarith

/-- **The new multipliers stay uniformly bounded.** -/
theorem lam_bounds (l Λ δ0 lam0 δq : ℝ) (hl : 0 ≤ l) (hδ0 : δ0 < 1) (h1 : l ≤ lam0)
    (h2 : lam0 ≤ Λ) (hδ : |δq| ≤ δ0) :
    l / (1 + δ0) ≤ lam0 / (1 + δq) ∧ lam0 / (1 + δq) ≤ Λ / (1 - δ0) := by
  have ha := neg_abs_le δq
  have hb := le_abs_self δq
  have hq1 : 0 < 1 + δq := by linarith
  have hd1 : 0 < 1 - δ0 := by linarith
  have hd2 : 0 < 1 + δ0 := by linarith
  have hlam0 : 0 ≤ lam0 := hl.trans h1
  constructor
  · rw [div_le_div_iff₀ hd2 hq1]
    have : l * (1 + δq) ≤ lam0 * (1 + δ0) := by
      have h3 : l * (1 + δq) ≤ lam0 * (1 + δq) := mul_le_mul_of_nonneg_right h1 hq1.le
      have h4 : lam0 * (1 + δq) ≤ lam0 * (1 + δ0) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0
      linarith
    exact this
  · rw [div_le_div_iff₀ hq1 hd1]
    have h3 : lam0 * (1 - δ0) ≤ Λ * (1 - δ0) := mul_le_mul_of_nonneg_right h2 hd1.le
    have h4 : Λ * (1 - δ0) ≤ Λ * (1 + δq) := by
      have : 0 ≤ Λ := hlam0.trans h2
      exact mul_le_mul_of_nonneg_left (by linarith) this
    linarith

/-- **Debreu's weight is a small perturbation of `A p_k`.**  On `S_ε`, if `|Z_k| ≤ M` and
`Z_k` is `Lz`-Lipschitz (against a distance `d` that dominates the change in the coordinate
`k`), then `δ = Z_k / (A p_k)` has `|δ| ≤ M / (A ε)` and
`|δ p − δ q| ≤ (Lz / (A ε) + M / (A ε²)) d(p,q)`. -/
theorem debreu_delta {X : Type*} (P : Set X) (pk Zk : X → ℝ) (d : X → X → ℝ)
    (A ε M Lz : ℝ) (hA : 0 < A) (hε : 0 < ε) (hpk : ∀ q ∈ P, ε ≤ pk q)
    (hZ : ∀ q ∈ P, |Zk q| ≤ M) (hZl : ∀ p ∈ P, ∀ q ∈ P, |Zk p - Zk q| ≤ Lz * d p q)
    (hpl : ∀ p ∈ P, ∀ q ∈ P, |pk p - pk q| ≤ d p q) (hLz : 0 ≤ Lz) :
    (∀ q ∈ P, |Zk q / (A * pk q)| ≤ M / (A * ε)) ∧
      ∀ p ∈ P, ∀ q ∈ P, |Zk p / (A * pk p) - Zk q / (A * pk q)| ≤
        (Lz / (A * ε) + M / (A * ε ^ 2)) * d p q := by
  have hpos : ∀ q ∈ P, 0 < A * pk q := fun q hq => mul_pos hA (hε.trans_le (hpk q hq))
  have hAe : 0 < A * ε := mul_pos hA hε
  constructor
  · intro q hq
    rw [abs_div, abs_of_pos (hpos q hq), div_le_div_iff₀ (hpos q hq) hAe]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hZ q hq)
    have h1 : |Zk q| * (A * ε) ≤ M * (A * ε) := mul_le_mul_of_nonneg_right (hZ q hq) hAe.le
    have h2 : M * (A * ε) ≤ M * (A * pk q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpk q hq) hA.le) hM
    linarith
  · intro p hp q hq
    have hp0 := hpos p hp
    have hq0 := hpos q hq
    have e : Zk p / (A * pk p) - Zk q / (A * pk q) =
        (Zk p - Zk q) / (A * pk p) + Zk q * (pk q - pk p) / (A * pk p * pk q) := by
      have : pk q ≠ 0 := (hε.trans_le (hpk q hq)).ne'
      have : pk p ≠ 0 := (hε.trans_le (hpk p hp)).ne'
      field_simp
      ring
    rw [e]
    have hdpq : 0 ≤ d p q := (abs_nonneg _).trans (hpl p hp q hq)
    have hM : 0 ≤ M := (abs_nonneg _).trans (hZ q hq)
    have t1 : |(Zk p - Zk q) / (A * pk p)| ≤ Lz / (A * ε) * d p q := by
      rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
      have h1 : Lz * d p q ≤ Lz / (A * ε) * d p q * (A * pk p) := by
        have : Lz / (A * ε) * d p q * (A * pk p) = Lz * d p q * (pk p / ε) := by
          field_simp
        rw [this]
        have h2 : 1 ≤ pk p / ε := (one_le_div hε).2 (hpk p hp)
        nlinarith [mul_nonneg hLz hdpq]
      linarith [hZl p hp q hq]
    have hpp : 0 < pk p := hε.trans_le (hpk p hp)
    have hpq : 0 < pk q := hε.trans_le (hpk q hq)
    have t2 : |Zk q * (pk q - pk p) / (A * pk p * pk q)| ≤ M / (A * ε ^ 2) * d p q := by
      have hD : 0 < A * pk p * pk q := by positivity
      rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_mul]
      have h1 : |Zk q| * |pk q - pk p| ≤ M * d p q := by
        rw [abs_sub_comm]
        exact mul_le_mul (hZ q hq) (hpl p hp q hq) (abs_nonneg _) hM
      have h2 : M * d p q ≤ M / (A * ε ^ 2) * d p q * (A * pk p * pk q) := by
        have : M / (A * ε ^ 2) * d p q * (A * pk p * pk q) =
            M * d p q * ((pk p / ε) * (pk q / ε)) := by
          field_simp
        rw [this]
        have h3 : 1 ≤ pk p / ε := (one_le_div hε).2 (hpk p hp)
        have h4 : 1 ≤ pk q / ε := (one_le_div hε).2 (hpk q hq)
        have h5 : 1 ≤ (pk p / ε) * (pk q / ε) := by nlinarith
        nlinarith [mul_nonneg hM hdpq]
      linarith
    calc |(Zk p - Zk q) / (A * pk p) + Zk q * (pk q - pk p) / (A * pk p * pk q)|
        ≤ |(Zk p - Zk q) / (A * pk p)| + |Zk q * (pk q - pk p) / (A * pk p * pk q)| :=
          abs_add_le _ _
      _ ≤ Lz / (A * ε) * d p q + M / (A * ε ^ 2) * d p q := add_le_add t1 t2
      _ = (Lz / (A * ε) + M / (A * ε ^ 2)) * d p q := by ring

/-! ### `n` goods: the margin for Debreu's consumer, and the perturbed weights -/

section NDim

variable {S : Type*} [Fintype S] [DecidableEq S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- Euclidean distance. -/
def dist2 (p q : S → ℝ) : ℝ := √(∑ s, (p s - q s) ^ 2)

theorem cs_bound (k : S) (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1)
    (hq : ∑ s, q s ^ 2 = 1) :
    dot q p ≤ q k * p k + Real.sqrt ((1 - q k ^ 2) * (1 - p k ^ 2)) := by
  have e1 := Finset.add_sum_erase Finset.univ (fun s => q s * p s) (Finset.mem_univ k)
  have e2 := Finset.add_sum_erase Finset.univ (fun s => q s ^ 2) (Finset.mem_univ k)
  have e3 := Finset.add_sum_erase Finset.univ (fun s => p s ^ 2) (Finset.mem_univ k)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase k) q p
  have hq' : ∑ s ∈ Finset.univ.erase k, q s ^ 2 = 1 - q k ^ 2 := by linarith
  have hp' : ∑ s ∈ Finset.univ.erase k, p s ^ 2 = 1 - p k ^ 2 := by linarith
  rw [hq', hp'] at h
  have h2 := Real.abs_le_sqrt h
  have h3 := le_abs_self (∑ s ∈ Finset.univ.erase k, q s * p s)
  have hd : dot q p = q k * p k + ∑ s ∈ Finset.univ.erase k, q s * p s := by
    unfold dot
    linarith
  linarith

omit [DecidableEq S] in
theorem dist2_sq (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) :
    dist2 p q ^ 2 = 2 - 2 * dot q p := by
  have h0 : 0 ≤ ∑ s, (p s - q s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  unfold dist2
  rw [Real.sq_sqrt h0]
  have e : ∑ s, (p s - q s) ^ 2 = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
    unfold dot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, hp, hq]
  ring

omit [DecidableEq S] in
theorem coord_le_dist2 (k : S) (p q : S → ℝ) : |p k - q k| ≤ dist2 p q := by
  unfold dist2
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun s => (p s - q s) ^ 2) (fun s _ => sq_nonneg _)
    (Finset.mem_univ k)

set_option maxHeartbeats 1600000 in
/-- **The margin for Debreu's weight-`p_k` consumer, `n` goods.** -/
theorem margin_nd (K σ μ ε β ν : ℝ) (hσ : 0 < σ) (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 1 / 40) (hε : 0 ≤ ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2))
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ μ * σ / 2) (hν2 : 3 * ν ≤ ε) (k : S) (p q : S → ℝ)
    (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) (hp0 : ∀ s, 0 ≤ p s)
    (hq0 : ∀ s, 0 ≤ q s) (ha0 : ε ≤ q k) (ha1 : q k ≤ β) (hb0 : ε ≤ p k) (hb1 : p k ≤ β) :
    F K (p k) - F K (q k) + ν * dist2 p q * (L K (q k) * p k * |q k - p k * dot q p|) ≤
      L K (q k) * p k * (q k - p k * dot q p) := by
  have hm := margin_ab K σ μ ε β hσ hK hμ0 hμ hε hεβ hβ hσa (q k) (p k) ha0 ha1 hb0 hb1
  have hcs := cs_bound k p q hp hq
  have hd2 := dist2_sq p q hp hq
  have hd0 : 0 ≤ dist2 p q := Real.sqrt_nonneg _
  have ht0 : 0 ≤ dot q p := Finset.sum_nonneg fun s _ => mul_nonneg (hq0 s) (hp0 s)
  have hL0 : 0 ≤ L K (q k) := L_nonneg K (q k) (by linarith) (by linarith)
  have hrs : √((1 - q k ^ 2) * (1 - p k ^ 2)) = √(1 - q k ^ 2) * √(1 - p k ^ 2) :=
    Real.sqrt_mul (by nlinarith) _
  have hr2 : √(1 - q k ^ 2) ^ 2 = 1 - q k ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs2 : √(1 - p k ^ 2) ^ 2 = 1 - p k ^ 2 := Real.sq_sqrt (by nlinarith)
  rw [hrs] at hm hcs
  set a := q k with ha
  set b := p k with hb
  set r := √(1 - a ^ 2) with hr
  set s := √(1 - b ^ 2) with hs
  set t := dot q p with ht
  set d := dist2 p q with hd
  set C := a * b + r * s with hC
  have hb0' : 0 ≤ b := by linarith
  have hid1 : (a * s - b * r) ^ 2 + C ^ 2 = 1 := by
    rw [hC]; linear_combination (a ^ 2 + r ^ 2) * hs2 + hr2
  have hc1 : a - b * C = s * (a * s - b * r) := by
    rw [hC]; linear_combination (-a) * hs2
  have hs1 : s ^ 2 ≤ 1 := by rw [hs2]; nlinarith
  have hc1sq : (a - b * C) ^ 2 ≤ 2 * (1 - C) := by
    rw [hc1, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hs1 (sq_nonneg (a * s - b * r)), sq_nonneg (1 - C)]
  have hC1 : C ≤ 1 := by nlinarith [sq_nonneg (a * s - b * r)]
  have hD0 : 0 ≤ C - t := by linarith
  have habs : |a - b * t| ≤ |a - b * C| + b * (C - t) := by
    have e : a - b * t = (a - b * C) + b * (C - t) := by ring
    rw [e]
    calc |(a - b * C) + b * (C - t)| ≤ |a - b * C| + |b * (C - t)| := abs_add_le _ _
      _ = |a - b * C| + b * (C - t) := by rw [abs_of_nonneg (mul_nonneg hb0' hD0)]
  have hdc1 : 2 * (d * |a - b * C|) ≤ d ^ 2 + (a - b * C) ^ 2 := by
    have := two_mul_le_add_sq d |a - b * C|
    rw [sq_abs] at this
    linarith
  have hdle : d ≤ 2 := by nlinarith
  have hdbD : d * (b * (C - t)) ≤ 2 * (b * (C - t)) :=
    mul_le_mul_of_nonneg_right hdle (mul_nonneg hb0' hD0)
  have hdc : d * |a - b * t| ≤ 2 * (1 - C) + (1 + 2 * b) * (C - t) := by
    have := mul_le_mul_of_nonneg_left habs hd0
    nlinarith
  have hν3 : ν * (2 * (1 - C)) ≤ μ * σ * (1 - C) := by
    nlinarith [mul_le_mul_of_nonneg_right hν1 (by linarith : (0:ℝ) ≤ 1 - C)]
  have hν4 : ν * ((1 + 2 * b) * (C - t)) ≤ b * (C - t) := by
    have h1 : ν * (1 + 2 * b) ≤ b := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hD0]
  have hν : ν * (d * |a - b * t|) ≤ μ * σ * (1 - C) + b * (C - t) := by
    have := mul_le_mul_of_nonneg_left hdc hν0
    nlinarith
  have hLb : 0 ≤ L K a * b := mul_nonneg hL0 hb0'
  have hfin := mul_le_mul_of_nonneg_left hν hLb
  nlinarith [hfin, hm]

/-- **Every small, Lipschitz perturbation of the weight `p_k` is rationalised.** -/
theorem pk_perturbed_afriat (P : Set (S → ℝ)) (K σ μ ε β ν : ℝ) (hσ : 0 < σ)
    (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 40) (hε : 0 ≤ ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2))
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ μ * σ / 2) (hν2 : 3 * ν ≤ ε) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1 ∧ (∀ s, 0 ≤ q s) ∧ ε ≤ q k ∧ q k ≤ β)
    (δ : (S → ℝ) → ℝ) (δ0 κ : ℝ) (hδ0 : δ0 < 1) (hδ : ∀ q ∈ P, |δ q| ≤ δ0)
    (hlip : ∀ p ∈ P, ∀ q ∈ P, |δ p - δ q| ≤ κ * dist2 p q) (hκ : κ ≤ ν * (1 - δ0)) :
    ∀ p ∈ P, ∀ q ∈ P, F K (p k) - F K (q k) ≤
      L K (q k) / (1 + δ q) * (p k * (1 + δ p)) * (q k - p k * dot q p) :=
  perturb_afriat_lip P (fun q => F K (q k)) (fun q => L K (q k)) (fun p => p k) δ
    (fun p q => q k - p k * dot q p) dist2 ν κ δ0 hδ0 hν0 hδ
    (fun q hq => L_nonneg K (q k) (hε.trans (hP q hq).2.2.1) ((hP q hq).2.2.2.trans hβ))
    (fun p hp => hε.trans (hP p hp).2.2.1)
    (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun p hp q hq => margin_nd K σ μ ε β ν hσ hK hμ0 hμ hε hεβ hβ hσa hν0 hν1 hν2 k p q
      (hP p hp).1 (hP q hq).1 (hP p hp).2.1 (hP q hq).2.1 (hP q hq).2.2.1 (hP q hq).2.2.2
      (hP p hp).2.2.1 (hP p hp).2.2.2)
    hlip hκ

/-- **Debreu's weight `A p_k + Z_k`, for `A` large.** The Afriat inequalities hold on the
continuum with `V q = F(q_k)` and `λ q = L(q_k) / (A (1 + Z_k q / (A q_k)))`. -/
theorem debreu_weight_afriat (P : Set (S → ℝ)) (K σ μ ε β ν : ℝ) (hσ : 0 < σ)
    (hK : 14 ≤ K * σ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 40) (hε0 : 0 < ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2))
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ μ * σ / 2) (hν2 : 3 * ν ≤ ε) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1 ∧ (∀ s, 0 ≤ q s) ∧ ε ≤ q k ∧ q k ≤ β)
    (Zk : (S → ℝ) → ℝ) (A M Lz δ0 : ℝ) (hA : 0 < A) (hLz : 0 ≤ Lz)
    (hZ : ∀ q ∈ P, |Zk q| ≤ M) (hZl : ∀ p ∈ P, ∀ q ∈ P, |Zk p - Zk q| ≤ Lz * dist2 p q)
    (hδ0 : δ0 < 1) (hMA : M / (A * ε) ≤ δ0)
    (hLA : Lz / (A * ε) + M / (A * ε ^ 2) ≤ ν * (1 - δ0)) :
    ∀ p ∈ P, ∀ q ∈ P, F K (p k) - F K (q k) ≤
      L K (q k) / (A * (1 + Zk q / (A * q k))) * (A * p k + Zk p) *
        (q k - p k * dot q p) := by
  obtain ⟨h1, h2⟩ := debreu_delta P (fun q => q k) Zk dist2 A ε M Lz hA hε0
    (fun q hq => (hP q hq).2.2.1) hZ hZl (fun p _ q _ => coord_le_dist2 k p q) hLz
  have key := pk_perturbed_afriat P K σ μ ε β ν hσ hK hμ0 hμ hε0.le hεβ hβ hσa hν0 hν1 hν2 k hP
    (fun q => Zk q / (A * q k)) δ0 (Lz / (A * ε) + M / (A * ε ^ 2)) hδ0
    (fun q hq => (h1 q hq).trans hMA) h2 hLA
  intro p hp q hq
  have hk := key p hp q hq
  have hpk : 0 < p k := hε0.trans_le (hP p hp).2.2.1
  have hδq : 0 < 1 + Zk q / (A * q k) := by
    have := neg_abs_le (Zk q / (A * q k))
    linarith [(h1 q hq).trans hMA]
  have e : L K (q k) / (A * (1 + Zk q / (A * q k))) * (A * p k + Zk p) =
      L K (q k) / (1 + Zk q / (A * q k)) * (p k * (1 + Zk p / (A * p k))) := by
    field_simp
  rw [e]
  exact hk

end NDim

end MarginLemma

end

#print axioms MarginLemma.g_continuous
#print axioms MarginLemma.G_hasDerivAt
#print axioms MarginLemma.core_pos
#print axioms MarginLemma.core_neg
#print axioms MarginLemma.phi_deriv
#print axioms MarginLemma.phi_self
#print axioms MarginLemma.scalar_angle
#print axioms MarginLemma.sin_two_ge
#print axioms MarginLemma.scalar_ab
#print axioms MarginLemma.L_bounds
#print axioms MarginLemma.sigma_symmetric
#print axioms MarginLemma.core_pos_m
#print axioms MarginLemma.neg_core_gen
#print axioms MarginLemma.core_neg_m
#print axioms MarginLemma.psi_deriv
#print axioms MarginLemma.psi_self
#print axioms MarginLemma.scalar_margin
#print axioms MarginLemma.L_nonneg
#print axioms MarginLemma.margin_ab
#print axioms MarginLemma.perturb_afriat
#print axioms MarginLemma.perturb_afriat_lip
#print axioms MarginLemma.lam_bounds
#print axioms MarginLemma.debreu_delta
#print axioms MarginLemma.cs_bound
#print axioms MarginLemma.dist2_sq
#print axioms MarginLemma.coord_le_dist2
#print axioms MarginLemma.margin_nd
#print axioms MarginLemma.pk_perturbed_afriat
#print axioms MarginLemma.debreu_weight_afriat
