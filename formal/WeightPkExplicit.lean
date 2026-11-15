import Mathlib

/-!
Stage 339 (discharges the scalar hypothesis of stage 336): the one-variable inequality for the
weight `p_k` holds with an explicit exponent.

Stage 336 reduced rationalising Debreu's weight-`p_k` consumer on `S_ε` to finding `F, L` with

    F b − F a ≤ L a · b · (a − b (a b + √((1 − a²)(1 − b²))))   for a, b ∈ [ε, β].

Here we take, with `a = cos α`,

    L a = sin α cos α · e^{−K α},     F a = ∫₀^α (sin t cos t)² e^{−K t} dt,

and prove the inequality whenever `K σ ≥ 7`, where `σ > 0` bounds `sin 2α` from below on the
range (`σ² ≤ 4 a² (1 − a²)`). For the symmetric range `β² ≤ 1 − ε²` one may take
`σ = 2 ε √(1 − ε²)`, so `K = 7 / (2 ε √(1 − ε²))` works (e.g. `K ≈ 70` at `ε = 0.05`;
numerics suggest `K ≈ 20` is already enough, so this bound is not sharp).

Proof: in angle coordinates the inequality reads `G θ − G α ≤ ℓ(α) sin θ cos θ sin(θ − α)`.
For fixed `θ` the difference `φ(α)` vanishes at `α = θ`, and its derivative is
`e^{−Kα}/4 · (s_α² − s_θ (s_α cos d + (K s_α − 2 c_α) sin d))` with `d = θ − α`,
`s = sin 2·`, `c = cos 2·`. The sign of that bracket is settled by `core_pos` / `core_neg` using
only `|sin x − sin y| ≤ |x − y|`, `1 − d²/2 ≤ cos d`, `sin d ≥ 2d/π` and `π < 3.15`.
-/

noncomputable section

open Real Set

namespace WeightPkExplicit

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

end WeightPkExplicit

end

#print axioms WeightPkExplicit.g_continuous
#print axioms WeightPkExplicit.G_hasDerivAt
#print axioms WeightPkExplicit.core_pos
#print axioms WeightPkExplicit.core_neg
#print axioms WeightPkExplicit.phi_deriv
#print axioms WeightPkExplicit.phi_self
#print axioms WeightPkExplicit.scalar_angle
#print axioms WeightPkExplicit.sin_two_ge
#print axioms WeightPkExplicit.scalar_ab
#print axioms WeightPkExplicit.L_bounds
#print axioms WeightPkExplicit.sigma_symmetric
