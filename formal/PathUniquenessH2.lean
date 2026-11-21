import Mathlib

/-!
# Stage 387: uniqueness of the horizon-two equilibrium path for every γ > 0

Stage 383 (`PathUniquenessGS.lean`) proved path uniqueness for the stage 364 model only for
`0 < γ ≤ 1` (and, for larger `γ`, only between ordered paths). This file removes the
restriction on `γ` **at horizon `N = 2`**.

## What is proved

`unique_h2`: in the stage 364 model at horizon `N = 2` (definitions restated verbatim from
stage 364/383: `B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`), any two equilibria whose
returns `Q 0, Q 1` are positive have the same returns and the same wealth distributions at
dates 0, 1, 2. Assumptions: `γ > 0`, `b ≥ 0`, `x0 ≥ 0`, `g ≥ 0`, `amp g σ ≥ 0`,
`g σ c ≥ 0`. No ordering of the two paths and no band on `γ` is assumed.

## How

* In log returns `X = log Q0`, `Y = log Q1` the date-0 clearing condition is `Φ(X, Y) = 1`,
  with `Φ` strictly increasing in `X` (`1 + E·n > 0` for `E = (1-γ)/γ > -1`). Every `Y` has a
  clearing `X` (`curve_exists`, intermediate value theorem), giving a curve `X = p(Y)`.
* `curve_deriv`: `p` is differentiable with slope `-Φ_Y/Φ_X`, via Mathlib's bivariate
  implicit function theorem; the global curve agrees with the local implicit function by
  strict monotonicity.
* `slope_pos`: the date-1 clearing residual `e^Y Σ α_h (amp·w_h + gσc)` has positive
  derivative along the curve. The core is an algebraic inequality in the weighted moments
  `S1, S2, M, P, R2`, proved separately for `E ≥ 0` and `-1 < E < 0`.
* `resid_strictMono` then gives at most one `Y`, hence one `X`, hence one path.

## Limits (stated honestly)

* Horizon two only. Longer horizons (`N ≥ 3`) for `γ > 1` remain open here: the reduction
  to one unknown along a clearing curve does not carry over directly.
* Uniqueness only. Existence at `N = 2` is not proved in this file.
* Positive returns are assumed of both equilibria (`Q t > 0`), as in stage 383.
* Same model as stage 364: one good, log-linear savings rule `F`, the `T` transition.
  Nothing here is about the general multi-good economy.
* The monotonicity was first found by numerical exploration; the Lean proof does not
  depend on that search.
-/

noncomputable section

open Finset Filter Topology

namespace PathUniquenessH2

variable {H : Type*} [Fintype H]

/-! ## Stage 364 definitions, restated unchanged -/

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def amp (g σ : ℝ) : ℝ := 1 + g * (1 - σ)

def T (g σ c : ℝ) (s x : H → ℝ) (h : H) : ℝ :=
  (amp g σ * (s h * x h / B s x) + g * σ * c) / (1 + g)

def F (b : ℝ) (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k + 1, t => b * r t * (1 + F b r k (t + 1))

def ex (γ : ℝ) : ℝ := (1 - γ) / γ

def rr (γ : ℝ) (Q : ℕ → ℝ) (t : ℕ) : ℝ := Q t ^ ex γ

def savN (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (t : ℕ) (h : H) : ℝ :=
  F (b h) (rr γ Q) (N - t) t / (1 + F (b h) (rr γ Q) (N - t) t)

def IsEqN (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t < N, x (t + 1) = T g σ c (savN γ b N Q t) (x t) ∧
    Q t = 1 / B (savN γ b N Q t) (x t)

/-! ## The horizon-two system in log returns

`X = log Q 0`, `Y = log Q 1`, `E = ex γ`. -/

def aa (b : H → ℝ) (E Y : ℝ) (h : H) : ℝ := b h * Real.exp (E * Y)

def zz (b : H → ℝ) (E X Y : ℝ) (h : H) : ℝ := b h * (1 + aa b E Y h) * Real.exp (E * X)

def nn (b : H → ℝ) (E X Y : ℝ) (h : H) : ℝ := 1 / (1 + zz b E X Y h)

def al (b : H → ℝ) (E Y : ℝ) (h : H) : ℝ := aa b E Y h / (1 + aa b E Y h)

def wt (b x0 : H → ℝ) (E X Y : ℝ) (h : H) : ℝ :=
  x0 h * Real.exp X * (zz b E X Y h / (1 + zz b E X Y h))

def Phi (b x0 : H → ℝ) (E X Y : ℝ) : ℝ := ∑ h, wt b x0 E X Y h

section basic

variable (b x0 : H → ℝ) (E : ℝ) (h : H)

omit [Fintype H] in
theorem aa_nonneg (Y : ℝ) (hb : 0 ≤ b h) : 0 ≤ aa b E Y h :=
  mul_nonneg hb (Real.exp_pos _).le

omit [Fintype H] in
theorem zz_nonneg (X Y : ℝ) (hb : 0 ≤ b h) : 0 ≤ zz b E X Y h :=
  mul_nonneg (mul_nonneg hb (by linarith [aa_nonneg b E h Y hb])) (Real.exp_pos _).le

omit [Fintype H] in
theorem nn_nonneg (X Y : ℝ) (hb : 0 ≤ b h) : 0 ≤ nn b E X Y h :=
  div_nonneg zero_le_one (by linarith [zz_nonneg b E h X Y hb])

omit [Fintype H] in
theorem nn_le_one (X Y : ℝ) (hb : 0 ≤ b h) : nn b E X Y h ≤ 1 := by
  have := zz_nonneg b E h X Y hb
  unfold nn
  rw [div_le_one (by linarith)]
  linarith

omit [Fintype H] in
theorem al_nonneg (Y : ℝ) (hb : 0 ≤ b h) : 0 ≤ al b E Y h :=
  div_nonneg (aa_nonneg b E h Y hb) (by linarith [aa_nonneg b E h Y hb])

omit [Fintype H] in
theorem al_le_one (Y : ℝ) (hb : 0 ≤ b h) : al b E Y h ≤ 1 := by
  have := aa_nonneg b E h Y hb
  unfold al
  rw [div_le_one (by linarith)]
  linarith

omit [Fintype H] in
theorem al_pos (Y : ℝ) (hb : 0 < b h) : 0 < al b E Y h :=
  div_pos (mul_pos hb (Real.exp_pos _)) (by linarith [aa_nonneg b E h Y hb.le])

omit [Fintype H] in
theorem wt_nonneg (X Y : ℝ) (hb : 0 ≤ b h) (hx : 0 ≤ x0 h) : 0 ≤ wt b x0 E X Y h :=
  mul_nonneg (mul_nonneg hx (Real.exp_pos _).le)
    (div_nonneg (zz_nonneg b E h X Y hb) (by linarith [zz_nonneg b E h X Y hb]))

omit [Fintype H] in
theorem wt_pos (X Y : ℝ) (hb : 0 < b h) (hx : 0 < x0 h) : 0 < wt b x0 E X Y h := by
  have hz : 0 < zz b E X Y h :=
    mul_pos (mul_pos hb (by linarith [aa_nonneg b E h Y hb.le])) (Real.exp_pos _)
  exact mul_pos (mul_pos hx (Real.exp_pos _)) (div_pos hz (by linarith))

omit [Fintype H] in
theorem wt_le (X Y : ℝ) (hb : 0 ≤ b h) (hx : 0 ≤ x0 h) : wt b x0 E X Y h ≤ x0 h * Real.exp X := by
  have hz := zz_nonneg b E h X Y hb
  have h1 : zz b E X Y h / (1 + zz b E X Y h) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h0 : 0 ≤ x0 h * Real.exp X := mul_nonneg hx (Real.exp_pos _).le
  unfold wt
  nlinarith

end basic

theorem one_add_mul_pos (E n : ℝ) (hE : -1 < E) (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 < 1 + E * n := by
  rcases le_or_gt 0 E with h | h
  · nlinarith [mul_nonneg h hn0]
  · nlinarith [mul_nonneg (neg_nonneg.2 h.le) (sub_nonneg.2 hn1)]

/-! ## Derivatives along a path `t ↦ (fx t, fy t)` -/

section deriv

variable (b x0 : H → ℝ) (E : ℝ) (h : H)

omit [Fintype H] in
theorem aa_deriv (fy : ℝ → ℝ) (ky t : ℝ) (hy : HasDerivAt fy ky t) :
    HasDerivAt (fun t => aa b E (fy t) h) (aa b E (fy t) h * (E * ky)) t := by
  have := ((hy.const_mul E).exp).const_mul (b h)
  unfold aa
  convert this using 1
  ring

omit [Fintype H] in
theorem al_deriv (fy : ℝ → ℝ) (ky t : ℝ) (hy : HasDerivAt fy ky t) (hb : 0 ≤ b h) :
    HasDerivAt (fun t => al b E (fy t) h)
      (ky * E * al b E (fy t) h * (1 - al b E (fy t) h)) t := by
  have ha := aa_deriv b E h fy ky t hy
  have hpos : 0 < 1 + aa b E (fy t) h := by linarith [aa_nonneg b E h (fy t) hb]
  have hne := hpos.ne'
  have := ha.div ((hasDerivAt_const t (1 : ℝ)).add ha) hne
  unfold al
  convert this using 1
  simp only [Pi.add_apply]
  field_simp
  ring

omit [Fintype H] in
theorem zz_deriv (fx fy : ℝ → ℝ) (kx ky t : ℝ) (hx : HasDerivAt fx kx t)
    (hy : HasDerivAt fy ky t) (hb : 0 ≤ b h) :
    HasDerivAt (fun t => zz b E (fx t) (fy t) h)
      (zz b E (fx t) (fy t) h * (E * kx + E * ky * al b E (fy t) h)) t := by
  have ha := aa_deriv b E h fy ky t hy
  have he := (hx.const_mul E).exp
  have := ((hasDerivAt_const t (b h)).mul ((hasDerivAt_const t (1 : ℝ)).add ha)).mul he
  have hpos : 0 < 1 + aa b E (fy t) h := by linarith [aa_nonneg b E h (fy t) hb]
  have hne := hpos.ne'
  unfold zz al
  convert this using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  field_simp
  ring

omit [Fintype H] in
theorem wt_deriv (fx fy : ℝ → ℝ) (kx ky t : ℝ) (hx : HasDerivAt fx kx t)
    (hy : HasDerivAt fy ky t) (hb : 0 ≤ b h) :
    HasDerivAt (fun t => wt b x0 E (fx t) (fy t) h)
      (wt b x0 E (fx t) (fy t) h * (kx * (1 + E * nn b E (fx t) (fy t) h) +
        ky * (E * nn b E (fx t) (fy t) h * al b E (fy t) h))) t := by
  have hz := zz_deriv b E h fx fy kx ky t hx hy hb
  have hzpos : 0 < 1 + zz b E (fx t) (fy t) h := by linarith [zz_nonneg b E h (fx t) (fy t) hb]
  have hne := hzpos.ne'
  have := ((hasDerivAt_const t (x0 h)).mul hx.exp).mul
    (hz.div ((hasDerivAt_const t (1 : ℝ)).add hz) hne)
  unfold wt nn
  convert this using 1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply]
  field_simp
  ring

end deriv

section partials

variable (b x0 : H → ℝ) (E : ℝ)

theorem Phi_dX (hb : ∀ h, 0 ≤ b h) (X Y : ℝ) :
    HasDerivAt (fun X => Phi b x0 E X Y)
      (∑ h, wt b x0 E X Y h * (1 + E * nn b E X Y h)) X := by
  have := HasDerivAt.sum (u := Finset.univ) (x := X) fun h _ =>
    wt_deriv b x0 E h (fun t => t) (fun _ => Y) 1 0 X (hasDerivAt_id' X)
      (hasDerivAt_const X Y) (hb h)
  unfold Phi
  convert this using 1
  · ext X'
    simp
  · simp

theorem Phi_dY (hb : ∀ h, 0 ≤ b h) (X Y : ℝ) :
    HasDerivAt (fun Y => Phi b x0 E X Y)
      (∑ h, wt b x0 E X Y h * (E * nn b E X Y h * al b E Y h)) Y := by
  have := HasDerivAt.sum (u := Finset.univ) (x := Y) fun h _ =>
    wt_deriv b x0 E h (fun _ => X) (fun t => t) 0 1 Y (hasDerivAt_const Y X)
      (hasDerivAt_id' Y) (hb h)
  unfold Phi
  convert this using 1
  · ext Y'
    simp
  · simp

omit [Fintype H] in
theorem cont_zz (h : H) (_hb : 0 ≤ b h) : Continuous fun v : ℝ × ℝ => zz b E v.2 v.1 h := by
  unfold zz aa
  fun_prop

omit [Fintype H] in
theorem cont_nn (h : H) (hb : 0 ≤ b h) : Continuous fun v : ℝ × ℝ => nn b E v.2 v.1 h := by
  unfold nn
  exact continuous_const.div (continuous_const.add (cont_zz b E h hb))
    fun v => ne_of_gt (by linarith [zz_nonneg b E h v.2 v.1 hb])

omit [Fintype H] in
theorem cont_al (h : H) (hb : 0 ≤ b h) : Continuous fun v : ℝ × ℝ => al b E v.1 h := by
  have ca : Continuous fun v : ℝ × ℝ => aa b E v.1 h := by unfold aa; fun_prop
  unfold al
  exact ca.div (continuous_const.add ca) fun v => ne_of_gt (by linarith [aa_nonneg b E h v.1 hb])

omit [Fintype H] in
theorem cont_wt (h : H) (hb : 0 ≤ b h) : Continuous fun v : ℝ × ℝ => wt b x0 E v.2 v.1 h := by
  unfold wt
  exact (continuous_const.mul (Real.continuous_exp.comp continuous_snd)).mul
    ((cont_zz b E h hb).div (continuous_const.add (cont_zz b E h hb))
      fun v => ne_of_gt (by linarith [zz_nonneg b E h v.2 v.1 hb]))

end partials

/-! ## The date-0 clearing curve -/

section curve

variable (b x0 : H → ℝ) (E : ℝ)

/-- The date-0 clearing curve `X = p Y` has slope `−Φ_Y / Φ_X` (implicit function theorem). -/
theorem curve_deriv (hb : ∀ h, 0 ≤ b h) (p : ℝ → ℝ) (hp : ∀ Y, Phi b x0 E (p Y) Y = 1)
    (hmono : ∀ Y, StrictMono fun X => Phi b x0 E X Y) (Y0 : ℝ)
    (hD : 0 < ∑ h, wt b x0 E (p Y0) Y0 h * (1 + E * nn b E (p Y0) Y0 h)) :
    HasDerivAt p (-((∑ h, wt b x0 E (p Y0) Y0 h * (E * nn b E (p Y0) Y0 h * al b E Y0 h)) /
      ∑ h, wt b x0 E (p Y0) Y0 h * (1 + E * nn b E (p Y0) Y0 h))) Y0 := by
  have toF : ∀ (g : ℝ → ℝ) (d x : ℝ), HasDerivAt g d x →
      HasFDerivAt g (d • ContinuousLinearMap.id ℝ ℝ) x := fun g d x hg => by
    have := hg.hasFDerivAt
    convert this using 1
    ext
    simp
  let f : ℝ → ℝ → ℝ := fun Y X => Phi b x0 E X Y
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun Y X =>
    (∑ h, wt b x0 E X Y h * (E * nn b E X Y h * al b E Y h)) • ContinuousLinearMap.id ℝ ℝ
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun Y X =>
    (∑ h, wt b x0 E X Y h * (1 + E * nn b E X Y h)) • ContinuousLinearMap.id ℝ ℝ
  have df₁ : ∀ᶠ v in 𝓝 (Y0, p Y0), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 :=
    Eventually.of_forall fun v => toF _ _ _ (Phi_dY b x0 E hb v.2 v.1)
  have df₂ : ∀ᶠ v in 𝓝 (Y0, p Y0), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 :=
    Eventually.of_forall fun v => toF _ _ _ (Phi_dX b x0 E hb v.2 v.1)
  have cD1 : Continuous fun v : ℝ × ℝ =>
      ∑ h, wt b x0 E v.2 v.1 h * (E * nn b E v.2 v.1 h * al b E v.1 h) :=
    continuous_finsetSum _ fun h _ => (cont_wt b x0 E h (hb h)).mul
      ((continuous_const.mul (cont_nn b E h (hb h))).mul (cont_al b E h (hb h)))
  have cD2 : Continuous fun v : ℝ × ℝ =>
      ∑ h, wt b x0 E v.2 v.1 h * (1 + E * nn b E v.2 v.1 h) :=
    continuous_finsetSum _ fun h _ => (cont_wt b x0 E h (hb h)).mul
      (continuous_const.add (continuous_const.mul (cont_nn b E h (hb h))))
  have cf₁ : ContinuousAt (Function.uncurry f₁) (Y0, p Y0) :=
    (cD1.smul continuous_const).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry f₂) (Y0, p Y0) :=
    (cD2.smul continuous_const).continuousAt
  have e2 : f₂ (Y0, p Y0).1 (Y0, p Y0).2 =
      ((ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hD.ne') : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) := by
    ext
    simp [f₂]
  have hinv : (f₂ (Y0, p Y0).1 (Y0, p Y0).2).IsInvertible := ⟨_, e2.symm⟩
  have hψ := hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  have hev := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  have heq : p =ᶠ[𝓝 Y0] implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv := by
    refine hev.mono fun Y hY => ?_
    refine (hmono Y).injective ?_
    simp only [f] at hY
    show Phi b x0 E (p Y) Y = Phi b x0 E _ Y
    rw [hY, hp Y, hp Y0]
  refine (hψ.hasFDerivAt.hasDerivAt.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [e2, ContinuousLinearMap.inverse_equiv]
  simp [f₁]
  field_simp
  exact Finset.sum_congr rfl fun h _ => by ring

omit [Fintype H] in
/-- A lower bound for one household's date-0 wealth at `X ≥ 0`. -/
theorem wt_lower (h : H) (_hE : -1 < E) (hb : 0 < b h) (X Y : ℝ) (hX : 0 ≤ X) :
    b h * Real.exp (min 1 (1 + E) * X) ≤
      (1 + b h) * (Real.exp X * (zz b E X Y h / (1 + zz b E X Y h))) := by
  set z := zz b E X Y h with hz_def
  set β := b h * Real.exp (E * X) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg hb.le (Real.exp_pos _).le
  have hzβ : β ≤ z := by
    have h1 : 1 ≤ 1 + aa b E Y h := by linarith [aa_nonneg b E h Y hb.le]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hb.le)
      (Real.exp_pos (E * X)).le
    simp only [hz_def, zz, hβ]
    linarith
  set t := z / (1 + z) with ht
  have hz0 : 0 ≤ z := le_trans hβ0 hzβ
  have ht0 : 0 ≤ t := div_nonneg hz0 (by linarith)
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by linarith)]; linarith
  have htβ : β ≤ (1 + β) * t := by
    rw [ht, ← mul_div_assoc, le_div_iff₀ (by linarith)]
    nlinarith
  have hexp : 0 < Real.exp X := Real.exp_pos X
  rcases le_or_gt 0 E with hE0 | hE0
  · have hmu : Real.exp (min 1 (1 + E) * X) ≤ Real.exp X :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left 1 (1 + E)])
    have hbβ : b h ≤ β := by
      have : 1 ≤ Real.exp (E * X) := Real.one_le_exp (mul_nonneg hE0 hX)
      simp only [hβ]
      nlinarith
    have h2 : b h ≤ (1 + b h) * t := by nlinarith [mul_nonneg (sub_nonneg.2 hbβ) (sub_nonneg.2 ht1)]
    calc b h * Real.exp (min 1 (1 + E) * X) ≤ b h * Real.exp X :=
          mul_le_mul_of_nonneg_left hmu hb.le
      _ ≤ (1 + b h) * t * Real.exp X := mul_le_mul_of_nonneg_right h2 hexp.le
      _ = (1 + b h) * (Real.exp X * t) := by ring
  · have hmu : min 1 (1 + E) = 1 + E := min_eq_right (by linarith)
    have hβb : β ≤ b h := by
      have : Real.exp (E * X) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [hβ]
      nlinarith
    have h2 : β ≤ (1 + b h) * t := by nlinarith
    have e : b h * Real.exp (min 1 (1 + E) * X) = Real.exp X * β := by
      rw [hmu, hβ, add_mul, one_mul, Real.exp_add]
      ring
    rw [e]
    calc Real.exp X * β ≤ Real.exp X * ((1 + b h) * t) := mul_le_mul_of_nonneg_left h2 hexp.le
      _ = (1 + b h) * (Real.exp X * t) := by ring

/-- Every `Y` has a date-0 clearing `X`. -/
theorem curve_exists (hb : ∀ h, 0 ≤ b h) (hx : ∀ h, 0 ≤ x0 h) (hE : -1 < E) (k : H)
    (hbk : 0 < b k) (hxk : 0 < x0 k) (Y : ℝ) : ∃ X, Phi b x0 E X Y = 1 := by
  have hcont : Continuous fun X => Phi b x0 E X Y :=
    continuous_iff_continuousAt.2 fun X => (Phi_dX b x0 E hb X Y).continuousAt
  set S0 := ∑ h, x0 h with hS0
  have hS0p : 0 < S0 := lt_of_lt_of_le hxk
    (Finset.single_le_sum (f := x0) (fun h _ => hx h) (Finset.mem_univ k))
  set Xlo := -Real.log (S0 + 1) with hXlo
  have hlo : Phi b x0 E Xlo Y ≤ 1 := by
    have h1 : Phi b x0 E Xlo Y ≤ ∑ h, x0 h * Real.exp Xlo :=
      Finset.sum_le_sum fun h _ => wt_le b x0 E h Xlo Y (hb h) (hx h)
    rw [← Finset.sum_mul, hXlo, Real.exp_neg, Real.exp_log (by linarith)] at h1
    have h2 : S0 * (S0 + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]
      linarith
    linarith
  set μ := min 1 (1 + E) with hμ
  have hμp : 0 < μ := lt_min one_pos (by linarith)
  set L := Real.log ((1 + b k) / (b k * x0 k)) with hL
  set Xhi := max 0 (L / μ) with hXhi
  have hXhi0 : 0 ≤ Xhi := le_max_left _ _
  have hhi : 1 ≤ Phi b x0 E Xhi Y := by
    have h1 : wt b x0 E Xhi Y k ≤ Phi b x0 E Xhi Y :=
      Finset.single_le_sum (f := fun h => wt b x0 E Xhi Y h)
        (fun h _ => wt_nonneg b x0 E h Xhi Y (hb h) (hx h)) (Finset.mem_univ k)
    have h2 := wt_lower b E k hE hbk Xhi Y hXhi0
    have h3 : L ≤ μ * Xhi := by
      have : L / μ ≤ Xhi := le_max_right _ _
      rw [div_le_iff₀ hμp] at this
      linarith
    have h4 : (1 + b k) / (b k * x0 k) ≤ Real.exp (μ * Xhi) := by
      rw [← Real.exp_log (div_pos (by linarith) (mul_pos hbk hxk))]
      exact Real.exp_le_exp.2 h3
    have h5 : (1 + b k) ≤ b k * x0 k * Real.exp (μ * Xhi) := by
      rw [div_le_iff₀ (mul_pos hbk hxk)] at h4
      linarith
    have hw : wt b x0 E Xhi Y k =
        x0 k * (Real.exp Xhi * (zz b E Xhi Y k / (1 + zz b E Xhi Y k))) := by
      unfold wt
      ring
    have h6 : (1 + b k) ≤ (1 + b k) * wt b x0 E Xhi Y k := by
      rw [hw]
      nlinarith [mul_le_mul_of_nonneg_left h2 hxk.le]
    have h7 : 1 ≤ wt b x0 E Xhi Y k := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    linarith
  obtain ⟨X, -, hX⟩ := intermediate_value_uIcc (a := Xlo) (b := Xhi) hcont.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hlo, hhi⟩))
  exact ⟨X, hX⟩

end curve

/-! ## The slope inequality -/

/-- **Slope inequality.** For weights `w ≥ 0` summing to one, `0 ≤ n, a ≤ 1`, `E > −1` and
`∑ w a > 0`, the slope of the date-1 clearing residual along the date-0 clearing curve (per
unit of the amplified term) is positive. -/
theorem slope_pos (w n a : H → ℝ) (E : ℝ) (hE : -1 < E) (hw : ∀ h, 0 ≤ w h)
    (hw1 : ∑ h, w h = 1) (hn0 : ∀ h, 0 ≤ n h) (hn1 : ∀ h, n h ≤ 1) (ha0 : ∀ h, 0 ≤ a h)
    (ha1 : ∀ h, a h ≤ 1) (hS : 0 < ∑ h, w h * a h) :
    0 < ∑ h, w h * a h + E * ∑ h, w h * a h * (1 - a h) +
      -(∑ h, w h * (E * n h * a h)) / (∑ h, w h * (1 + E * n h)) *
        ∑ h, w h * a h * (1 + E * n h) + E * ∑ h, w h * n h * a h ^ 2 := by
  set S1 := ∑ h, w h * a h with hS1
  set S2 := ∑ h, w h * a h ^ 2 with hS2
  set M := ∑ h, w h * n h with hM
  set P := ∑ h, w h * n h * a h with hP
  set R2 := ∑ h, w h * n h * a h ^ 2 with hR2
  have e1 : ∑ h, w h * a h * (1 - a h) = S1 - S2 := by
    rw [hS1, hS2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e2 : ∑ h, w h * (E * n h * a h) = E * P := by
    rw [hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e3 : ∑ h, w h * (1 + E * n h) = ∑ h, w h + E * M := by
    rw [hM, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hw1] at e3
  have e4 : ∑ h, w h * a h * (1 + E * n h) = S1 + E * P := by
    rw [hS1, hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun h _ => mul_nonneg (hw h) (hn0 h)
  have hM1 : M ≤ 1 := by
    rw [← hw1]
    exact Finset.sum_le_sum fun h _ => mul_le_of_le_one_right (hw h) (hn1 h)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun h _ => mul_nonneg (mul_nonneg (hw h) (hn0 h)) (ha0 h)
  have hPM : P ≤ M := Finset.sum_le_sum fun h _ =>
    mul_le_of_le_one_right (mul_nonneg (hw h) (hn0 h)) (ha1 h)
  have hPS : P ≤ S1 := Finset.sum_le_sum fun h _ => by
    nlinarith [mul_nonneg (mul_nonneg (hw h) (ha0 h)) (sub_nonneg.2 (hn1 h))]
  have hS1le : S1 ≤ 1 := by
    rw [← hw1]
    exact Finset.sum_le_sum fun h _ => mul_le_of_le_one_right (hw h) (ha1 h)
  have hD0 : 0 ≤ S2 - R2 := by
    rw [hS2, hR2, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun h _ => by
      nlinarith [mul_nonneg (mul_nonneg (hw h) (sq_nonneg (a h))) (sub_nonneg.2 (hn1 h))]
  have hD1 : S2 - R2 ≤ S1 - P := by
    rw [hS2, hR2, hS1, hP, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun h _ => by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (hw h) (ha0 h)) (sub_nonneg.2 (hn1 h)))
        (sub_nonneg.2 (ha1 h))]
  rw [e1, e2, e3, e4]
  have hden : 0 < 1 + E * M := one_add_mul_pos E M hE hM0 hM1
  set D := S2 - R2 with hD
  set N := (1 + E * M) * ((1 + E) * S1 - E * D) - E * P * S1 - E ^ 2 * P ^ 2 with hN
  have eq : S1 + E * (S1 - S2) + -(E * P) / (1 + E * M) * (S1 + E * P) + E * R2 =
      N / (1 + E * M) := by
    rw [hN, hD]
    field_simp
    ring
  rw [eq]
  refine div_pos ?_ hden
  rcases le_or_gt 0 E with hE0 | hE0
  · nlinarith [mul_nonneg (mul_nonneg hE0 hP0) (sub_nonneg.2 hS1le),
      mul_nonneg (mul_nonneg hE0 hM0) hS.le,
      mul_nonneg (mul_nonneg (sq_nonneg E) hP0) (sub_nonneg.2 hPM),
      mul_nonneg (mul_nonneg hE0 hden.le) (sub_nonneg.2 hD1)]
  · have hSP : 0 ≤ S1 + E * P := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ E + 1) hP0]
    nlinarith [mul_pos hden (mul_pos (by linarith : (0:ℝ) < 1 + E) hS),
      mul_nonneg (mul_nonneg (neg_nonneg.2 hE0.le) hD0) hden.le,
      mul_nonneg (mul_nonneg (neg_nonneg.2 hE0.le) hP0) hSP]

/-! ## The date-1 residual is strictly increasing along the curve -/

section mono

variable (b x0 : H → ℝ) (E : ℝ)

theorem resid_strictMono (hb : ∀ h, 0 ≤ b h) (hx : ∀ h, 0 ≤ x0 h) (hE : -1 < E) (k : H)
    (hbk : 0 < b k) (hxk : 0 < x0 k) (A m : ℝ) (hA : 0 ≤ A) (hm : 0 ≤ m) (hAm : 0 < A ∨ 0 < m)
    (p : ℝ → ℝ) (hp : ∀ Y, Phi b x0 E (p Y) Y = 1)
    (hmono : ∀ Y, StrictMono fun X => Phi b x0 E X Y) :
    StrictMono fun Y => Real.exp Y * ∑ h, al b E Y h * (A * wt b x0 E (p Y) Y h + m) := by
  refine strictMono_of_deriv_pos fun Y => ?_
  set w := fun h => wt b x0 E (p Y) Y h with hw
  set n := fun h => nn b E (p Y) Y h with hn
  set a := fun h => al b E Y h with ha
  have hD : 0 < ∑ h, wt b x0 E (p Y) Y h * (1 + E * nn b E (p Y) Y h) :=
    Finset.sum_pos' (fun h _ => mul_nonneg (wt_nonneg b x0 E h _ _ (hb h) (hx h))
        (one_add_mul_pos E _ hE (nn_nonneg b E h _ _ (hb h)) (nn_le_one b E h _ _ (hb h))).le)
      ⟨k, Finset.mem_univ _, mul_pos (wt_pos b x0 E k _ _ hbk hxk)
        (one_add_mul_pos E _ hE (nn_nonneg b E k _ _ hbk.le) (nn_le_one b E k _ _ hbk.le))⟩
  set κ := -((∑ h, wt b x0 E (p Y) Y h * (E * nn b E (p Y) Y h * al b E Y h)) /
      ∑ h, wt b x0 E (p Y) Y h * (1 + E * nn b E (p Y) Y h)) with hκ
  have hpd : HasDerivAt p κ Y := curve_deriv b x0 E hb p hp hmono Y hD
  have hterm : ∀ h ∈ (Finset.univ : Finset H), HasDerivAt
      (fun Y => al b E Y h * (A * wt b x0 E (p Y) Y h + m))
      ((1 * E * al b E Y h * (1 - al b E Y h)) * (A * wt b x0 E (p Y) Y h + m) +
        al b E Y h * (A * (wt b x0 E (p Y) Y h * (κ * (1 + E * nn b E (p Y) Y h) +
          1 * (E * nn b E (p Y) Y h * al b E Y h))))) Y := fun h _ => by
    have h1 := al_deriv b E h (fun t => t) 1 Y (hasDerivAt_id' Y) (hb h)
    have h2 := wt_deriv b x0 E h p (fun t => t) κ 1 Y hpd (hasDerivAt_id' Y) (hb h)
    exact h1.mul ((h2.const_mul A).add_const m)
  have hsum := HasDerivAt.sum hterm
  have hfull := (Real.hasDerivAt_exp Y).mul hsum
  have hfe : (fun Y => Real.exp Y * ∑ h, al b E Y h * (A * wt b x0 E (p Y) Y h + m)) =
      (Real.exp * ∑ h ∈ Finset.univ, fun Y => al b E Y h * (A * wt b x0 E (p Y) Y h + m)) := by
    ext Y'
    simp
  rw [hfe, hfull.deriv]
  simp only [Finset.sum_apply]
  have hw1 : ∑ h, w h = 1 := hp Y
  have hS : 0 < ∑ h, w h * a h :=
    Finset.sum_pos' (fun h _ => mul_nonneg (wt_nonneg b x0 E h _ _ (hb h) (hx h))
        (al_nonneg b E h Y (hb h)))
      ⟨k, Finset.mem_univ _, mul_pos (wt_pos b x0 E k _ _ hbk hxk) (al_pos b E k Y hbk)⟩
  have hkey := slope_pos w n a E hE (fun h => wt_nonneg b x0 E h _ _ (hb h) (hx h)) hw1
    (fun h => nn_nonneg b E h _ _ (hb h)) (fun h => nn_le_one b E h _ _ (hb h))
    (fun h => al_nonneg b E h Y (hb h)) (fun h => al_le_one b E h Y (hb h)) hS
  have hmpos : 0 < ∑ h, a h * (1 + E * (1 - a h)) :=
    Finset.sum_pos' (fun h _ => mul_nonneg (al_nonneg b E h Y (hb h))
        (one_add_mul_pos E _ hE (sub_nonneg.2 (al_le_one b E h Y (hb h)))
          (by linarith [al_nonneg b E h Y (hb h)])).le)
      ⟨k, Finset.mem_univ _, mul_pos (al_pos b E k Y hbk)
        (one_add_mul_pos E _ hE (sub_nonneg.2 (al_le_one b E k Y hbk.le))
          (by linarith [al_nonneg b E k Y hbk.le]))⟩
  have hsplit : ∑ h, al b E Y h * (A * wt b x0 E (p Y) Y h + m) +
      ∑ h, ((1 * E * al b E Y h * (1 - al b E Y h)) * (A * wt b x0 E (p Y) Y h + m) +
        al b E Y h * (A * (wt b x0 E (p Y) Y h * (κ * (1 + E * nn b E (p Y) Y h) +
          1 * (E * nn b E (p Y) Y h * al b E Y h))))) =
      m * ∑ h, a h * (1 + E * (1 - a h)) +
        A * (∑ h, w h * a h + E * ∑ h, w h * a h * (1 - a h) +
          -(∑ h, w h * (E * n h * a h)) / (∑ h, w h * (1 + E * n h)) *
            ∑ h, w h * a h * (1 + E * n h) + E * ∑ h, w h * n h * a h ^ 2) := by
    have hκ' : κ = -(∑ h, w h * (E * n h * a h)) / (∑ h, w h * (1 + E * n h)) := by
      rw [hκ, neg_div]
    rw [← hκ']
    simp only [hw, hn, ha, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hpos : 0 < m * ∑ h, a h * (1 + E * (1 - a h)) +
      A * (∑ h, w h * a h + E * ∑ h, w h * a h * (1 - a h) +
        -(∑ h, w h * (E * n h * a h)) / (∑ h, w h * (1 + E * n h)) *
          ∑ h, w h * a h * (1 + E * n h) + E * ∑ h, w h * n h * a h ^ 2) := by
    rcases hAm with hA' | hm'
    · nlinarith [mul_nonneg hm hmpos.le, mul_pos hA' hkey]
    · nlinarith [mul_pos hm' hmpos, mul_nonneg hA hkey.le]
  rw [← mul_add, hsplit]
  exact mul_pos (Real.exp_pos Y) hpos

end mono

/-! ## Back to the stage 364 model at horizon two -/

theorem F_one (bb : ℝ) (r : ℕ → ℝ) : F bb r 1 1 = bb * r 1 * (1 + 0) := rfl

theorem F_two (bb : ℝ) (r : ℕ → ℝ) : F bb r 2 0 = bb * r 0 * (1 + bb * r 1 * (1 + 0)) := rfl

theorem rr_eq (γ : ℝ) (Q : ℕ → ℝ) (t : ℕ) (hQ : 0 < Q t) :
    rr γ Q t = Real.exp (ex γ * Real.log (Q t)) := by
  unfold rr
  rw [Real.rpow_def_of_pos hQ, mul_comm]

omit [Fintype H] in
theorem sav_one (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (h : H) (hQ1 : 0 < Q 1) :
    savN γ b 2 Q 1 h = al b (ex γ) (Real.log (Q 1)) h := by
  unfold savN al aa
  rw [show (2 : ℕ) - 1 = 1 from rfl, F_one, rr_eq γ Q 1 hQ1]
  simp only [add_zero, mul_one]

omit [Fintype H] in
theorem sav_zero (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (h : H) (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) :
    savN γ b 2 Q 0 h = zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h /
      (1 + zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h) := by
  unfold savN
  rw [show (2 : ℕ) - 0 = 2 from rfl, F_two, rr_eq γ Q 0 hQ0, rr_eq γ Q 1 hQ1]
  have e : b h * Real.exp (ex γ * Real.log (Q 0)) *
      (1 + b h * Real.exp (ex γ * Real.log (Q 1)) * (1 + 0)) =
      zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h := by
    unfold zz aa
    ring
  rw [e]

/-- What a horizon-two equilibrium with positive returns says in the reduced variables. -/
theorem eq_facts (g σ c γ : ℝ) (b x0 : H → ℝ) (hg : 0 ≤ g) (x : ℕ → H → ℝ) (Q : ℕ → ℝ)
    (he : IsEqN g σ c γ b x0 2 x Q) (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) :
    Phi b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) = 1 ∧
    (∀ h, x 1 h = (amp g σ * wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h + g * σ * c) /
      (1 + g)) ∧
    Real.exp (Real.log (Q 1)) * ∑ h, al b (ex γ) (Real.log (Q 1)) h *
      (amp g σ * wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h + g * σ * c) = 1 + g ∧
    x 2 = T g σ c (fun h => al b (ex γ) (Real.log (Q 1)) h) (x 1) := by
  obtain ⟨hx0, hall⟩ := he
  obtain ⟨hx1, hq0⟩ := hall 0 (by norm_num)
  obtain ⟨hx2, hq1⟩ := hall 1 (by norm_num)
  have hs0 : savN γ b 2 Q 0 = fun h => zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h /
      (1 + zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h) :=
    funext fun h => sav_zero γ b Q h hQ0 hQ1
  have hs1 : savN γ b 2 Q 1 = fun h => al b (ex γ) (Real.log (Q 1)) h :=
    funext fun h => sav_one γ b Q h hQ1
  rw [hx0, hs0] at hx1 hq0
  rw [hs1] at hx2 hq1
  set s0 := fun h => zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h /
      (1 + zz b (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h) with hs0d
  have hB0 : B s0 x0 ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hq0
    linarith
  have hB0' : B s0 x0 = 1 / Q 0 := by
    rw [hq0]
    field_simp
  have hwt : ∀ h, wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h = s0 h * x0 h / B s0 x0 := by
    intro h
    rw [hB0']
    unfold wt
    rw [Real.exp_log hQ0, hs0d]
    field_simp
  have hx1' : ∀ h, x 1 h = (amp g σ * wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) h +
      g * σ * c) / (1 + g) := by
    intro h
    rw [hx1, hwt]
    rfl
  refine ⟨?_, hx1', ?_, hx2⟩
  · unfold Phi
    simp only [hwt]
    rw [← Finset.sum_div]
    exact div_self hB0
  · have hB1 : B (fun h => al b (ex γ) (Real.log (Q 1)) h) (x 1) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hq1
      linarith
    have hQB := hq1
    rw [eq_div_iff hB1] at hQB
    rw [Real.exp_log hQ1]
    unfold B at hQB
    simp only [hx1'] at hQB
    have hg1 : (0 : ℝ) < 1 + g := by linarith
    have e : ∑ k, al b (ex γ) (Real.log (Q 1)) k * ((amp g σ *
        wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) k + g * σ * c) / (1 + g)) =
        (∑ k, al b (ex γ) (Real.log (Q 1)) k * (amp g σ *
          wt b x0 (ex γ) (Real.log (Q 0)) (Real.log (Q 1)) k + g * σ * c)) / (1 + g) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [e, mul_div_assoc', div_eq_one_iff_eq hg1.ne'] at hQB
    exact hQB

/-- **Uniqueness at horizon two for every `γ > 0`.** Two equilibria of the stage 364 model at
horizon `N = 2` whose returns are positive have the same returns and the same distributions at
every date. No band on `γ`, no ordering of the two paths, and no restriction to `γ ≤ 1` is
assumed. -/
theorem unique_h2 (g σ c γ : ℝ) (b x0 : H → ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 ≤ b h)
    (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hamp : 0 ≤ amp g σ) (hgsc : 0 ≤ g * σ * c)
    (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (he : IsEqN g σ c γ b x0 2 x Q) (he' : IsEqN g σ c γ b x0 2 x' Q')
    (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) (hQ0' : 0 < Q' 0) (hQ1' : 0 < Q' 1) :
    Q 0 = Q' 0 ∧ Q 1 = Q' 1 ∧ x 0 = x' 0 ∧ x 1 = x' 1 ∧ x 2 = x' 2 := by
  obtain ⟨hP, hx1, hQe, hx2⟩ := eq_facts g σ c γ b x0 hg x Q he hQ0 hQ1
  obtain ⟨hP', hx1', hQe', hx2'⟩ := eq_facts g σ c γ b x0 hg x' Q' he' hQ0' hQ1'
  set E := ex γ with hE_def
  have hE : -1 < E := by
    rw [hE_def, ex, lt_div_iff₀ hγ]
    linarith
  -- a household with positive wealth and positive patience
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show Phi b x0 E (Real.log (Q 0)) (Real.log (Q 1)) ≠ 0 by rw [hP]; norm_num)
  have hxk : 0 < x0 k := lt_of_le_of_ne (hx0 k) fun h0 => hk (by simp [wt, ← h0])
  have hbk : 0 < b k := lt_of_le_of_ne (hb k) fun h0 => hk (by simp [wt, zz, ← h0])
  have hmono : ∀ Y, StrictMono fun X => Phi b x0 E X Y := fun Y =>
    strictMono_of_deriv_pos fun X => by
      rw [(Phi_dX b x0 E hb X Y).deriv]
      exact Finset.sum_pos' (fun h _ => mul_nonneg (wt_nonneg b x0 E h _ _ (hb h) (hx0 h))
          (one_add_mul_pos E _ hE (nn_nonneg b E h _ _ (hb h)) (nn_le_one b E h _ _ (hb h))).le)
        ⟨k, Finset.mem_univ _, mul_pos (wt_pos b x0 E k _ _ hbk hxk)
          (one_add_mul_pos E _ hE (nn_nonneg b E k _ _ hbk.le) (nn_le_one b E k _ _ hbk.le))⟩
  choose p hp using fun Y => curve_exists b x0 E hb hx0 hE k hbk hxk Y
  have hX : Real.log (Q 0) = p (Real.log (Q 1)) :=
    (hmono _).injective (by rw [hP, hp])
  have hX' : Real.log (Q' 0) = p (Real.log (Q' 1)) :=
    (hmono _).injective (by rw [hP', hp])
  have hAm : 0 < amp g σ ∨ 0 < g * σ * c := by
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    have hA0 : amp g σ = 0 := le_antisymm hc.1 hamp
    have hm0 : g * σ * c = 0 := le_antisymm hc.2 hgsc
    rw [hA0, hm0] at hQe
    simp at hQe
    linarith
  have hsm := resid_strictMono b x0 E hb hx0 hE k hbk hxk (amp g σ) (g * σ * c) hamp hgsc hAm
    p hp hmono
  rw [hX] at hQe
  rw [hX'] at hQe'
  have hY : Real.log (Q 1) = Real.log (Q' 1) :=
    hsm.injective (by rw [hQe, hQe'])
  have hQ1eq : Q 1 = Q' 1 := by
    rw [← Real.exp_log hQ1, ← Real.exp_log hQ1', hY]
  have hQ0eq : Q 0 = Q' 0 := by
    rw [← Real.exp_log hQ0, ← Real.exp_log hQ0', hX, hX', hY]
  have hx1eq : x 1 = x' 1 := funext fun h => by
    rw [hx1 h, hx1' h, hQ0eq, hQ1eq]
  refine ⟨hQ0eq, hQ1eq, by rw [he.1, he'.1], hx1eq, ?_⟩
  rw [hx2, hx2', hx1eq, hQ1eq]

end PathUniquenessH2

#print axioms PathUniquenessH2.slope_pos
#print axioms PathUniquenessH2.curve_deriv
#print axioms PathUniquenessH2.curve_exists
#print axioms PathUniquenessH2.resid_strictMono
#print axioms PathUniquenessH2.eq_facts
#print axioms PathUniquenessH2.unique_h2
