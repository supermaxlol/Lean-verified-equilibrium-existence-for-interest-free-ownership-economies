import Mathlib

/-!
# Stage 385: existence of two-cycles in the money economy, from the slope at `m*`

Stage 384 found one explicit two-cycle (`γ = 3`, the path `1, 8, 1, 8, …`) but had no general
theorem. This file proves one. Definitions are copied from stage 384 (`MoneyDynamics.lean`, not
modified): `Av x = x (e1 − x) ^ (−γ)`, `Bv y = y (e2 + G y) ^ (−γ)`, `K = β G / (1 + μ)`, and a path
satisfies `Av (m t) = K · Bv (m (t+1))` with `0 < m t < e1`.

* `stat_unique` (any `γ > 0`): there is at most one stationary point `m*`.
* `Ai`, `hb`: the inverse of `Av` on `(0, e1)` and the backward map
  `hb y = Av⁻¹ (K · Bv y)`, defined for every `y > 0` and every `γ > 0`.
* `Ai_continuousAt`, `hb_continuousAt`: both are continuous (strict monotonicity + image
  a neighbourhood). `Ai_hasDeriv`: inverse-function derivative.
* `hb_hasDeriv`: the backward map is differentiable at `m*` with slope `D / N`, the reciprocal of
  the forward slope `N / D` of stage 384. This removes the stage-384 assumption that a
  differentiable local forward map exists: the backward map is constructed, not assumed.
* **`two_cycle_exists`**: if a stationary point `m*` exists and `N < −D` (backward slope below
  `−1`, i.e. forward slope in `(−1, 0)`), then there are `x ≠ y` with `m* < x < e1`,
  `0 < y < e1`, such that `x, y, x, y, …` is an equilibrium path. Proof: `φ(x) = hb (hb x) − x`
  has `φ(m*) = 0` and `φ'(m*) = (D / N)² − 1 > 0`, so `φ > 0` just right of `m*`; `φ(e1) < 0`
  because `hb` maps into `(0, e1)`; the intermediate value theorem gives a root `x`, and `x` is
  not stationary because `m*` is the only stationary point.
* `example_stat`, `example_flip`, `example_cycle`: the condition holds at
  `γ = 3, β = 343/32768, G = 1, μ = 0, e1 = 20, e2 = 5/16`, where `m* = 10/3`, `N = 8/5` and
  `−D = 61/35`.

Limits (honest):
* The condition `N < −D` is sufficient, not necessary; by stage 384 (`slope_flip_of_le_two`) it
  can only hold when `γ > 2`. When `D < 0` but `−D < N` (forward slope below `−1`), nothing is
  claimed about cycles.
* Existence only: no statement on the number of cycles, their stability, cycles of period
  above two, or sunspot equilibria.
* The theorem does not say the cycle found is the one of stage 384 (`1, 8`).
-/

open Set Filter Topology

namespace MoneyCycles

noncomputable section

/-- Young side of the forward map: `x (e1 − x) ^ (−γ)`. -/
def Av (γ e1 x : ℝ) : ℝ := x * (e1 - x) ^ (-γ)

/-- Old side of the forward map: `y (e2 + G y) ^ (−γ)`. -/
def Bv (γ G e2 y : ℝ) : ℝ := y * (e2 + G * y) ^ (-γ)

/-- The constant `β G / (1 + μ)`. -/
def Kc (β G μ : ℝ) : ℝ := β * G / (1 + μ)

/-- An equilibrium path of real balances. -/
def IsPath (γ β G μ e1 e2 : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ m t < e1 ∧ Av γ e1 (m t) = Kc β G μ * Bv γ G e2 (m (t + 1))

/-- A stationary point of the forward map. -/
def IsStat (γ β G μ e1 e2 ms : ℝ) : Prop :=
  0 < ms ∧ ms < e1 ∧ Av γ e1 ms = Kc β G μ * Bv γ G e2 ms

/-- Inflation factor between two dates with real balances `x` then `y`. -/
def infl (G μ x y : ℝ) : ℝ := (1 + μ) * x / (G * y)

/-- Derivative of `Av`. -/
def dAv (γ e1 x : ℝ) : ℝ := (e1 - x) ^ (-γ) + γ * x * (e1 - x) ^ (-γ - 1)

/-- Derivative of `Bv`. -/
def dBv (γ G e2 y : ℝ) : ℝ := (e2 + G * y) ^ (-γ) - γ * G * y * (e2 + G * y) ^ (-γ - 1)

/-- Numerator of the slope at the stationary point. -/
def Nn (γ e1 m : ℝ) : ℝ := 1 + γ * m / (e1 - m)

/-- Denominator of the slope at the stationary point. -/
def Dd (γ G e2 m : ℝ) : ℝ := 1 - γ * G * m / (e2 + G * m)


/-! ## Facts copied from stage 384 (`MoneyDynamics.lean`, not modified) -/

theorem small_delta (A M γ : ℝ) (hA : 0 < A) (hM : 0 ≤ M) (hγ : 0 < γ) :
    ∃ δ, 0 < δ ∧ δ ≤ A ∧ M < δ ^ (-γ) := by
  set t := (1 / (M + 1)) ^ γ⁻¹ with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min A t, lt_min hA ht0, min_le_left _ _, ?_⟩
  have hd0 : 0 < min A t := lt_min hA ht0
  have hp : 0 < min A t ^ γ := Real.rpow_pos_of_pos hd0 _
  have h1 : min A t ^ γ ≤ 1 / (M + 1) := by
    calc min A t ^ γ ≤ t ^ γ := Real.rpow_le_rpow hd0.le (min_le_right _ _) hγ.le
      _ = 1 / (M + 1) := Real.rpow_inv_rpow (by positivity) hγ.ne'
  rw [le_div_iff₀ (by linarith)] at h1
  rw [Real.rpow_neg hd0.le, ← one_div, lt_div_iff₀ hp]
  nlinarith

theorem Kc_pos (β G μ : ℝ) (hβ : 0 < β) (hG : 0 < G) (hμ : -1 < μ) : 0 < Kc β G μ := by
  unfold Kc
  exact div_pos (mul_pos hβ hG) (by linarith)

theorem Av_pos (γ e1 x : ℝ) (hx0 : 0 < x) (hx1 : x < e1) : 0 < Av γ e1 x :=
  mul_pos hx0 (Real.rpow_pos_of_pos (by linarith) _)

theorem Bv_pos (γ G e2 y : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hy : 0 < y) : 0 < Bv γ G e2 y :=
  mul_pos hy (Real.rpow_pos_of_pos (by have := mul_pos hG hy; linarith) _)

/-- **The young side is strictly increasing** on `(0, e1)`, for every `γ > 0`. -/
theorem Av_strictMono (γ e1 : ℝ) (hγ : 0 < γ) : StrictMonoOn (Av γ e1) (Ioo 0 e1) := by
  intro x hx x' hx' hxx
  have hP : (e1 - x) ^ (-γ) < (e1 - x') ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith [hx'.2]) (by linarith) (by linarith)
  unfold Av
  exact mul_lt_mul' hxx.le hP (Real.rpow_nonneg (by linarith [hx.2]) _) (by linarith [hx.1])

theorem stat_iff (γ β G μ e1 e2 ms : ℝ) :
    IsStat γ β G μ e1 e2 ms ↔
      0 < ms ∧ ms < e1 ∧ (e1 - ms) ^ (-γ) = Kc β G μ * (e2 + G * ms) ^ (-γ) := by
  constructor
  · intro hs
    obtain ⟨h0, h1, h⟩ := hs
    refine ⟨h0, h1, mul_left_cancel₀ h0.ne' ?_⟩
    unfold Av Bv at h
    rw [h]
    ring
  · intro hs
    obtain ⟨h0, h1, h⟩ := hs
    refine ⟨h0, h1, ?_⟩
    unfold Av Bv
    rw [h]
    ring

theorem sign_below (γ β G μ e1 e2 ms x : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hx0 : 0 < x) (hxs : x < ms) :
    Av γ e1 x < Kc β G μ * Bv γ G e2 x := by
  obtain ⟨h0, h1, h⟩ := (stat_iff γ β G μ e1 e2 ms).1 hs
  have ha : (e1 - x) ^ (-γ) < (e1 - ms) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  have hb : (e2 + G * ms) ^ (-γ) < (e2 + G * x) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by have := mul_pos hG hx0; linarith)
      (by have := mul_lt_mul_of_pos_left hxs hG; linarith) (by linarith)
  have hc : (e1 - x) ^ (-γ) < Kc β G μ * (e2 + G * x) ^ (-γ) := by
    rw [h] at ha
    exact ha.trans (mul_lt_mul_of_pos_left hb hK)
  unfold Av Bv
  calc x * (e1 - x) ^ (-γ) < x * (Kc β G μ * (e2 + G * x) ^ (-γ)) :=
        mul_lt_mul_of_pos_left hc hx0
    _ = Kc β G μ * (x * (e2 + G * x) ^ (-γ)) := by ring

theorem Av_hasDeriv (γ e1 x : ℝ) (hx1 : x < e1) : HasDerivAt (Av γ e1) (dAv γ e1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => e1 - y) (-1) x := (hasDerivAt_id' (x := x)).const_sub e1
  have h2 := h1.rpow_const (p := -γ) (Or.inl (sub_pos.2 hx1).ne')
  have h3 := (hasDerivAt_id' (x := x)).mul h2
  unfold dAv
  exact h3.congr_deriv (by ring)

theorem Bv_hasDeriv (γ G e2 y : ℝ) (hz : 0 < e2 + G * y) :
    HasDerivAt (Bv γ G e2) (dBv γ G e2 y) y := by
  have h1 : HasDerivAt (fun x : ℝ => e2 + G * x) (G * 1) y :=
    ((hasDerivAt_id' (x := y)).const_mul G).const_add e2
  have h2 := h1.rpow_const (p := -γ) (Or.inl hz.ne')
  have h3 := (hasDerivAt_id' (x := y)).mul h2
  unfold dBv
  exact h3.congr_deriv (by ring)

theorem dAv_eq (γ e1 m : ℝ) (h1 : m < e1) : dAv γ e1 m = (e1 - m) ^ (-γ) * Nn γ e1 m := by
  unfold dAv Nn
  rw [Real.rpow_sub_one (sub_pos.2 h1).ne']
  ring

theorem dBv_eq (γ G e2 m : ℝ) (hz : 0 < e2 + G * m) :
    dBv γ G e2 m = (e2 + G * m) ^ (-γ) * Dd γ G e2 m := by
  unfold dBv Dd
  rw [Real.rpow_sub_one hz.ne']
  ring

/-- **Slope formula** at the stationary point: `Av'(m*) / (K Bv'(m*)) = N / D`. -/
theorem Nn_gt_one (γ e1 m : ℝ) (hγ : 0 < γ) (h0 : 0 < m) (h1 : m < e1) : 1 < Nn γ e1 m := by
  unfold Nn
  have := div_pos (mul_pos hγ h0) (sub_pos.2 h1)
  linarith

/-- The young side maps `(0, e1)` onto `(0, ∞)` (any `γ > 0`). -/
theorem Av_surj (γ e1 c : ℝ) (hγ : 0 < γ) (he1 : 0 < e1) (hc : 0 < c) :
    ∃ x, 0 < x ∧ x < e1 ∧ Av γ e1 x = c := by
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta (e1 / 2) (2 * c / e1) γ (by linarith)
    (by positivity) hγ
  have hb0 : 0 ≤ e1 - δ := by linarith
  have hAv : c ≤ Av γ e1 (e1 - δ) := by
    unfold Av
    rw [sub_sub_cancel]
    rw [div_lt_iff₀ he1] at hδM
    have hp : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
    have := mul_le_mul_of_nonneg_right (by linarith : e1 / 2 ≤ e1 - δ) hp.le
    linarith
  have hcont : ContinuousOn (Av γ e1) (Icc 0 (e1 - δ)) := by
    show ContinuousOn (fun x => x * (e1 - x) ^ (-γ)) (Icc 0 (e1 - δ))
    exact (by fun_prop : ContinuousOn (fun x : ℝ => x) (Icc 0 (e1 - δ))).mul
      ((by fun_prop : ContinuousOn (fun x : ℝ => e1 - x) (Icc 0 (e1 - δ))).rpow_const
        fun x hx => Or.inl (ne_of_gt (by linarith [hx.2])))
  have hA0 : Av γ e1 0 = 0 := by
    unfold Av
    exact zero_mul _
  obtain ⟨x, hxI, hxc⟩ := intermediate_value_Icc hb0 hcont ⟨by rw [hA0]; exact hc.le, hAv⟩
  have hx0 : 0 < x := by
    rcases hxI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hA0] at hxc
      linarith
  exact ⟨x, hx0, by linarith [hxI.2], hxc⟩

/-- **The backward map is well defined** (any `γ > 0`): every `m (t+1) > 0` has exactly one
predecessor in `(0, e1)`. -/
theorem back_existsUnique (γ β G μ e1 e2 y : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he1 : 0 < e1)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hy : 0 < y) :
    ∃! x, (0 < x ∧ x < e1) ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y := by
  obtain ⟨x, hx0, hx1, hx⟩ :=
    Av_surj γ e1 _ hγ he1 (mul_pos hK (Bv_pos γ G e2 y hG he2 hy))
  refine ⟨x, ⟨⟨hx0, hx1⟩, hx⟩, fun x' hx' => ?_⟩
  exact (Av_strictMono γ e1 hγ).injOn (mem_Ioo.2 hx'.1) (mem_Ioo.2 ⟨hx0, hx1⟩)
    (hx'.2.trans hx.symm)

theorem rpow_neg_three (z : ℝ) (hz : 0 < z) : z ^ (-(3 : ℝ)) = (z ^ 3)⁻¹ := by
  rw [Real.rpow_neg hz.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]


/-! ## The stationary point is unique (sign above `m*`) -/

theorem sign_above (γ β G μ e1 e2 ms x : ℝ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hγ : 0 < γ) (hs : IsStat γ β G μ e1 e2 ms) (hxs : ms < x)
    (hx1 : x < e1) : Kc β G μ * Bv γ G e2 x < Av γ e1 x := by
  obtain ⟨h0, h1, h⟩ := (stat_iff γ β G μ e1 e2 ms).1 hs
  have hx0 : 0 < x := by linarith
  have ha : (e1 - ms) ^ (-γ) < (e1 - x) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  have hb : (e2 + G * x) ^ (-γ) < (e2 + G * ms) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by have := mul_pos hG h0; linarith)
      (by have := mul_lt_mul_of_pos_left hxs hG; linarith) (by linarith)
  have hc : Kc β G μ * (e2 + G * x) ^ (-γ) < (e1 - x) ^ (-γ) := by
    rw [h] at ha
    exact (mul_lt_mul_of_pos_left hb hK).trans ha
  unfold Av Bv
  calc Kc β G μ * (x * (e2 + G * x) ^ (-γ)) = x * (Kc β G μ * (e2 + G * x) ^ (-γ)) := by ring
    _ < x * (e1 - x) ^ (-γ) := mul_lt_mul_of_pos_left hc hx0

/-- **Uniqueness of the stationary point** (any `γ > 0`). -/
theorem stat_unique (γ β G μ e1 e2 ms ms' : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hs' : IsStat γ β G μ e1 e2 ms') :
    ms' = ms := by
  rcases lt_trichotomy ms' ms with h | h | h
  · have := sign_below γ β G μ e1 e2 ms ms' hγ hG he2 hK hs hs'.1 h
    linarith [hs'.2.2]
  · exact h
  · have := sign_above γ β G μ e1 e2 ms ms' hG he2 hK hγ hs h hs'.2.1
    linarith [hs'.2.2]

/-! ## The inverse of the young side and the backward map -/

/-- The inverse of `Av` on `(0, e1)`. -/
def Ai (γ e1 c : ℝ) : ℝ := Function.invFunOn (Av γ e1) (Ioo 0 e1) c

/-- **The backward map**: `hb y` is the unique `x ∈ (0, e1)` with `Av x = K · Bv y`. -/
def hb (γ β G μ e1 e2 y : ℝ) : ℝ := Ai γ e1 (Kc β G μ * Bv γ G e2 y)

theorem Ai_spec (γ e1 c : ℝ) (hγ : 0 < γ) (he1 : 0 < e1) (hc : 0 < c) :
    0 < Ai γ e1 c ∧ Ai γ e1 c < e1 ∧ Av γ e1 (Ai γ e1 c) = c := by
  obtain ⟨x, hx0, hx1, hx⟩ := Av_surj γ e1 c hγ he1 hc
  have h := Function.invFunOn_pos (f := Av γ e1) (s := Ioo 0 e1) (b := c)
    ⟨x, ⟨hx0, hx1⟩, hx⟩
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem Ai_Av (γ e1 x : ℝ) (hγ : 0 < γ) (hx0 : 0 < x) (hx1 : x < e1) :
    Ai γ e1 (Av γ e1 x) = x := by
  have he1 : 0 < e1 := by linarith
  obtain ⟨h0, h1, h⟩ := Ai_spec γ e1 _ hγ he1 (Av_pos γ e1 x hx0 hx1)
  exact (Av_strictMono γ e1 hγ).injOn (mem_Ioo.2 ⟨h0, h1⟩) (mem_Ioo.2 ⟨hx0, hx1⟩) h

theorem Ai_strictMono (γ e1 : ℝ) (hγ : 0 < γ) (he1 : 0 < e1) :
    StrictMonoOn (Ai γ e1) (Ioi 0) := by
  intro c hc c' hc' hcc
  obtain ⟨a0, a1, ha⟩ := Ai_spec γ e1 c hγ he1 hc
  obtain ⟨b0, b1, hb'⟩ := Ai_spec γ e1 c' hγ he1 hc'
  by_contra hle
  have := (Av_strictMono γ e1 hγ).monotoneOn (mem_Ioo.2 ⟨b0, b1⟩) (mem_Ioo.2 ⟨a0, a1⟩)
    (not_lt.1 hle)
  rw [ha, hb'] at this
  linarith

theorem Ai_continuousAt (γ e1 c : ℝ) (hγ : 0 < γ) (he1 : 0 < e1) (hc : 0 < c) :
    ContinuousAt (Ai γ e1) c := by
  apply (Ai_strictMono γ e1 hγ he1).continuousAt_of_image_mem_nhds (Ioi_mem_nhds hc)
  obtain ⟨h0, h1, _⟩ := Ai_spec γ e1 c hγ he1 hc
  apply Filter.mem_of_superset (Ioo_mem_nhds h0 h1)
  intro x hx
  exact ⟨Av γ e1 x, Av_pos γ e1 x hx.1 hx.2, Ai_Av γ e1 x hγ hx.1 hx.2⟩

theorem dAv_pos (γ e1 x : ℝ) (hγ : 0 < γ) (hx0 : 0 < x) (hx1 : x < e1) : 0 < dAv γ e1 x := by
  rw [dAv_eq γ e1 x hx1]
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (by linarith [Nn_gt_one γ e1 x hγ hx0 hx1])

theorem Ai_hasDeriv (γ e1 c : ℝ) (hγ : 0 < γ) (he1 : 0 < e1) (hc : 0 < c) :
    HasDerivAt (Ai γ e1) (dAv γ e1 (Ai γ e1 c))⁻¹ c := by
  obtain ⟨h0, h1, _⟩ := Ai_spec γ e1 c hγ he1 hc
  refine HasDerivAt.of_local_left_inverse (Ai_continuousAt γ e1 c hγ he1 hc)
    (Av_hasDeriv γ e1 _ h1) (dAv_pos γ e1 _ hγ h0 h1).ne' ?_
  filter_upwards [Ioi_mem_nhds hc] with y hy
  exact (Ai_spec γ e1 y hγ he1 hy).2.2

theorem Bv_continuousAt (γ G e2 y : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hy : 0 < y) :
    ContinuousAt (Bv γ G e2) y :=
  (Bv_hasDeriv γ G e2 y (by have := mul_pos hG hy; linarith)).continuousAt

section Back

variable (γ β G μ e1 e2 : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he1 : 0 < e1) (he2 : 0 < e2)
  (hK : 0 < Kc β G μ)

include hγ hG he1 he2 hK

theorem hb_spec (y : ℝ) (hy : 0 < y) :
    0 < hb γ β G μ e1 e2 y ∧ hb γ β G μ e1 e2 y < e1 ∧
      Av γ e1 (hb γ β G μ e1 e2 y) = Kc β G μ * Bv γ G e2 y :=
  Ai_spec γ e1 _ hγ he1 (mul_pos hK (Bv_pos γ G e2 y hG he2 hy))

theorem hb_continuousAt (y : ℝ) (hy : 0 < y) : ContinuousAt (hb γ β G μ e1 e2) y := by
  have hc : 0 < Kc β G μ * Bv γ G e2 y := mul_pos hK (Bv_pos γ G e2 y hG he2 hy)
  exact ContinuousAt.comp (f := fun y => Kc β G μ * Bv γ G e2 y)
    (Ai_continuousAt γ e1 _ hγ he1 hc) ((Bv_continuousAt γ G e2 y hG he2 hy).const_mul _)

omit hG he1 he2 hK in
theorem hb_stat (ms : ℝ) (hs : IsStat γ β G μ e1 e2 ms) : hb γ β G μ e1 e2 ms = ms := by
  obtain ⟨h0, h1, h⟩ := hs
  unfold hb
  rw [← h]
  exact Ai_Av γ e1 ms hγ h0 h1

/-- **Slope of the backward map** at `m*`: `D / N`, the reciprocal of the forward slope. -/
theorem hb_hasDeriv (ms : ℝ) (hs : IsStat γ β G μ e1 e2 ms) :
    HasDerivAt (hb γ β G μ e1 e2) (Dd γ G e2 ms / Nn γ e1 ms) ms := by
  obtain ⟨h0, h1, h⟩ := hs
  have hz : 0 < e2 + G * ms := by have := mul_pos hG h0; linarith
  have hc : 0 < Kc β G μ * Bv γ G e2 ms := mul_pos hK (Bv_pos γ G e2 ms hG he2 h0)
  have hA := Ai_hasDeriv γ e1 _ hγ he1 hc
  have hAi : Ai γ e1 (Kc β G μ * Bv γ G e2 ms) = ms := by
    rw [← h]
    exact Ai_Av γ e1 ms hγ h0 h1
  rw [hAi] at hA
  have hB : HasDerivAt (fun y => Kc β G μ * Bv γ G e2 y) (Kc β G μ * dBv γ G e2 ms) ms :=
    (Bv_hasDeriv γ G e2 ms hz).const_mul _
  have hcomp := hA.comp ms hB
  have hst := ((stat_iff γ β G μ e1 e2 ms).1 ⟨h0, h1, h⟩).2.2
  have hP : 0 < (e1 - ms) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _
  have hN : 0 < Nn γ e1 ms := by linarith [Nn_gt_one γ e1 ms hγ h0 h1]
  have hval : (dAv γ e1 ms)⁻¹ * (Kc β G μ * dBv γ G e2 ms) = Dd γ G e2 ms / Nn γ e1 ms := by
    rw [dAv_eq γ e1 ms h1, dBv_eq γ G e2 ms hz,
      show Kc β G μ * ((e2 + G * ms) ^ (-γ) * Dd γ G e2 ms)
        = (Kc β G μ * (e2 + G * ms) ^ (-γ)) * Dd γ G e2 ms by ring, ← hst]
    field_simp
  rw [← hval]
  exact hcomp

end Back

/-- A function with positive derivative at `a` and value `0` there is positive somewhere in
`(a, b)`. -/
theorem pos_right_of_deriv (f : ℝ → ℝ) (a f' b : ℝ) (hf : HasDerivAt f f' a) (hpos : 0 < f')
    (hfa : f a = 0) (hab : a < b) : ∃ x, a < x ∧ x < b ∧ 0 < f x := by
  have ht := hasDerivAt_iff_tendsto_slope.1 hf
  have ht' : Tendsto (slope f a) (𝓝[>] a) (𝓝 f') :=
    ht.mono_left (nhdsWithin_mono _ fun x hx => Set.mem_compl_singleton_iff.2 (ne_of_gt hx))
  have h1 : ∀ᶠ x in 𝓝[>] a, 0 < slope f a x := ht'.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ x in 𝓝[>] a, x < b := nhdsWithin_le_nhds (gt_mem_nhds hab)
  have h3 : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2, hx3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨x, hx3, hx2, ?_⟩
  rw [slope_def_field, hfa, sub_zero] at hx1
  exact (div_pos_iff_of_pos_right (sub_pos.2 hx3)).1 hx1

/-- **Existence of a two-cycle.** If the stationary point `m*` exists and
`N < −D` (equivalently, the backward map has slope `D / N < −1` at `m*`, i.e. the forward slope
lies in `(−1, 0)`), then there is an equilibrium path that alternates between two distinct
values `x ≠ y`, with `m* < x < e1`. Any `γ > 0`; the condition forces `γ > 2` (stage 384,
`slope_flip_of_le_two`). -/
theorem two_cycle_exists (γ β G μ e1 e2 ms : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he1 : 0 < e1)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hflip : Nn γ e1 ms < -Dd γ G e2 ms) :
    ∃ x y, ms < x ∧ x < e1 ∧ 0 < y ∧ y < e1 ∧ x ≠ y ∧
      IsPath γ β G μ e1 e2 (fun t => if t % 2 = 0 then x else y) := by
  have hm0 := hs.1
  have hm1 := hs.2.1
  have hN : 0 < Nn γ e1 ms := by linarith [Nn_gt_one γ e1 ms hγ hm0 hm1]
  have hlt : Dd γ G e2 ms / Nn γ e1 ms < -1 := by
    rw [div_lt_iff₀ hN]
    linarith
  have hsl : 0 < Dd γ G e2 ms / Nn γ e1 ms * (Dd γ G e2 ms / Nn γ e1 ms) - 1 := by nlinarith
  have hHpos : ∀ y, 0 < y → 0 < hb γ β G μ e1 e2 y ∧ hb γ β G μ e1 e2 y < e1 ∧
      Av γ e1 (hb γ β G μ e1 e2 y) = Kc β G μ * Bv γ G e2 y :=
    fun y hy => hb_spec γ β G μ e1 e2 hγ hG he1 he2 hK y hy
  have hHm := hb_stat γ β G μ e1 e2 hγ ms hs
  have hd := hb_hasDeriv γ β G μ e1 e2 hγ hG he1 he2 hK ms hs
  have hdd : HasDerivAt (fun x => hb γ β G μ e1 e2 (hb γ β G μ e1 e2 x) - x)
      (Dd γ G e2 ms / Nn γ e1 ms * (Dd γ G e2 ms / Nn γ e1 ms) - 1) ms := by
    have hd' : HasDerivAt (hb γ β G μ e1 e2) (Dd γ G e2 ms / Nn γ e1 ms)
        (hb γ β G μ e1 e2 ms) := by
      rw [hHm]
      exact hd
    exact (hd'.comp ms hd).sub (hasDerivAt_id ms)
  obtain ⟨x0, hx0a, hx0b, hx0pos⟩ := pos_right_of_deriv _ ms _ e1 hdd hsl
    (by simp only [hHm, sub_self]) hm1
  have hcont : ContinuousOn (fun x => hb γ β G μ e1 e2 (hb γ β G μ e1 e2 x) - x)
      (Icc x0 e1) := by
    intro x hx
    have hxp : 0 < x := by linarith [hx.1]
    apply ContinuousAt.continuousWithinAt
    exact ((hb_continuousAt γ β G μ e1 e2 hγ hG he1 he2 hK _ (hHpos x hxp).1).comp
      (hb_continuousAt γ β G μ e1 e2 hγ hG he1 he2 hK x hxp)).sub continuousAt_id
  have he : hb γ β G μ e1 e2 (hb γ β G μ e1 e2 e1) - e1 < 0 := by
    linarith [(hHpos _ (hHpos e1 he1).1).2.1]
  obtain ⟨x, hxI, hx⟩ := intermediate_value_Icc' (by linarith : x0 ≤ e1) hcont
    ⟨he.le, hx0pos.le⟩
  have hx' : hb γ β G μ e1 e2 (hb γ β G μ e1 e2 x) = x := sub_eq_zero.1 hx
  have hxe : x < e1 := by
    refine lt_of_le_of_ne hxI.2 fun h => ?_
    rw [h] at hx'
    linarith
  have hxm : ms < x := lt_of_lt_of_le hx0a hxI.1
  have hx0' : 0 < x := by linarith
  have hy := hHpos x hx0'
  have hyy := (hHpos _ hy.1).2.2
  rw [hx'] at hyy
  refine ⟨x, hb γ β G μ e1 e2 x, hxm, hxe, hy.1, hy.2.1, fun hxy => ?_, fun t => ?_⟩
  · have e := hy.2.2
    rw [← hxy] at e
    linarith [sign_above γ β G μ e1 e2 ms x hG he2 hK hγ hs hxm hxe]
  · by_cases ht : t % 2 = 0
    · have ht1 : ¬ (t + 1) % 2 = 0 := by omega
      simp only [ht, ht1, eq_self, ↓reduceIte]
      exact ⟨hx0', hxe, hyy⟩
    · have ht1 : (t + 1) % 2 = 0 := by omega
      simp only [ht, ht1, eq_self, ↓reduceIte]
      exact ⟨hy.1, hy.2.1, hy.2.2⟩

/-! ## The condition holds in an explicit economy -/

theorem example_stat : IsStat 3 (343 / 32768) 1 0 20 (5 / 16) (10 / 3) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold Av Bv Kc
  rw [rpow_neg_three (20 - 10 / 3) (by norm_num),
    rpow_neg_three (5 / 16 + 1 * (10 / 3)) (by norm_num)]
  norm_num

theorem example_flip : Nn 3 20 (10 / 3) < -Dd 3 1 (5 / 16) (10 / 3) := by
  unfold Nn Dd
  norm_num

/-- **The two-cycle theorem applies**: with `γ = 3`, `β = 343/32768`, `G = 1`, `μ = 0`,
`e1 = 20`, `e2 = 5/16`, the stationary point is `m* = 10/3`, `N = 8/5 < 61/35 = −D`, so a
two-cycle with one value in `(10/3, 20)` exists. -/
theorem example_cycle :
    ∃ x y, 10 / 3 < x ∧ x < 20 ∧ 0 < y ∧ y < 20 ∧ x ≠ y ∧
      IsPath 3 (343 / 32768) 1 0 20 (5 / 16) (fun t => if t % 2 = 0 then x else y) :=
  two_cycle_exists 3 (343 / 32768) 1 0 20 (5 / 16) (10 / 3) (by norm_num) one_pos
    (by norm_num) (by norm_num) (Kc_pos _ _ _ (by norm_num) one_pos (by norm_num))
    example_stat example_flip

end

end MoneyCycles

#print axioms MoneyCycles.stat_unique
#print axioms MoneyCycles.Ai_continuousAt
#print axioms MoneyCycles.Ai_hasDeriv
#print axioms MoneyCycles.hb_continuousAt
#print axioms MoneyCycles.hb_hasDeriv
#print axioms MoneyCycles.pos_right_of_deriv
#print axioms MoneyCycles.two_cycle_exists
#print axioms MoneyCycles.example_stat
#print axioms MoneyCycles.example_cycle
