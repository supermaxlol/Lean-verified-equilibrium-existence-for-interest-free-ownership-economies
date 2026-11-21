import Mathlib

/-!
# Stage 384: local dynamics, inflation along collapsing paths, and the case `γ > 1`

This file continues stage 381 (`MoneyTransition`) for the overlapping-generations economy with
money growing at rate `μ > −1`. The definitions are copied from stage 381 so the file is
self-contained. Notation:

* young side `Av x = x (e1 − x) ^ (−γ)`, old side `Bv y = y (e2 + G y) ^ (−γ)`;
* `K = β G / (1 + μ)` (`Kc`); the forward map is `Av (m t) = K · Bv (m (t+1))`;
* inflation between two dates `infl x y = (1 + μ) x / (G y)` (the reciprocal of the gross
  return on money of stage 381); the stationary inflation factor is `(1 + μ) / G`.

## What is proved

**1. Existence of the next step.**
* `Bv_unbounded` (`γ < 1`): `Bv` takes arbitrarily large values.
* `fwd_existsUnique` (`γ < 1`): every `m t ∈ (0, e1)` has exactly one successor `m (t+1) > 0`;
  `fwd_function`: so the forward map is a genuine function on `(0, e1)`.
* `fwd_exists_one` (`γ = 1`): `Bv` is bounded by `1 / G`, and a successor exists iff
  `Av (m t) < K / G`; `fwd_exists_one_iff` restates this as `m t (1 + μ + β) < β e1`.

**2. Local instability of the stationary point `m*`.**
* `Av_hasDeriv`, `Bv_hasDeriv`: explicit derivatives (`HasDerivAt`) `dAv`, `dBv`.
* `Av_strictMono`: `Av` is strictly increasing on `(0, e1)` for every `γ > 0`.
* `slope_eq`: at `m*`, `Av'(m*) / (K Bv'(m*)) = N / D` with
  `N = 1 + γ m* / (e1 − m*)` (`Nn`) and `D = 1 − γ G m* / (e2 + G m*)` (`Dd`).
* `fwd_slope`: if `f` is any forward map near `m*` (i.e. `Av x = K Bv (f x)` for `x` near `m*`)
  with `f m* = m*` and `f` differentiable at `m*`, then `f'(m*) = N / D`.
* `slope_gt_one`: `D > 0 ⇒ N / D > 1`; `Dd_pos_of_le_one`: `D > 0` whenever `γ ≤ 1`;
  `fwd_slope_gt_one`: hence for `γ ≤ 1` the forward slope at `m*` exceeds `1`.
* `Dd_neg_iff`: `D < 0 ⇔ e2 + G m* < γ G m*` (only possible for `γ > 1`, `one_lt_of_Dd_neg`);
  `slope_neg`, `fwd_slope_neg`: then the slope is negative.
* `slope_flip_iff`: when `D < 0`, the slope is `< −1` iff `−D < N`, i.e.
  `γ G m* / (e2 + G m*) < 2 + γ m* / (e1 − m*)`; `slope_flip_of_le_two`: this always holds when
  `γ ≤ 2`. So a slope in `(−1, 0)` (a stable oscillatory forward map) requires `γ > 2`.

**3. Inflation along collapsing paths.**
* `infl_path`: along any path, `infl (m t) (m (t+1)) = β (e2 + G m (t+1)) ^ (−γ) / (e1 − m t) ^ (−γ)`.
* `infl_strictMono`: along any strictly decreasing path, inflation is strictly increasing.
* `infl_limit`: along any path converging to `0`, inflation converges to `β (e1 / e2) ^ γ`
  (the autarky marginal rate of substitution). NOTE: this is the correct limit; the conjectured
  formula `(1 + μ) / G · (e1 / e2) ^ γ / β` proposed in an earlier draft is not right.
* `infl_limit_gt`: if a stationary point exists, `(1 + μ) / G < β (e1 / e2) ^ γ`.
* `antitone_path_zero` (any `γ > 0`): a monotonically decreasing path starting below `m*` goes to `0`.
* `infl_below` (`γ ≤ 1`, `m 0 < m*`): inflation is strictly increasing, converges to
  `β (e1 / e2) ^ γ`, and this limit is strictly above the stationary inflation `(1 + μ) / G`.
  Both the monotone statement and the limit are proved.

**4. The case `γ > 1`.**
* `Av_surj`, `back_existsUnique` (any `γ > 0`): every `m (t+1) > 0` has exactly one
  predecessor `m t ∈ (0, e1)`; the backward map is well defined.
* `Bv_two_example`, `fwd_multivalued` (`γ = 2`, `G = e2 = 1`): `Bv (1/2) = Bv 2`, so for any
  `β, μ, e1` there is `m t ∈ (0, e1)` with two distinct successors `1/2` and `2`.
* `cycle_path`: an explicit **two-cycle equilibrium path**: with `γ = 3`, `β = 343/32768`,
  `G = 1`, `μ = 0`, `e1 = 20`, `e2 = 5/16`, the sequence `1, 8, 1, 8, …` is an equilibrium
  path. It is neither stationary nor convergent.

## Limits

* No general existence theorem for two-cycles: the flip argument (backward map `h`, slope of
  `h ∘ h` above `1` at `m*`, boundary behaviour, intermediate values) is not formalised. Only
  the explicit numerical example `cycle_path` is proved.
* `fwd_slope` assumes a differentiable local forward map through `m*`; its existence (an implicit
  function argument) is not proved. The slope formula, its sign, and the flip condition are
  proved as statements about `N / D`.
* No statement here on whether parameters with `D < 0` and a stationary point actually exist,
  other than `Dd_neg_iff`; no sunspot equilibria; no welfare comparisons.
* Monotonicity of inflation is proved along strictly decreasing paths; for `γ > 1` it is not
  shown which paths are decreasing.
-/

open Set Filter Topology

namespace MoneyDynamics

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

/-- The two-cycle `1, 8, 1, 8, …`. -/
def cyc (t : ℕ) : ℝ := if t % 2 = 0 then 1 else 8

/-! ## Basic facts (copied from stage 381) -/

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

theorem Bv_zero (γ G e2 : ℝ) : Bv γ G e2 0 = 0 := by
  unfold Bv
  exact zero_mul _

theorem Bv_split (γ G e2 x : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hx : 0 < x) :
    Bv γ G e2 x = x ^ (1 - γ) * (x / (e2 + G * x)) ^ γ := by
  have hzx : 0 < e2 + G * x := by have := mul_pos hG hx; linarith
  have h1 : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
  have h2 : 0 < (e2 + G * x) ^ γ := Real.rpow_pos_of_pos hzx γ
  unfold Bv
  rw [Real.div_rpow hx.le hzx.le, Real.rpow_neg hzx.le, Real.rpow_sub hx, Real.rpow_one]
  field_simp

theorem Bv_strictMono (γ G e2 : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G) (he2 : 0 < e2) :
    StrictMonoOn (Bv γ G e2) (Ioi 0) := by
  intro y hy y' hy' hyy
  rw [mem_Ioi] at hy hy'
  have hz : 0 < e2 + G * y := by have := mul_pos hG hy; linarith
  have hz' : 0 < e2 + G * y' := by have := mul_pos hG hy'; linarith
  rw [Bv_split γ G e2 y hG he2 hy, Bv_split γ G e2 y' hG he2 hy']
  have h1 : y ^ (1 - γ) ≤ y' ^ (1 - γ) := Real.rpow_le_rpow hy.le hyy.le (by linarith)
  have h2 : (y / (e2 + G * y)) ^ γ < (y' / (e2 + G * y')) ^ γ := by
    apply Real.rpow_lt_rpow (div_pos hy hz).le _ hγ
    rw [div_lt_div_iff₀ hz hz']
    nlinarith
  exact mul_lt_mul' h1 h2 (Real.rpow_nonneg (div_pos hy hz).le _) (Real.rpow_pos_of_pos hy' _)

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

theorem next_unique (γ β G μ e1 e2 x y y' : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hy : 0 < y) (hy' : 0 < y')
    (h : Av γ e1 x = Kc β G μ * Bv γ G e2 y) (h' : Av γ e1 x = Kc β G μ * Bv γ G e2 y') :
    y = y' :=
  (Bv_strictMono γ G e2 hγ hγ1 hG he2).injOn (mem_Ioi.2 hy) (mem_Ioi.2 hy')
    (mul_left_cancel₀ hK.ne' (h.symm.trans h'))

theorem next_exists (γ β G μ e1 e2 x Y : ℝ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hx0 : 0 < x) (hx1 : x < e1) (hY : 0 < Y)
    (hle : Av γ e1 x ≤ Kc β G μ * Bv γ G e2 Y) :
    ∃ y, 0 < y ∧ y ≤ Y ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y := by
  have hKne : Kc β G μ ≠ 0 := hK.ne'
  have hA := Av_pos γ e1 x hx0 hx1
  have hc0 : 0 < Av γ e1 x / Kc β G μ := div_pos hA hK
  have hcY : Av γ e1 x / Kc β G μ ≤ Bv γ G e2 Y := by
    rw [div_le_iff₀ hK]
    linarith
  have hcont : ContinuousOn (Bv γ G e2) (Icc 0 Y) := by
    show ContinuousOn (fun y => y * (e2 + G * y) ^ (-γ)) (Icc 0 Y)
    exact (by fun_prop : ContinuousOn (fun y : ℝ => y) (Icc 0 Y)).mul
      ((by fun_prop : ContinuousOn (fun y : ℝ => e2 + G * y) (Icc 0 Y)).rpow_const
        fun y hy => Or.inl (ne_of_gt (by have := mul_nonneg hG.le hy.1; linarith)))
  obtain ⟨y, hyI, hyc⟩ :=
    intermediate_value_Icc hY.le hcont ⟨by rw [Bv_zero]; exact hc0.le, hcY⟩
  have hy0 : 0 < y := by
    rcases hyI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, Bv_zero] at hyc
      linarith
  refine ⟨y, hy0, hyI.2, ?_⟩
  rw [hyc]
  field_simp

theorem step_down (γ β G μ e1 e2 ms x y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hx0 : 0 < x)
    (hxs : x < ms) (hy : 0 < y) (h : Av γ e1 x = Kc β G μ * Bv γ G e2 y) : y < x := by
  by_contra hc
  push Not at hc
  have hB := (Bv_strictMono γ G e2 hγ hγ1 hG he2).monotoneOn (mem_Ioi.2 hx0) (mem_Ioi.2 hy) hc
  have h1 := sign_below γ β G μ e1 e2 ms x hγ hG he2 hK hs hx0 hxs
  have h2 := mul_le_mul_of_nonneg_left hB hK.le
  linarith

/-- A limit of an equilibrium path inside `(0, e1)` is a stationary point. -/
theorem limit_stat (γ β G μ e1 e2 L : ℝ) (m : ℕ → ℝ) (hG : 0 < G) (he2 : 0 < e2)
    (hp : IsPath γ β G μ e1 e2 m) (hL : Tendsto m atTop (𝓝 L)) (hL0 : 0 < L) (hL1 : L < e1) :
    Av γ e1 L = Kc β G μ * Bv γ G e2 L := by
  have hA : ContinuousAt (Av γ e1) L := by
    show ContinuousAt (fun x => x * (e1 - x) ^ (-γ)) L
    exact (by fun_prop : ContinuousAt (fun x : ℝ => x) L).mul
      ((by fun_prop : ContinuousAt (fun x : ℝ => e1 - x) L).rpow_const
        (Or.inl (sub_pos.2 hL1).ne'))
  have hB : ContinuousAt (Bv γ G e2) L := by
    show ContinuousAt (fun y => y * (e2 + G * y) ^ (-γ)) L
    exact (by fun_prop : ContinuousAt (fun y : ℝ => y) L).mul
      ((by fun_prop : ContinuousAt (fun y : ℝ => e2 + G * y) L).rpow_const
        (Or.inl (by have := mul_pos hG hL0; linarith : (0 : ℝ) < e2 + G * L).ne'))
  have h1 : Tendsto (fun t => Av γ e1 (m t)) atTop (𝓝 (Av γ e1 L)) := hA.tendsto.comp hL
  have h2 : Tendsto (fun t => Kc β G μ * Bv γ G e2 (m (t + 1))) atTop
      (𝓝 (Kc β G μ * Bv γ G e2 L)) :=
    ((hB.tendsto.comp hL).comp (tendsto_add_atTop_nat 1)).const_mul _
  have h3 : Tendsto (fun t => Kc β G μ * Bv γ G e2 (m (t + 1))) atTop (𝓝 (Av γ e1 L)) :=
    h1.congr fun t => (hp t).2.2
  exact tendsto_nhds_unique h3 h2

/-- **Any `γ > 0`**: a monotonically decreasing path starting below `m*` converges to `0`. -/
theorem antitone_path_zero (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hp : IsPath γ β G μ e1 e2 m) (hanti : Antitone m) (h0 : m 0 < ms) :
    Tendsto m atTop (𝓝 0) := by
  have hbdd : BddBelow (range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hp t).1.le⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  have hL0 : 0 ≤ ⨅ t, m t := le_ciInf fun t => (hp t).1.le
  rcases hL0.lt_or_eq with hpos | heq
  · exfalso
    have hle : (⨅ t, m t) ≤ m 0 := ciInf_le hbdd 0
    have h1 := (hp 0).2.1
    have hst := limit_stat γ β G μ e1 e2 _ m hG he2 hp hL hpos (by linarith)
    exact absurd hst (ne_of_lt (sign_below γ β G μ e1 e2 ms _ hγ hG he2 hK hs hpos
      (by linarith)))
  · rw [← heq] at hL
    exact hL

/-- Stage 381 phase portrait below `m*` (`γ ≤ 1`). -/
theorem path_below (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hp : IsPath γ β G μ e1 e2 m) (h0 : m 0 < ms) :
    StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hlt : ∀ t, m t < ms := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      exact (step_down γ β G μ e1 e2 ms (m n) (m (n + 1)) hγ hγ1 hG he2 hK hs (hp n).1 ih
        (hp (n + 1)).1 (hp n).2.2).trans ih
  have hanti : StrictAnti m := strictAnti_nat_of_succ_lt fun n =>
    step_down γ β G μ e1 e2 ms (m n) (m (n + 1)) hγ hγ1 hG he2 hK hs (hp n).1 (hlt n)
      (hp (n + 1)).1 (hp n).2.2
  exact ⟨hanti, antitone_path_zero γ β G μ e1 e2 ms m hγ hG he2 hK hs hp hanti.antitone h0⟩

/-! ## 1. Existence of the next step -/

/-- **`γ < 1`: the old side is unbounded.** -/
theorem Bv_unbounded (γ G e2 M : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hG : 0 < G) (he2 : 0 < e2) :
    ∃ Y, 0 < Y ∧ M ≤ Bv γ G e2 Y := by
  have hc0 : 0 < (1 / (2 * G)) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hev : ∀ᶠ y : ℝ in atTop,
      M / (1 / (2 * G)) ^ γ ≤ y ^ (1 - γ) ∧ e2 / G ≤ y ∧ 0 < y :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - γ)).eventually
      (eventually_ge_atTop _)).and ((eventually_ge_atTop _).and (eventually_gt_atTop 0))
  obtain ⟨y, h1, h2, h3⟩ := hev.exists
  refine ⟨y, h3, ?_⟩
  have hz : 0 < e2 + G * y := by have := mul_pos hG h3; linarith
  have hq : 1 / (2 * G) ≤ y / (e2 + G * y) := by
    rw [div_le_div_iff₀ (by positivity) hz]
    rw [div_le_iff₀ hG] at h2
    linarith
  have hq' : (1 / (2 * G)) ^ γ ≤ (y / (e2 + G * y)) ^ γ :=
    Real.rpow_le_rpow (by positivity) hq hγ.le
  rw [div_le_iff₀ hc0] at h1
  rw [Bv_split γ G e2 y hG he2 h3]
  calc M ≤ y ^ (1 - γ) * (1 / (2 * G)) ^ γ := h1
    _ ≤ y ^ (1 - γ) * (y / (e2 + G * y)) ^ γ :=
      mul_le_mul_of_nonneg_left hq' (Real.rpow_nonneg h3.le _)

/-- **`γ < 1`: every date-`t` balance has exactly one successor.** -/
theorem fwd_existsUnique (γ β G μ e1 e2 x : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hx0 : 0 < x) (hx1 : x < e1) :
    ∃! y, 0 < y ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y := by
  obtain ⟨Y, hY, hM⟩ := Bv_unbounded γ G e2 (Av γ e1 x / Kc β G μ) hγ hγ1 hG he2
  rw [div_le_iff₀ hK] at hM
  obtain ⟨y, hy, _, hyx⟩ :=
    next_exists γ β G μ e1 e2 x Y hG he2 hK hx0 hx1 hY (by linarith)
  exact ⟨y, ⟨hy, hyx⟩, fun y' hy' =>
    next_unique γ β G μ e1 e2 x y' y hγ hγ1.le hG he2 hK hy'.1 hy hy'.2 hyx⟩

/-- **`γ < 1`: the forward map is a function on `(0, e1)`.** -/
theorem fwd_function (γ β G μ e1 e2 : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) :
    ∃ f : ℝ → ℝ, ∀ x ∈ Ioo 0 e1, 0 < f x ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 (f x) ∧
      ∀ y, 0 < y → Av γ e1 x = Kc β G μ * Bv γ G e2 y → y = f x := by
  have h : ∀ x : ℝ, ∃ y : ℝ, x ∈ Ioo 0 e1 → 0 < y ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y := by
    intro x
    by_cases hx : x ∈ Ioo 0 e1
    · obtain ⟨y, hy, _⟩ := fwd_existsUnique γ β G μ e1 e2 x hγ hγ1 hG he2 hK hx.1 hx.2
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h
  refine ⟨f, fun x hx => ⟨(hf x hx).1, (hf x hx).2, fun y hy hyx => ?_⟩⟩
  exact next_unique γ β G μ e1 e2 x y (f x) hγ hγ1.le hG he2 hK hy (hf x hx).1 hyx (hf x hx).2

theorem Bv_one (G e2 y : ℝ) (hz : 0 < e2 + G * y) : Bv 1 G e2 y = y / (e2 + G * y) := by
  unfold Bv
  rw [Real.rpow_neg hz.le, Real.rpow_one, div_eq_mul_inv]

theorem Av_one (e1 x : ℝ) (hx1 : x < e1) : Av 1 e1 x = x / (e1 - x) := by
  unfold Av
  rw [Real.rpow_neg (sub_pos.2 hx1).le, Real.rpow_one, div_eq_mul_inv]

theorem one_solve (A K G e2 y : ℝ) (he2 : 0 < e2) (hG : 0 < G) (hy : 0 < y)
    (hyd : y * (K - G * A) = A * e2) : A = K * (y / (e2 + G * y)) := by
  have hz : 0 < e2 + G * y := by have := mul_pos hG hy; linarith
  rw [eq_comm, ← mul_div_assoc, div_eq_iff hz.ne']
  linear_combination hyd

/-- **`γ = 1`: a successor exists iff `Av (m t) < K / G`** (and `Bv < 1 / G` always). -/
theorem fwd_exists_one (β G μ e1 e2 x : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ)
    (hx0 : 0 < x) (hx1 : x < e1) :
    (∃ y, 0 < y ∧ Av 1 e1 x = Kc β G μ * Bv 1 G e2 y) ↔ Av 1 e1 x < Kc β G μ / G := by
  have hA := Av_pos 1 e1 x hx0 hx1
  constructor
  · rintro ⟨y, hy, h⟩
    have hz : 0 < e2 + G * y := by have := mul_pos hG hy; linarith
    have hq : y / (e2 + G * y) * G < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hz]
      linarith
    have h2 := mul_lt_mul_of_pos_left hq hK
    rw [h, Bv_one G e2 y hz, lt_div_iff₀ hG]
    linarith
  · intro hlt
    rw [lt_div_iff₀ hG] at hlt
    have hd : 0 < Kc β G μ - G * Av 1 e1 x := by linarith
    have hy : 0 < Av 1 e1 x * e2 / (Kc β G μ - G * Av 1 e1 x) := div_pos (mul_pos hA he2) hd
    refine ⟨_, hy, ?_⟩
    rw [Bv_one G e2 _ (by have := mul_pos hG hy; linarith)]
    exact one_solve _ _ G e2 _ he2 hG hy (div_mul_cancel₀ _ hd.ne')

/-- **`γ = 1`, explicit form**: a successor exists iff `m t (1 + μ + β) < β e1`. -/
theorem fwd_exists_one_iff (β G μ e1 e2 x : ℝ) (hβ : 0 < β) (hG : 0 < G) (he2 : 0 < e2)
    (hμ : -1 < μ) (hx0 : 0 < x) (hx1 : x < e1) :
    (∃ y, 0 < y ∧ Av 1 e1 x = Kc β G μ * Bv 1 G e2 y) ↔ x * (1 + μ + β) < β * e1 := by
  rw [fwd_exists_one β G μ e1 e2 x hG he2 (Kc_pos β G μ hβ hG hμ) hx0 hx1, Av_one e1 x hx1]
  have hGi : G * G⁻¹ = 1 := mul_inv_cancel₀ hG.ne'
  have h1 : Kc β G μ / G = β / (1 + μ) := by
    unfold Kc
    linear_combination (β / (1 + μ)) * hGi
  rw [h1, div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-! ## 2. Local instability of the stationary point -/

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
theorem slope_eq (γ β G μ e1 e2 ms : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ)
    (hs : IsStat γ β G μ e1 e2 ms) :
    dAv γ e1 ms / (Kc β G μ * dBv γ G e2 ms) = Nn γ e1 ms / Dd γ G e2 ms := by
  obtain ⟨h0, h1, h⟩ := (stat_iff γ β G μ e1 e2 ms).1 hs
  have hz : 0 < e2 + G * ms := by have := mul_pos hG h0; linarith
  have hQ : 0 < (e2 + G * ms) ^ (-γ) := Real.rpow_pos_of_pos hz _
  rw [dAv_eq γ e1 ms h1, dBv_eq γ G e2 ms hz, h]
  by_cases hDd : Dd γ G e2 ms = 0
  · simp [hDd]
  · field_simp [hK.ne', hQ.ne', hDd]

/-- **Slope of the forward map**: any forward map through `m*` differentiable at `m*` has
slope `N / D` there. -/
theorem fwd_slope (γ β G μ e1 e2 ms f' : ℝ) (f : ℝ → ℝ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hD : Dd γ G e2 ms ≠ 0)
    (hf : HasDerivAt f f' ms) (hfm : f ms = ms)
    (hloc : ∀ᶠ x in 𝓝 ms, Av γ e1 x = Kc β G μ * Bv γ G e2 (f x)) :
    f' = Nn γ e1 ms / Dd γ G e2 ms := by
  have h0 := ((stat_iff γ β G μ e1 e2 ms).1 hs).1
  have h1 := ((stat_iff γ β G μ e1 e2 ms).1 hs).2.1
  have hz : 0 < e2 + G * ms := by have := mul_pos hG h0; linarith
  have hQ : 0 < (e2 + G * ms) ^ (-γ) := Real.rpow_pos_of_pos hz _
  have hB : HasDerivAt (Bv γ G e2) (dBv γ G e2 ms) (f ms) := by
    rw [hfm]
    exact Bv_hasDeriv γ G e2 ms hz
  have hc : HasDerivAt (fun x => Kc β G μ * Bv γ G e2 (f x)) (Kc β G μ * (dBv γ G e2 ms * f'))
      ms := (HasDerivAt.comp ms hB hf).const_mul _
  have hA : HasDerivAt (fun x => Kc β G μ * Bv γ G e2 (f x)) (dAv γ e1 ms) ms :=
    (Av_hasDeriv γ e1 ms h1).congr_of_eventuallyEq (hloc.mono fun x hx => hx.symm)
  have heq := hA.unique hc
  have hne : Kc β G μ * dBv γ G e2 ms ≠ 0 := by
    rw [dBv_eq γ G e2 ms hz]
    exact mul_ne_zero hK.ne' (mul_ne_zero hQ.ne' hD)
  rw [← slope_eq γ β G μ e1 e2 ms hG he2 hK hs, heq, eq_div_iff hne]
  ring

theorem Nn_gt_one (γ e1 m : ℝ) (hγ : 0 < γ) (h0 : 0 < m) (h1 : m < e1) : 1 < Nn γ e1 m := by
  unfold Nn
  have := div_pos (mul_pos hγ h0) (sub_pos.2 h1)
  linarith

theorem Dd_lt_one (γ G e2 m : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2) (h0 : 0 < m) :
    Dd γ G e2 m < 1 := by
  unfold Dd
  have hz : 0 < e2 + G * m := by have := mul_pos hG h0; linarith
  have := div_pos (mul_pos (mul_pos hγ hG) h0) hz
  linarith

/-- For `γ ≤ 1` the denominator `D` is positive. -/
theorem Dd_pos_of_le_one (γ G e2 m : ℝ) (hγ1 : γ ≤ 1) (hG : 0 < G) (he2 : 0 < e2)
    (h0 : 0 < m) : 0 < Dd γ G e2 m := by
  have hz : 0 < e2 + G * m := by have := mul_pos hG h0; linarith
  have hq : γ * G * m / (e2 + G * m) < 1 := by
    rw [div_lt_one hz]
    have := mul_le_mul_of_nonneg_right hγ1 (mul_pos hG h0).le
    linarith
  unfold Dd
  linarith

/-- `D < 0` exactly when `e2 + G m* < γ G m*`. -/
theorem Dd_neg_iff (γ G e2 m : ℝ) (hz : 0 < e2 + G * m) :
    Dd γ G e2 m < 0 ↔ e2 + G * m < γ * G * m := by
  unfold Dd
  rw [← one_lt_div hz]
  constructor <;> intro h <;> linarith

/-- `D < 0` forces `γ > 1`. -/
theorem one_lt_of_Dd_neg (γ G e2 m : ℝ) (hG : 0 < G) (he2 : 0 < e2) (h0 : 0 < m)
    (hD : Dd γ G e2 m < 0) : 1 < γ := by
  by_contra hc
  push Not at hc
  linarith [Dd_pos_of_le_one γ G e2 m hc hG he2 h0]

/-- `D > 0` gives slope `> 1`. -/
theorem slope_gt_one (γ G e2 e1 m : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2) (h0 : 0 < m)
    (h1 : m < e1) (hD : 0 < Dd γ G e2 m) : 1 < Nn γ e1 m / Dd γ G e2 m := by
  rw [one_lt_div hD]
  linarith [Nn_gt_one γ e1 m hγ h0 h1, Dd_lt_one γ G e2 m hγ hG he2 h0]

/-- `D < 0` gives a negative slope. -/
theorem slope_neg (γ G e2 e1 m : ℝ) (hγ : 0 < γ) (h0 : 0 < m) (h1 : m < e1)
    (hD : Dd γ G e2 m < 0) : Nn γ e1 m / Dd γ G e2 m < 0 :=
  div_neg_of_pos_of_neg (by linarith [Nn_gt_one γ e1 m hγ h0 h1]) hD

/-- **Flip condition**: with `D < 0`, the slope is below `−1` iff `−D < N`. -/
theorem slope_flip_iff (γ G e2 e1 m : ℝ) (hD : Dd γ G e2 m < 0) :
    Nn γ e1 m / Dd γ G e2 m < -1 ↔ -Dd γ G e2 m < Nn γ e1 m := by
  rw [div_lt_iff_of_neg hD]
  constructor <;> intro h <;> linarith

/-- For `γ ≤ 2`, a negative slope is always below `−1`. -/
theorem slope_flip_of_le_two (γ G e2 e1 m : ℝ) (hγ : 0 < γ) (hγ2 : γ ≤ 2) (hG : 0 < G)
    (he2 : 0 < e2) (h0 : 0 < m) (h1 : m < e1) (hD : Dd γ G e2 m < 0) :
    Nn γ e1 m / Dd γ G e2 m < -1 := by
  rw [slope_flip_iff γ G e2 e1 m hD]
  have hz : 0 < e2 + G * m := by have := mul_pos hG h0; linarith
  have hq : γ * G * m / (e2 + G * m) < γ := by
    rw [div_lt_iff₀ hz]
    have := mul_pos hγ he2
    linarith
  have := Nn_gt_one γ e1 m hγ h0 h1
  unfold Dd
  linarith

/-- **Local instability for `γ ≤ 1`**: the forward slope at `m*` exceeds `1`. -/
theorem fwd_slope_gt_one (γ β G μ e1 e2 ms f' : ℝ) (f : ℝ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hf : HasDerivAt f f' ms) (hfm : f ms = ms)
    (hloc : ∀ᶠ x in 𝓝 ms, Av γ e1 x = Kc β G μ * Bv γ G e2 (f x)) : 1 < f' := by
  have h0 := ((stat_iff γ β G μ e1 e2 ms).1 hs).1
  have h1 := ((stat_iff γ β G μ e1 e2 ms).1 hs).2.1
  have hD := Dd_pos_of_le_one γ G e2 ms hγ1 hG he2 h0
  rw [fwd_slope γ β G μ e1 e2 ms f' f hG he2 hK hs hD.ne' hf hfm hloc]
  exact slope_gt_one γ G e2 e1 ms hγ hG he2 h0 h1 hD

/-- **Oscillation for `D < 0`**: the forward slope at `m*` is negative. -/
theorem fwd_slope_neg (γ β G μ e1 e2 ms f' : ℝ) (f : ℝ → ℝ) (hγ : 0 < γ)
    (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hD : Dd γ G e2 ms < 0) (hf : HasDerivAt f f' ms) (hfm : f ms = ms)
    (hloc : ∀ᶠ x in 𝓝 ms, Av γ e1 x = Kc β G μ * Bv γ G e2 (f x)) : f' < 0 := by
  have h0 := ((stat_iff γ β G μ e1 e2 ms).1 hs).1
  have h1 := ((stat_iff γ β G μ e1 e2 ms).1 hs).2.1
  rw [fwd_slope γ β G μ e1 e2 ms f' f hG he2 hK hs hD.ne hf hfm hloc]
  exact slope_neg γ G e2 e1 ms hγ h0 h1 hD

/-! ## 3. Inflation along collapsing paths -/

/-- Inflation along a path, from the Euler equation. -/
theorem infl_path (γ β G μ e1 e2 : ℝ) (m : ℕ → ℝ) (hG : 0 < G) (hμ : -1 < μ)
    (hp : IsPath γ β G μ e1 e2 m) (t : ℕ) :
    infl G μ (m t) (m (t + 1)) = β * (e2 + G * m (t + 1)) ^ (-γ) / (e1 - m t) ^ (-γ) := by
  obtain ⟨h0, h1, h⟩ := hp t
  have hn := (hp (t + 1)).1
  have hP : 0 < (e1 - m t) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _
  have hinv : (1 + μ) * (1 + μ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (by linarith))
  unfold Av Bv Kc at h
  unfold infl
  rw [div_eq_div_iff (mul_pos hG hn).ne' hP.ne']
  linear_combination (1 + μ) * h + β * G * m (t + 1) * (e2 + G * m (t + 1)) ^ (-γ) * hinv

/-- **Inflation rises** along any strictly decreasing path. -/
theorem infl_strictMono (γ β G μ e1 e2 : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hβ : 0 < β)
    (hG : 0 < G) (he2 : 0 < e2) (hμ : -1 < μ) (hp : IsPath γ β G μ e1 e2 m)
    (hd : StrictAnti m) : StrictMono (fun t => infl G μ (m t) (m (t + 1))) := by
  apply strictMono_nat_of_lt_succ
  intro t
  show infl G μ (m t) (m (t + 1)) < infl G μ (m (t + 1)) (m (t + 1 + 1))
  rw [infl_path γ β G μ e1 e2 m hG hμ hp t, infl_path γ β G μ e1 e2 m hG hμ hp (t + 1)]
  have a0 := (hp t).2.1
  have c1 := (hp (t + 1)).1
  have c2 := (hp (t + 1 + 1)).1
  have d1 : m (t + 1) < m t := hd (Nat.lt_succ_self t)
  have d2 : m (t + 1 + 1) < m (t + 1) := hd (Nat.lt_succ_self (t + 1))
  have hP1 : (e1 - m (t + 1)) ^ (-γ) < (e1 - m t) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  have hQ : (e2 + G * m (t + 1)) ^ (-γ) < (e2 + G * m (t + 1 + 1)) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by have := mul_pos hG c2; linarith)
      (by have := mul_lt_mul_of_pos_left d2 hG; linarith) (by linarith)
  have hP0 : 0 < (e1 - m t) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _
  have hP1' : 0 < (e1 - m (t + 1)) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _
  have hQ0 : 0 < (e2 + G * m (t + 1)) ^ (-γ) :=
    Real.rpow_pos_of_pos (by have := mul_pos hG c1; linarith) _
  rw [div_lt_div_iff₀ hP0 hP1']
  have key := mul_lt_mul' hP1.le hQ hQ0.le hP0
  have := mul_lt_mul_of_pos_left key hβ
  linarith

theorem lim_val (β γ e1 e2 : ℝ) (he1 : 0 < e1) (he2 : 0 < e2) :
    β * e2 ^ (-γ) / e1 ^ (-γ) = β * (e1 / e2) ^ γ := by
  rw [Real.rpow_neg he2.le, Real.rpow_neg he1.le, div_inv_eq_mul, Real.div_rpow he1.le he2.le]
  ring

/-- **Limit of inflation** along a path converging to `0`: `β (e1 / e2) ^ γ`. -/
theorem infl_limit (γ β G μ e1 e2 : ℝ) (m : ℕ → ℝ) (hG : 0 < G) (he1 : 0 < e1)
    (he2 : 0 < e2) (hμ : -1 < μ) (hp : IsPath γ β G μ e1 e2 m) (hm : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun t => infl G μ (m t) (m (t + 1))) atTop (𝓝 (β * (e1 / e2) ^ γ)) := by
  have hm1 : Tendsto (fun t => m (t + 1)) atTop (𝓝 0) := hm.comp (tendsto_add_atTop_nat 1)
  have hQ : Tendsto (fun t => (e2 + G * m (t + 1)) ^ (-γ)) atTop (𝓝 ((e2 + G * 0) ^ (-γ))) :=
    (tendsto_const_nhds.add (hm1.const_mul G)).rpow_const
      (Or.inl (by rw [mul_zero, add_zero]; exact he2.ne'))
  have hP : Tendsto (fun t => (e1 - m t) ^ (-γ)) atTop (𝓝 ((e1 - 0) ^ (-γ))) :=
    (tendsto_const_nhds.sub hm).rpow_const (Or.inl (by rw [sub_zero]; exact he1.ne'))
  have hP0 : (e1 - 0) ^ (-γ) ≠ 0 := by
    rw [sub_zero]
    exact (Real.rpow_pos_of_pos he1 _).ne'
  have hlim := (hQ.const_mul β).div hP hP0
  rw [mul_zero, add_zero, sub_zero, lim_val β γ e1 e2 he1 he2] at hlim
  exact hlim.congr fun t => (infl_path γ β G μ e1 e2 m hG hμ hp t).symm

/-- **The limit exceeds stationary inflation** whenever a stationary point exists. -/
theorem infl_limit_gt (γ β G μ e1 e2 ms : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he1 : 0 < e1) (he2 : 0 < e2) (hμ : -1 < μ) (hs : IsStat γ β G μ e1 e2 ms) :
    (1 + μ) / G < β * (e1 / e2) ^ γ := by
  obtain ⟨h0, h1, h⟩ := (stat_iff γ β G μ e1 e2 ms).1 hs
  have hK := Kc_pos β G μ hβ hG hμ
  have ha : e1 ^ (-γ) < (e1 - ms) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  have hb : (e2 + G * ms) ^ (-γ) < e2 ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg he2 (by have := mul_pos hG h0; linarith) (by linarith)
  have hc : e1 ^ (-γ) < Kc β G μ * e2 ^ (-γ) := by
    rw [h] at ha
    exact ha.trans (mul_lt_mul_of_pos_left hb hK)
  have hinv : (1 + μ) * (1 + μ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (by linarith))
  have hKe : (1 + μ) * (Kc β G μ * e2 ^ (-γ)) = β * e2 ^ (-γ) * G := by
    unfold Kc
    linear_combination (β * G * e2 ^ (-γ)) * hinv
  rw [← lim_val β γ e1 e2 he1 he2, div_lt_div_iff₀ hG (Real.rpow_pos_of_pos he1 _)]
  have := mul_lt_mul_of_pos_left hc (by linarith : (0 : ℝ) < 1 + μ)
  linarith

/-- **Inflation along collapsing paths (`γ ≤ 1`)**: strictly increasing, converging to
`β (e1 / e2) ^ γ`, which is above stationary inflation `(1 + μ) / G`. -/
theorem infl_below (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hβ : 0 < β) (hG : 0 < G) (he1 : 0 < e1) (he2 : 0 < e2) (hμ : -1 < μ)
    (hs : IsStat γ β G μ e1 e2 ms) (hp : IsPath γ β G μ e1 e2 m) (h0 : m 0 < ms) :
    StrictMono (fun t => infl G μ (m t) (m (t + 1))) ∧
      Tendsto (fun t => infl G μ (m t) (m (t + 1))) atTop (𝓝 (β * (e1 / e2) ^ γ)) ∧
      (1 + μ) / G < β * (e1 / e2) ^ γ := by
  have hK := Kc_pos β G μ hβ hG hμ
  obtain ⟨hanti, hlim⟩ := path_below γ β G μ e1 e2 ms m hγ hγ1 hG he2 hK hs hp h0
  exact ⟨infl_strictMono γ β G μ e1 e2 m hγ hβ hG he2 hμ hp hanti,
    infl_limit γ β G μ e1 e2 m hG he1 he2 hμ hp hlim,
    infl_limit_gt γ β G μ e1 e2 ms hγ hβ hG he1 he2 hμ hs⟩

/-! ## 4. The case `γ > 1` -/

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

theorem rpow_neg_two (z : ℝ) (hz : 0 < z) : z ^ (-(2 : ℝ)) = (z ^ 2)⁻¹ := by
  rw [Real.rpow_neg hz.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_neg_three (z : ℝ) (hz : 0 < z) : z ^ (-(3 : ℝ)) = (z ^ 3)⁻¹ := by
  rw [Real.rpow_neg hz.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- With `γ = 2`, `G = e2 = 1`: `Bv (1/2) = Bv 2`. -/
theorem Bv_two_example : Bv 2 1 1 (1 / 2) = Bv 2 1 1 2 := by
  unfold Bv
  rw [rpow_neg_two (1 + 1 * (1 / 2)) (by norm_num), rpow_neg_two (1 + 1 * 2) (by norm_num)]
  norm_num

/-- **The forward map is multi-valued for `γ = 2`**: some `m t` has two successors. -/
theorem fwd_multivalued (β μ e1 : ℝ) (hβ : 0 < β) (hμ : -1 < μ) (he1 : 0 < e1) :
    ∃ x y y', 0 < x ∧ x < e1 ∧ 0 < y ∧ 0 < y' ∧ y ≠ y' ∧
      Av 2 e1 x = Kc β 1 μ * Bv 2 1 1 y ∧ Av 2 e1 x = Kc β 1 μ * Bv 2 1 1 y' := by
  have hK := Kc_pos β 1 μ hβ one_pos hμ
  obtain ⟨x, hx0, hx1, hx⟩ :=
    Av_surj 2 e1 _ two_pos he1 (mul_pos hK (Bv_pos 2 1 1 2 one_pos one_pos two_pos))
  refine ⟨x, 1 / 2, 2, hx0, hx1, by norm_num, two_pos, by norm_num, ?_, hx⟩
  rw [hx, Bv_two_example]

theorem cycle_eq1 : Av 3 20 1 = Kc (343 / 32768) 1 0 * Bv 3 1 (5 / 16) 8 := by
  unfold Av Bv Kc
  rw [rpow_neg_three (20 - 1) (by norm_num), rpow_neg_three (5 / 16 + 1 * 8) (by norm_num)]
  norm_num

theorem cycle_eq2 : Av 3 20 8 = Kc (343 / 32768) 1 0 * Bv 3 1 (5 / 16) 1 := by
  unfold Av Bv Kc
  rw [rpow_neg_three (20 - 8) (by norm_num), rpow_neg_three (5 / 16 + 1 * 1) (by norm_num)]
  norm_num

/-- **An explicit two-cycle equilibrium path** (`γ = 3`). -/
theorem cycle_path : IsPath 3 (343 / 32768) 1 0 20 (5 / 16) cyc ∧ cyc 0 ≠ cyc 1 := by
  refine ⟨fun t => ?_, ?_⟩
  · by_cases ht : t % 2 = 0
    · have ht1 : ¬ (t + 1) % 2 = 0 := by omega
      have e0 : cyc t = 1 := ite_eq_left ht
      have e1 : cyc (t + 1) = 8 := ite_eq_right ht1
      rw [e0, e1]
      exact ⟨by norm_num, by norm_num, cycle_eq1⟩
    · have ht1 : (t + 1) % 2 = 0 := by omega
      have e0 : cyc t = 8 := ite_eq_right ht
      have e1 : cyc (t + 1) = 1 := ite_eq_left ht1
      rw [e0, e1]
      exact ⟨by norm_num, by norm_num, cycle_eq2⟩
  · have e0 : cyc 0 = 1 := ite_eq_left rfl
    have e1 : cyc 1 = 8 := ite_eq_right (by norm_num)
    rw [e0, e1]
    norm_num

end

end MoneyDynamics

#print axioms MoneyDynamics.Bv_unbounded
#print axioms MoneyDynamics.fwd_existsUnique
#print axioms MoneyDynamics.fwd_function
#print axioms MoneyDynamics.fwd_exists_one
#print axioms MoneyDynamics.fwd_exists_one_iff
#print axioms MoneyDynamics.Av_strictMono
#print axioms MoneyDynamics.Av_hasDeriv
#print axioms MoneyDynamics.Bv_hasDeriv
#print axioms MoneyDynamics.slope_eq
#print axioms MoneyDynamics.fwd_slope
#print axioms MoneyDynamics.Dd_pos_of_le_one
#print axioms MoneyDynamics.Dd_neg_iff
#print axioms MoneyDynamics.one_lt_of_Dd_neg
#print axioms MoneyDynamics.slope_gt_one
#print axioms MoneyDynamics.slope_neg
#print axioms MoneyDynamics.slope_flip_iff
#print axioms MoneyDynamics.slope_flip_of_le_two
#print axioms MoneyDynamics.fwd_slope_gt_one
#print axioms MoneyDynamics.fwd_slope_neg
#print axioms MoneyDynamics.infl_path
#print axioms MoneyDynamics.infl_strictMono
#print axioms MoneyDynamics.infl_limit
#print axioms MoneyDynamics.infl_limit_gt
#print axioms MoneyDynamics.antitone_path_zero
#print axioms MoneyDynamics.infl_below
#print axioms MoneyDynamics.Av_surj
#print axioms MoneyDynamics.back_existsUnique
#print axioms MoneyDynamics.Bv_two_example
#print axioms MoneyDynamics.fwd_multivalued
#print axioms MoneyDynamics.cycle_path
