import Mathlib

/-!
# Stage 381: transition dynamics of the money-growth economy of stage 377

Stage 377 studied stationary equilibria of the overlapping-generations economy with a money
stock growing at rate `μ > −1` (new money handed lump-sum to the old). This file studies the
non-stationary paths of the same economy.

Setting: generations of relative size `G > 0`, endowments `e1, e2 > 0`, lifetime utility
`u (c₁) + β u (c₂)` with `β > 0`, `u' c = c ^ (−γ)`, `γ > 0`. Let `m t` be real balances per
young person at date `t`. Money bought at `t` returns `R (t+1) = G m (t+1) / ((1 + μ) m t)`
(`ret`), and an old person at `t + 1` consumes `e2 + G m (t+1)` (transfer plus own money, as in
stage 377 `cons_id`). The young household's Euler equation
`(e1 − m t) ^ (−γ) = β R (t+1) (e2 + G m (t+1)) ^ (−γ)` is, after multiplying by `m t`,
the forward map

  `Av (m t) = K · Bv (m (t+1))`, where `Av x = x (e1 − x) ^ (−γ)`,
  `Bv y = y (e2 + G y) ^ (−γ)`, `K = β G / (1 + μ)` (`Kc`).

An equilibrium path (`IsPath`) is a sequence with `0 < m t < e1` satisfying this at every date;
a stationary point (`IsStat`) is a constant one, which by `stat_iff` is exactly the stationary
Euler equation of stage 377.

## What is proved

* `path_euler`: the forward map is equivalent to the household Euler equation with return `ret`.
* `stat_iff`, `stat_unique`: the stationary point is the stage 377 equilibrium; it is unique.
* `sign_below`, `sign_above`: `Av < K Bv` strictly below the stationary point, `Av > K Bv`
  strictly above it (no restriction on `γ`).
* **Well-posedness** (assuming `γ ≤ 1`):
  - `Bv_strictMono`: `y ↦ y (e2 + G y) ^ (−γ)` is strictly increasing on `(0, ∞)`;
  - `next_unique`: each `m t` admits at most one `m (t+1) > 0`;
  - `next_exists_iff`: one exists iff `Av (m t) ≤ K · Bv Y` for some `Y > 0`, i.e. iff
    `Av (m t) / K` lies in the range of `Bv` (this direction needs no restriction on `γ`).
* **Phase portrait** (`γ ≤ 1`, stationary point `m*`):
  - `path_below`: if `m 0 < m*`, the path is strictly decreasing, stays below `m*`, and
    converges to `0` (the value of money vanishes asymptotically);
  - `path_ret_below`: along such a path the return on money is below the stationary return
    `G / (1 + μ)` at every date, i.e. inflation exceeds the stationary inflation rate;
  - `no_path_above`: no equilibrium path starts above `m*` (the path would be strictly
    increasing, stay bounded away from `e1` by the budget, converge, and its limit would be a
    second stationary point).
* **Indeterminacy** (`γ ≤ 1`):
  - `path_classify`: every equilibrium path is either the constant path `m*` or converges to `0`;
  - `path_exists`: every `m 0 ∈ (0, m*]` starts an equilibrium path (which is antitone).
* **Comparative dynamics** `next_mono_mu`: for a given `m t`, a higher money growth rate `μ`
  requires a strictly higher `m (t+1)` (`γ ≤ 1`).

## Limits

* The monotonicity hypothesis `γ ≤ 1` is used for uniqueness of the forward step and for the
  whole phase portrait. For `γ > 1`, `Bv` is not monotone, the forward map can be multi-valued,
  and cycles or sunspot paths are not excluded; nothing here covers that case.
* Existence of the next step is characterised through the range of `Bv`; the explicit fact that
  `Bv` is unbounded when `γ < 1` (so a step always exists) is not proved here.
* The stationary point `m*` is taken as a hypothesis; its existence condition is stage 377
  `exists_iff`.
* Inflation along a decreasing path is shown to exceed the stationary rate at every date; it is
  NOT shown to rise monotonically over time.
* Local instability of `m*` as a derivative statement (slope of the forward map above 1) is not
  proved; only the global statement that paths starting off `m*` move away from it.
* The money growth rate is constant along the path; no feedback rules, no welfare comparison of
  paths, no initial-old allocation question.
-/

open Set Filter Topology

namespace MoneyTransition

noncomputable section

/-- Young side of the forward map: `x (e1 − x) ^ (−γ)`. -/
def Av (γ e1 x : ℝ) : ℝ := x * (e1 - x) ^ (-γ)

/-- Old side of the forward map: `y (e2 + G y) ^ (−γ)`. -/
def Bv (γ G e2 y : ℝ) : ℝ := y * (e2 + G * y) ^ (-γ)

/-- The constant `β G / (1 + μ)`. -/
def Kc (β G μ : ℝ) : ℝ := β * G / (1 + μ)

/-- The gross real return on money between two dates with real balances `x` then `y`. -/
def ret (G μ x y : ℝ) : ℝ := G * y / ((1 + μ) * x)

/-- An equilibrium path of real balances. -/
def IsPath (γ β G μ e1 e2 : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ m t < e1 ∧ Av γ e1 (m t) = Kc β G μ * Bv γ G e2 (m (t + 1))

/-- A stationary point of the forward map. -/
def IsStat (γ β G μ e1 e2 ms : ℝ) : Prop :=
  0 < ms ∧ ms < e1 ∧ Av γ e1 ms = Kc β G μ * Bv γ G e2 ms

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

/-- **Monotone old side** (`γ ≤ 1`). -/
theorem Bv_strictMono (γ G e2 : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G) (he2 : 0 < e2) :
    StrictMonoOn (Bv γ G e2) (Ioi 0) := by
  intro y hy y' hy' hyy
  rw [mem_Ioi] at hy hy'
  have hz : 0 < e2 + G * y := by have := mul_pos hG hy; linarith
  have hz' : 0 < e2 + G * y' := by have := mul_pos hG hy'; linarith
  have key : ∀ x : ℝ, 0 < x → Bv γ G e2 x = x ^ (1 - γ) * (x / (e2 + G * x)) ^ γ := by
    intro x hx
    have hzx : 0 < e2 + G * x := by have := mul_pos hG hx; linarith
    have h1 : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
    have h2 : 0 < (e2 + G * x) ^ γ := Real.rpow_pos_of_pos hzx γ
    unfold Bv
    rw [Real.div_rpow hx.le hzx.le, Real.rpow_neg hzx.le, Real.rpow_sub hx, Real.rpow_one]
    field_simp
  rw [key y hy, key y' hy']
  have h1 : y ^ (1 - γ) ≤ y' ^ (1 - γ) := Real.rpow_le_rpow hy.le hyy.le (by linarith)
  have h2 : (y / (e2 + G * y)) ^ γ < (y' / (e2 + G * y')) ^ γ := by
    apply Real.rpow_lt_rpow (div_pos hy hz).le _ hγ
    rw [div_lt_div_iff₀ hz hz']
    nlinarith
  exact mul_lt_mul' h1 h2 (Real.rpow_nonneg (div_pos hy hz).le _) (Real.rpow_pos_of_pos hy' _)

/-- The forward map is the household Euler equation with return `ret`. -/
theorem path_euler (γ β G μ e1 e2 x y : ℝ) (hμ : -1 < μ) (hx : 0 < x) :
    Av γ e1 x = Kc β G μ * Bv γ G e2 y ↔
      (e1 - x) ^ (-γ) = β * ret G μ x y * (e2 + G * y) ^ (-γ) := by
  have h1 : (1 + μ) ≠ 0 := ne_of_gt (by linarith)
  have hx' : x ≠ 0 := hx.ne'
  have key : β * ret G μ x y * (e2 + G * y) ^ (-γ) = Kc β G μ * Bv γ G e2 y / x := by
    unfold ret Kc Bv
    field_simp
  rw [key, eq_div_iff hx']
  unfold Av
  rw [mul_comm x]

/-- A stationary point is exactly a stage 377 stationary equilibrium. -/
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

theorem sign_above (γ β G μ e1 e2 ms x : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hsx : ms < x) (hx1 : x < e1) :
    Kc β G μ * Bv γ G e2 x < Av γ e1 x := by
  obtain ⟨h0, h1, h⟩ := (stat_iff γ β G μ e1 e2 ms).1 hs
  have hx0 : 0 < x := h0.trans hsx
  have ha : (e1 - ms) ^ (-γ) < (e1 - x) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  have hb : (e2 + G * x) ^ (-γ) < (e2 + G * ms) ^ (-γ) :=
    Real.rpow_lt_rpow_of_neg (by have := mul_pos hG h0; linarith)
      (by have := mul_lt_mul_of_pos_left hsx hG; linarith) (by linarith)
  have hc : Kc β G μ * (e2 + G * x) ^ (-γ) < (e1 - x) ^ (-γ) := by
    rw [h] at ha
    exact (mul_lt_mul_of_pos_left hb hK).trans ha
  unfold Av Bv
  calc Kc β G μ * (x * (e2 + G * x) ^ (-γ)) = x * (Kc β G μ * (e2 + G * x) ^ (-γ)) := by ring
    _ < x * (e1 - x) ^ (-γ) := mul_lt_mul_of_pos_left hc hx0

/-- The stationary point is unique. -/
theorem stat_unique (γ β G μ e1 e2 ms ms' : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hs' : IsStat γ β G μ e1 e2 ms') :
    ms = ms' := by
  obtain ⟨a0, a1, a2⟩ := hs
  obtain ⟨b0, b1, b2⟩ := hs'
  rcases lt_trichotomy ms ms' with h | h | h
  · exact absurd b2 (ne_of_gt (sign_above γ β G μ e1 e2 ms ms' hγ hG he2 hK ⟨a0, a1, a2⟩ h b1))
  · exact h
  · exact absurd b2 (ne_of_lt (sign_below γ β G μ e1 e2 ms ms' hγ hG he2 hK ⟨a0, a1, a2⟩ b0 h))

/-! ## Well-posedness of the forward map -/

/-- **Uniqueness of the next step** (`γ ≤ 1`). -/
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

/-- **Existence of the next step**: exactly when `Av x / K` is in the range of `Bv`. -/
theorem next_exists_iff (γ β G μ e1 e2 x : ℝ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hx0 : 0 < x) (hx1 : x < e1) :
    (∃ y, 0 < y ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y) ↔
      ∃ Y, 0 < Y ∧ Av γ e1 x ≤ Kc β G μ * Bv γ G e2 Y := by
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.le⟩
  · rintro ⟨Y, hY, h⟩
    obtain ⟨y, hy, _, hyx⟩ := next_exists γ β G μ e1 e2 x Y hG he2 hK hx0 hx1 hY h
    exact ⟨y, hy, hyx⟩

/-! ## One step of the dynamics -/

theorem step_down (γ β G μ e1 e2 ms x y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hx0 : 0 < x)
    (hxs : x < ms) (hy : 0 < y) (h : Av γ e1 x = Kc β G μ * Bv γ G e2 y) : y < x := by
  by_contra hc
  push Not at hc
  have hB := (Bv_strictMono γ G e2 hγ hγ1 hG he2).monotoneOn (mem_Ioi.2 hx0) (mem_Ioi.2 hy) hc
  have h1 := sign_below γ β G μ e1 e2 ms x hγ hG he2 hK hs hx0 hxs
  have h2 := mul_le_mul_of_nonneg_left hB hK.le
  linarith

theorem step_up (γ β G μ e1 e2 ms x y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hsx : ms < x)
    (hx1 : x < e1) (hy : 0 < y) (h : Av γ e1 x = Kc β G μ * Bv γ G e2 y) : x < y := by
  have h0 : 0 < ms := ((stat_iff γ β G μ e1 e2 ms).1 hs).1
  by_contra hc
  push Not at hc
  have hB := (Bv_strictMono γ G e2 hγ hγ1 hG he2).monotoneOn (mem_Ioi.2 hy)
    (mem_Ioi.2 (h0.trans hsx)) hc
  have h1 := sign_above γ β G μ e1 e2 ms x hγ hG he2 hK hs hsx hx1
  have h2 := mul_le_mul_of_nonneg_left hB hK.le
  linarith

theorem step_stat (γ β G μ e1 e2 ms y : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hG : 0 < G)
    (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (hy : 0 < y)
    (h : Av γ e1 ms = Kc β G μ * Bv γ G e2 y) : y = ms := by
  obtain ⟨h0, _, h2⟩ := hs
  exact next_unique γ β G μ e1 e2 ms y ms hγ hγ1 hG he2 hK hy h0 h h2

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

/-! ## Phase portrait -/

/-- **Below the stationary point**: strictly decreasing, stays below, converges to `0`. -/
theorem path_below (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he2 : 0 < e2) (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms)
    (hp : IsPath γ β G μ e1 e2 m) (h0 : m 0 < ms) :
    StrictAnti m ∧ (∀ t, m t < ms) ∧ Tendsto m atTop (𝓝 0) := by
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
  refine ⟨hanti, hlt, ?_⟩
  have hbdd : BddBelow (range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hp t).1.le⟩
  have hL := tendsto_atTop_ciInf hanti.antitone hbdd
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

/-- Along a path below the stationary point the return on money is below the stationary
return `G / (1 + μ)` at every date. -/
theorem path_ret_below (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he2 : 0 < e2) (hμ : -1 < μ) (hK : 0 < Kc β G μ)
    (hs : IsStat γ β G μ e1 e2 ms) (hp : IsPath γ β G μ e1 e2 m) (h0 : m 0 < ms) (t : ℕ) :
    ret G μ (m t) (m (t + 1)) < G / (1 + μ) := by
  have hdec := (path_below γ β G μ e1 e2 ms m hγ hγ1 hG he2 hK hs hp h0).1
  have hyx : m (t + 1) < m t := hdec (Nat.lt_succ_self t)
  have hy := (hp (t + 1)).1
  have h1 : 0 < 1 + μ := by linarith
  unfold ret
  rw [div_lt_div_iff₀ (mul_pos h1 (hy.trans hyx)) h1]
  nlinarith [mul_pos (mul_pos hG h1) (sub_pos.2 hyx)]

/-- **Above the stationary point there is no equilibrium path.** -/
theorem no_path_above (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he1 : 0 < e1) (he2 : 0 < e2) (hK : 0 < Kc β G μ)
    (hs : IsStat γ β G μ e1 e2 ms) (hp : IsPath γ β G μ e1 e2 m) : ¬ ms < m 0 := by
  intro h0
  have hgt : ∀ t, ms < m t := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      exact ih.trans (step_up γ β G μ e1 e2 ms (m n) (m (n + 1)) hγ hγ1 hG he2 hK hs ih
        (hp n).2.1 (hp (n + 1)).1 (hp n).2.2)
  have hmono : StrictMono m := strictMono_nat_of_lt_succ fun n =>
    step_up γ β G μ e1 e2 ms (m n) (m (n + 1)) hγ hγ1 hG he2 hK hs (hgt n) (hp n).2.1
      (hp (n + 1)).1 (hp n).2.2
  have hm0 := (hp 0).1
  have hBe1 := Bv_pos γ G e2 e1 hG he2 he1
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta e1 (Kc β G μ * Bv γ G e2 e1 / m 0) γ he1
    (div_nonneg (mul_pos hK hBe1).le hm0.le) hγ
  rw [div_lt_iff₀ hm0] at hδM
  have hb : ∀ t, m t ≤ e1 - δ := by
    intro t
    by_contra hc
    push Not at hc
    obtain ⟨ht0, ht1, ht⟩ := hp t
    obtain ⟨hn0, hn1, _⟩ := hp (t + 1)
    have hX : δ ^ (-γ) < (e1 - m t) ^ (-γ) :=
      Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
    have hXp : 0 < (e1 - m t) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _
    have hmon : m 0 ≤ m t := hmono.monotone (Nat.zero_le t)
    have hBle : Bv γ G e2 (m (t + 1)) ≤ Bv γ G e2 e1 :=
      (Bv_strictMono γ G e2 hγ hγ1 hG he2).monotoneOn (mem_Ioi.2 hn0) (mem_Ioi.2 he1) hn1.le
    have q1 := mul_le_mul_of_nonneg_left hmon hXp.le
    have q2 := mul_lt_mul_of_pos_right hX hm0
    have q3 := mul_le_mul_of_nonneg_left hBle hK.le
    unfold Av at ht
    linarith
  have hbdd : BddAbove (range m) := ⟨e1 - δ, by rintro _ ⟨t, rfl⟩; exact hb t⟩
  have hL := tendsto_atTop_ciSup hmono.monotone hbdd
  have hLle : (⨆ t, m t) ≤ e1 - δ := ciSup_le hb
  have hLge : m 0 ≤ ⨆ t, m t := le_ciSup hbdd 0
  have hst := limit_stat γ β G μ e1 e2 _ m hG he2 hp hL (by linarith) (by linarith)
  exact absurd hst (ne_of_gt (sign_above γ β G μ e1 e2 ms _ hγ hG he2 hK hs (by linarith)
    (by linarith)))

/-! ## Indeterminacy -/

/-- **Classification**: every equilibrium path is the stationary one or converges to `0`. -/
theorem path_classify (γ β G μ e1 e2 ms : ℝ) (m : ℕ → ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hG : 0 < G) (he1 : 0 < e1) (he2 : 0 < e2) (hK : 0 < Kc β G μ)
    (hs : IsStat γ β G μ e1 e2 ms) (hp : IsPath γ β G μ e1 e2 m) :
    (∀ t, m t = ms) ∨ Tendsto m atTop (𝓝 0) := by
  rcases lt_trichotomy (m 0) ms with h | h | h
  · exact Or.inr (path_below γ β G μ e1 e2 ms m hγ hγ1 hG he2 hK hs hp h).2.2
  · left
    intro t
    induction t with
    | zero => exact h
    | succ n ih =>
      have hn := (hp n).2.2
      rw [ih] at hn
      exact step_stat γ β G μ e1 e2 ms (m (n + 1)) hγ hγ1 hG he2 hK hs (hp (n + 1)).1 hn
  · exact absurd h (no_path_above γ β G μ e1 e2 ms m hγ hγ1 hG he1 he2 hK hs hp)

/-- **Indeterminacy**: every initial value in `(0, m*]` starts an equilibrium path. -/
theorem path_exists (γ β G μ e1 e2 ms m0 : ℝ) (hγ : 0 < γ) (hG : 0 < G) (he2 : 0 < e2)
    (hK : 0 < Kc β G μ) (hs : IsStat γ β G μ e1 e2 ms) (h0 : 0 < m0) (h1 : m0 ≤ ms) :
    ∃ m : ℕ → ℝ, IsPath γ β G μ e1 e2 m ∧ m 0 = m0 ∧ Antitone m := by
  have hs' := hs
  obtain ⟨_, hs1, hs2⟩ := hs'
  have hstep : ∀ x : ℝ, ∃ y : ℝ, x ∈ Ioc 0 ms →
      (0 < y ∧ y ≤ x ∧ Av γ e1 x = Kc β G μ * Bv γ G e2 y) := by
    intro x
    by_cases hx : x ∈ Ioc 0 ms
    · have hle : Av γ e1 x ≤ Kc β G μ * Bv γ G e2 x := by
        rcases hx.2.lt_or_eq with hlt | heq
        · exact (sign_below γ β G μ e1 e2 ms x hγ hG he2 hK hs hx.1 hlt).le
        · rw [heq]
          exact hs2.le
      obtain ⟨y, hy0, hyx, hy⟩ := next_exists γ β G μ e1 e2 x x hG he2 hK hx.1
        (by linarith [hx.2]) hx.1 hle
      exact ⟨y, fun _ => ⟨hy0, hyx, hy⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hstep
  have hin : ∀ t : ℕ, g^[t] m0 ∈ Ioc 0 ms := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨a, b, _⟩ := hg _ ih
      exact ⟨a, b.trans ih.2⟩
  refine ⟨fun t => g^[t] m0, ?_, rfl, ?_⟩
  · intro t
    obtain ⟨_, _, c⟩ := hg _ (hin t)
    refine ⟨(hin t).1, lt_of_le_of_lt (hin t).2 hs1, ?_⟩
    show Av γ e1 (g^[t] m0) = Kc β G μ * Bv γ G e2 (g^[t + 1] m0)
    rw [Function.iterate_succ_apply']
    exact c
  · apply antitone_nat_of_succ_le
    intro n
    show g^[n + 1] m0 ≤ g^[n] m0
    rw [Function.iterate_succ_apply']
    exact (hg _ (hin n)).2.1

/-! ## Comparative dynamics -/

/-- For given current balances, faster money growth requires strictly higher next-period
balances. -/
theorem next_mono_mu (γ β G μ μ' e1 e2 x y y' : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hβ : 0 < β)
    (hG : 0 < G) (he2 : 0 < e2) (hμ : -1 < μ) (hμμ : μ < μ') (hy : 0 < y) (hy' : 0 < y')
    (h : Av γ e1 x = Kc β G μ * Bv γ G e2 y) (h' : Av γ e1 x = Kc β G μ' * Bv γ G e2 y') :
    y < y' := by
  have h1 : 0 < 1 + μ := by linarith
  have h2 : 0 < 1 + μ' := by linarith
  have hKK : Kc β G μ' < Kc β G μ := by
    unfold Kc
    rw [div_lt_div_iff₀ h2 h1]
    nlinarith [mul_pos hβ hG]
  have hK' : 0 < Kc β G μ' := Kc_pos β G μ' hβ hG (by linarith)
  have hBy := Bv_pos γ G e2 y hG he2 hy
  by_contra hc
  push Not at hc
  have hB := (Bv_strictMono γ G e2 hγ hγ1 hG he2).monotoneOn (mem_Ioi.2 hy') (mem_Ioi.2 hy) hc
  have q1 := mul_le_mul_of_nonneg_left hB hK'.le
  have q2 := mul_lt_mul_of_pos_right hKK hBy
  linarith

end

end MoneyTransition

#print axioms MoneyTransition.Bv_strictMono
#print axioms MoneyTransition.path_euler
#print axioms MoneyTransition.stat_iff
#print axioms MoneyTransition.stat_unique
#print axioms MoneyTransition.sign_below
#print axioms MoneyTransition.sign_above
#print axioms MoneyTransition.next_unique
#print axioms MoneyTransition.next_exists_iff
#print axioms MoneyTransition.path_below
#print axioms MoneyTransition.path_ret_below
#print axioms MoneyTransition.no_path_above
#print axioms MoneyTransition.path_classify
#print axioms MoneyTransition.path_exists
#print axioms MoneyTransition.next_mono_mu
