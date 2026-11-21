import Mathlib

/-!
# Stage 369: valued fiat money in a stationary overlapping-generations economy

A first, narrowly scoped treatment of money inside the model. Each period a generation is born,
lives two periods, receives `e1 > 0` when young and `e2 > 0` when old, and has utility
`u c₁ + β u c₂` with `β > 0` and marginal utility `c ^ (−γ)`, `γ > 0` (log and every power
utility). Each generation is `G > 0` times as large as the one before. A fixed stock `M > 0` of
fiat money, which pays no interest, is the only asset. A young household that holds real
balances `s` consumes `e1 − s` young and `e2 + G s` old, because along a stationary path the
price level falls at the growth rate (`price_return`, `price_clears`), so money returns exactly
`G`.

* `E_anti`: the Euler expression `E s = −(e1 − s) ^ (−γ) + β G (e2 + G s) ^ (−γ)` is strictly
  decreasing in saving.
* `strict_opt`, `optimal`: a zero of `E` is the strict maximiser of lifetime utility over all
  affordable saving levels (mean value theorem).
* `root_unique`, `mon_eq_unique`: there is at most one zero, so at most one stationary monetary
  equilibrium.
* **`exists_iff`**: a stationary monetary equilibrium (positive real balances, chosen
  optimally among all non-negative money holdings) exists **if and only if** the Samuelson
  condition `e1 ^ (−γ) < β G e2 ^ (−γ)` holds: at autarky the young would like to save at the
  return `G`, that is, the autarky interest rate is below the growth rate.
* `welfare`: in that equilibrium every generation is strictly better off than in autarky, and
  the initial old consume `e2 + G m > e2`.

Reading: money that pays no interest can still have value and improve on autarky; its return
is the growth rate of the economy, not an interest payment. When `G = 1` the condition reads
`e1 ^ (−γ) < β e2 ^ (−γ)`.

Limits: stationary equilibria only. The non-stationary paths (including the well-known
continuum of paths converging to the non-monetary state) and the stability of the monetary
steady state are not studied. There is one good, one type per generation, no production, no
banks, credit or money creation, and the money stock is fixed. This is not a theory of
endogenous money supply.
-/

noncomputable section

open Set Filter Topology

namespace OLGMoney

/-- Lifetime utility of a young household holding real balances `s`. -/
def U (u : ℝ → ℝ) (β G e1 e2 s : ℝ) : ℝ := u (e1 - s) + β * u (e2 + G * s)

/-- The Euler expression (derivative of `U` in `s`). -/
def E (γ β G e1 e2 s : ℝ) : ℝ := -(e1 - s) ^ (-γ) + β * G * (e2 + G * s) ^ (-γ)

/-- Saving `s` is affordable: consumption is positive in both periods. -/
def Feas (G e1 e2 s : ℝ) : Prop := 0 < e1 - s ∧ 0 < e2 + G * s

/-- The Samuelson condition: autarky interest rate below the growth rate. -/
def Samuelson (γ β G e1 e2 : ℝ) : Prop := e1 ^ (-γ) < β * G * e2 ^ (-γ)

/-- A stationary monetary equilibrium: positive real balances, optimal among all non-negative
money holdings the young can afford. -/
def IsMonEq (u : ℝ → ℝ) (β G e1 e2 m : ℝ) : Prop :=
  0 < m ∧ m < e1 ∧ ∀ s, 0 ≤ s → s < e1 → U u β G e1 e2 s ≤ U u β G e1 e2 m

/-- The price level along the stationary path: `M` units of money buy the real balances of
the `N0 G ^ t` young of date `t`. -/
def price (M N0 G m : ℝ) (t : ℕ) : ℝ := M / (N0 * G ^ t * m)

theorem price_clears (M N0 G m : ℝ) (hN : 0 < N0) (hG : 0 < G) (hm : 0 < m) (t : ℕ) :
    N0 * G ^ t * m * price M N0 G m t = M := by
  have : 0 < N0 * G ^ t * m := by positivity
  unfold price
  field_simp

/-- **Money returns the growth rate**: `p t / p (t + 1) = G`. -/
theorem price_return (M N0 G m : ℝ) (hM : 0 < M) (hN : 0 < N0) (hG : 0 < G) (hm : 0 < m)
    (t : ℕ) : price M N0 G m t / price M N0 G m (t + 1) = G := by
  have h1 : 0 < G ^ t := pow_pos hG t
  unfold price
  rw [pow_succ]
  field_simp

theorem E_anti (γ β G e1 e2 s t : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G) (hst : s < t)
    (hs : Feas G e1 e2 s) (ht : Feas G e1 e2 t) : E γ β G e1 e2 t < E γ β G e1 e2 s := by
  unfold E
  have h1 := Real.rpow_lt_rpow_of_neg ht.1 (by linarith : e1 - t < e1 - s) (by linarith : -γ < 0)
  have h2 := Real.rpow_lt_rpow_of_neg hs.2
    (by linarith [mul_lt_mul_of_pos_left hst hG] : e2 + G * s < e2 + G * t) (by linarith : -γ < 0)
  have h3 := mul_lt_mul_of_pos_left h2 (mul_pos hβ hG)
  linarith

theorem feas_between (G e1 e2 s t x : ℝ) (hG : 0 < G) (h1 : s ≤ x) (h2 : x ≤ t)
    (hs : Feas G e1 e2 s) (ht : Feas G e1 e2 t) : Feas G e1 e2 x :=
  ⟨by linarith [ht.1], by linarith [hs.2, mul_le_mul_of_nonneg_left h1 hG.le]⟩

theorem hasDeriv_U (γ β G e1 e2 x : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hF : Feas G e1 e2 x) :
    HasDerivAt (fun s => U u β G e1 e2 s) (E γ β G e1 e2 x) x := by
  have h1 : HasDerivAt (fun s => e1 - s) (-1) x := (hasDerivAt_id' x).const_sub e1
  have h2 : HasDerivAt (fun s => e2 + G * s) G x :=
    (((hasDerivAt_id' x).const_mul G).const_add e2).congr_deriv (mul_one G)
  have a := (hu _ hF.1).comp x h1
  have b := ((hu _ hF.2).comp x h2).const_mul β
  unfold U E
  exact (a.add b).congr_deriv (by ring)

/-- **A zero of the Euler expression is the strict maximiser** of lifetime utility. -/
theorem strict_opt (γ β G e1 e2 m s : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hFm : Feas G e1 e2 m) (hE : E γ β G e1 e2 m = 0) (hFs : Feas G e1 e2 s) (hne : s ≠ m) :
    U u β G e1 e2 s < U u β G e1 e2 m := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : ∀ x ∈ Icc s m, HasDerivAt (fun t => U u β G e1 e2 t) (E γ β G e1 e2 x) x :=
      fun x hx => hasDeriv_U γ β G e1 e2 x u hu (feas_between G e1 e2 s m x hG hx.1 hx.2 hFs hFm)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun t => U u β G e1 e2 t)
      (fun x => E γ β G e1 e2 x) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between G e1 e2 s m c hG hc.1.le hc.2.le hFs hFm
    have hEc : 0 < E γ β G e1 e2 c := by
      have := E_anti γ β G e1 e2 c m hγ hβ hG hc.2 hcF hFm
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_pos hEc (sub_pos.2 h)]
  · have hd : ∀ x ∈ Icc m s, HasDerivAt (fun t => U u β G e1 e2 t) (E γ β G e1 e2 x) x :=
      fun x hx => hasDeriv_U γ β G e1 e2 x u hu (feas_between G e1 e2 m s x hG hx.1 hx.2 hFm hFs)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun t => U u β G e1 e2 t)
      (fun x => E γ β G e1 e2 x) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between G e1 e2 m s c hG hc.1.le hc.2.le hFm hFs
    have hEc : E γ β G e1 e2 c < 0 := by
      have := E_anti γ β G e1 e2 m c hγ hβ hG hc.1 hFm hcF
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_neg_of_neg_of_pos hEc (sub_pos.2 h)]

theorem optimal (γ β G e1 e2 m s : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hFm : Feas G e1 e2 m) (hE : E γ β G e1 e2 m = 0) (hFs : Feas G e1 e2 s) :
    U u β G e1 e2 s ≤ U u β G e1 e2 m := by
  by_cases h : s = m
  · rw [h]
  · exact (strict_opt γ β G e1 e2 m s u hu hγ hβ hG hFm hE hFs h).le

/-- **The Euler expression has at most one zero.** -/
theorem root_unique (γ β G e1 e2 a b : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (ha : Feas G e1 e2 a) (hb : Feas G e1 e2 b) (hEa : E γ β G e1 e2 a = 0)
    (hEb : E γ β G e1 e2 b = 0) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have := E_anti γ β G e1 e2 a b hγ hβ hG h ha hb
    linarith
  · exact h
  · have := E_anti γ β G e1 e2 b a hγ hβ hG h hb ha
    linarith

/-- A consumption level small enough that its marginal utility exceeds any bound. -/
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

theorem E_zero (γ β G e1 e2 : ℝ) : E γ β G e1 e2 0 = -e1 ^ (-γ) + β * G * e2 ^ (-γ) := by
  unfold E
  simp only [sub_zero, mul_zero, add_zero]

theorem feas_nonneg (G e1 e2 s : ℝ) (hG : 0 < G) (he2 : 0 < e2) (hs : 0 ≤ s) (hs' : s < e1) :
    Feas G e1 e2 s :=
  ⟨by linarith, by nlinarith [mul_nonneg hG.le hs]⟩

/-- Under the Samuelson condition the Euler expression has a positive zero. -/
theorem exists_root (γ β G e1 e2 : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G) (he1 : 0 < e1)
    (he2 : 0 < e2) (hS : Samuelson γ β G e1 e2) :
    ∃ m, 0 < m ∧ Feas G e1 e2 m ∧ E γ β G e1 e2 m = 0 := by
  have hK : 0 ≤ β * G * e2 ^ (-γ) :=
    mul_nonneg (mul_pos hβ hG).le (Real.rpow_nonneg he2.le _)
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta e1 (β * G * e2 ^ (-γ)) γ he1 hK hγ
  set b := e1 - δ with hb
  have hb0 : 0 ≤ b := by linarith
  have hF0 : Feas G e1 e2 0 := feas_nonneg G e1 e2 0 hG he2 le_rfl he1
  have hFb : Feas G e1 e2 b := ⟨by linarith, by nlinarith [mul_nonneg hG.le hb0]⟩
  have hE0 : 0 < E γ β G e1 e2 0 := by
    rw [E_zero]
    unfold Samuelson at hS
    linarith
  have hEb : E γ β G e1 e2 b < 0 := by
    unfold E
    have h1 : e1 - b = δ := by rw [hb]; ring
    have h2 : (e2 + G * b) ^ (-γ) ≤ e2 ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos he2 (by nlinarith [mul_nonneg hG.le hb0]) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_pos hβ hG).le
    rw [h1]
    linarith
  have hcont : ContinuousOn (fun s => E γ β G e1 e2 s) (Icc 0 b) := by
    intro x hx
    have hF := feas_between G e1 e2 0 b x hG hx.1 hx.2 hF0 hFb
    have c1 : ContinuousAt (fun s : ℝ => e1 - s) x := by fun_prop
    have c2 : ContinuousAt (fun s : ℝ => e2 + G * s) x := by fun_prop
    have : ContinuousAt (fun s => -(e1 - s) ^ (-γ) + β * G * (e2 + G * s) ^ (-γ)) x :=
      ((c1.rpow_const (Or.inl hF.1.ne')).neg).add
        (continuousAt_const.mul (c2.rpow_const (Or.inl hF.2.ne')))
    exact this.continuousWithinAt
  obtain ⟨m, hm, hm0⟩ := intermediate_value_Icc' hb0 hcont ⟨hEb.le, hE0.le⟩
  have hFm := feas_between G e1 e2 0 b m hG hm.1 hm.2 hF0 hFb
  have hmpos : 0 < m := by
    rcases hm.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hm0
      linarith
  exact ⟨m, hmpos, hFm, hm0⟩

/-- In a stationary monetary equilibrium the Euler equation holds. -/
theorem euler_of_eq (γ β G e1 e2 m : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hG : 0 < G) (he2 : 0 < e2)
    (h : IsMonEq u β G e1 e2 m) : Feas G e1 e2 m ∧ E γ β G e1 e2 m = 0 := by
  obtain ⟨hm0, hm1, hopt⟩ := h
  have hFm := feas_nonneg G e1 e2 m hG he2 hm0.le hm1
  refine ⟨hFm, ?_⟩
  have hloc : IsLocalMax (fun s => U u β G e1 e2 s) m := by
    filter_upwards [Ioo_mem_nhds hm0 hm1] with s hs
    exact hopt s hs.1.le hs.2
  exact hloc.hasDerivAt_eq_zero (hasDeriv_U γ β G e1 e2 m u hu hFm)

/-- **Existence of a stationary monetary equilibrium iff the Samuelson condition holds.** -/
theorem exists_iff (γ β G e1 e2 : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he1 : 0 < e1) (he2 : 0 < e2) :
    (∃ m, IsMonEq u β G e1 e2 m) ↔ Samuelson γ β G e1 e2 := by
  constructor
  · rintro ⟨m, h⟩
    have hm0 := h.1
    obtain ⟨hFm, hEm⟩ := euler_of_eq γ β G e1 e2 m u hu hG he2 h
    have hF0 : Feas G e1 e2 0 := feas_nonneg G e1 e2 0 hG he2 le_rfl he1
    have := E_anti γ β G e1 e2 0 m hγ hβ hG hm0 hF0 hFm
    rw [E_zero] at this
    unfold Samuelson
    linarith
  · intro hS
    obtain ⟨m, hm0, hFm, hEm⟩ := exists_root γ β G e1 e2 hγ hβ hG he1 he2 hS
    refine ⟨m, hm0, by linarith [hFm.1], fun s hs hs' => ?_⟩
    exact optimal γ β G e1 e2 m s u hu hγ hβ hG hFm hEm (feas_nonneg G e1 e2 s hG he2 hs hs')

/-- **The stationary monetary equilibrium is unique.** -/
theorem mon_eq_unique (γ β G e1 e2 m m' : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he2 : 0 < e2) (h : IsMonEq u β G e1 e2 m) (h' : IsMonEq u β G e1 e2 m') : m = m' := by
  obtain ⟨hF, hE⟩ := euler_of_eq γ β G e1 e2 m u hu hG he2 h
  obtain ⟨hF', hE'⟩ := euler_of_eq γ β G e1 e2 m' u hu hG he2 h'
  exact root_unique γ β G e1 e2 m m' hγ hβ hG hF hF' hE hE'

/-- **Welfare**: every generation strictly prefers the monetary steady state to autarky, and the
initial old consume more than their endowment. -/
theorem welfare (γ β G e1 e2 m : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he1 : 0 < e1) (he2 : 0 < e2) (h : IsMonEq u β G e1 e2 m) :
    u e1 + β * u e2 < U u β G e1 e2 m ∧ e2 < e2 + G * m := by
  have hm0 := h.1
  obtain ⟨hFm, hEm⟩ := euler_of_eq γ β G e1 e2 m u hu hG he2 h
  have hF0 : Feas G e1 e2 0 := feas_nonneg G e1 e2 0 hG he2 le_rfl he1
  have := strict_opt γ β G e1 e2 m 0 u hu hγ hβ hG hFm hEm hF0 hm0.ne
  unfold U at this
  simp only [sub_zero, mul_zero, add_zero] at this
  exact ⟨this, by nlinarith [mul_pos hG hm0]⟩

end OLGMoney

end

#print axioms OLGMoney.price_clears
#print axioms OLGMoney.price_return
#print axioms OLGMoney.E_anti
#print axioms OLGMoney.strict_opt
#print axioms OLGMoney.optimal
#print axioms OLGMoney.root_unique
#print axioms OLGMoney.exists_root
#print axioms OLGMoney.euler_of_eq
#print axioms OLGMoney.exists_iff
#print axioms OLGMoney.mon_eq_unique
#print axioms OLGMoney.welfare
