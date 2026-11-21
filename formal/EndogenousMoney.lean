import Mathlib

/-!
# Stage 377: a growing money supply, its welfare cost, and a money supply that responds to
# real balances

Stage 369 treated a fixed stock of fiat money in the stationary overlapping-generations
economy. This file lets the money stock grow, `M (t + 1) = (1 + μ) M t` with `μ > −1`, the new
money being handed out lump-sum to the old, and then lets the growth rate respond to the state
of the economy through a rule `μ = f m`.

Setting (as in stage 369): generations of relative size `G > 0`, endowments `e1, e2 > 0`,
lifetime utility `u (c₁) + β u (c₂)` with `β > 0` and `u' c = c ^ (−γ)`, `γ > 0`. Write
`R = G / (1 + μ)` (`ret`) and `τ = μ R m` (`tr`). A young household takes the price path and the
transfer `τ` as given and chooses real balances `s`: it consumes `e1 − s` young and
`e2 + τ + R s` old.

* `price_return`, `young_balances`, `own_money`, `transfer_value`, `old_total`: along the
  stationary path `p t = M t / (N t m)` the money market clears, money returns `R`, the transfer
  is worth `τ` per old person, and an old person's total real wealth from money is `G m`.
* `cons_id`: `e2 + τ + R m = e2 + G m`, so the stationary allocation is feasible.
* **`eq_iff`**: `m` is a stationary monetary equilibrium (optimal choice among all feasible
  non-negative holdings, given `τ`) iff `0 < m < e1` and
  `(e1 − m) ^ (−γ) = β R (e2 + G m) ^ (−γ)`.
* **`exists_iff`**: one exists iff `e1 ^ (−γ) < β (G / (1 + μ)) e2 ^ (−γ)`; enough money
  growth (inflation) destroys the value of money.
* **`eq_unique`**: it is unique.
* **`balances_anti`**: real balances strictly fall as `μ` rises (the inflation tax).
* **`golden_rule`**: steady-state welfare `u (e1 − m) + β u (e2 + G m)` is highest at `μ = 0`:
  for every `μ`, welfare at the `μ`-equilibrium is at most welfare at the `μ = 0` equilibrium, and
  strictly below it when `μ ≠ 0`. So with lump-sum transfers to the old, neither inflation nor
  deflation (a Friedman-rule contraction) improves on a constant money stock in steady state.
* **`feedback_exists`**: let the growth rate respond to real balances, `μ = f m`, with `f`
  continuous on `[0, e1]` and `f > −1` there. If `e1 ^ (−γ) < β (G / (1 + f 0)) e2 ^ (−γ)`, there
  is a stationary equilibrium `m` with money growing at `f m`. **`feedback_unique`**: if `f` is
  non-decreasing (money grows faster when balances are higher), it is unique.

Reading: money that pays no interest and whose supply grows, at a fixed rate or by a rule
that responds to the economy, has a value pinned down by the Euler equation; growth of the
money supply works as a tax on money holders, and in steady state the best constant rule is
to keep the stock fixed.

Limits: stationary equilibria only (no transition paths, no stability). New money is paid
lump-sum to the old; other injection schemes (to the young, proportional to holdings, through
government spending or lending) are not treated. The welfare result compares steady states
for the newborn generations only and ignores the initial old. The feedback rule depends on
current real balances only; for `f` that falls with balances uniqueness is not proved. There
is no inside (bank) money, credit or interest, so this is not a model of money created by
lending.
-/

noncomputable section

open Set Filter Topology

namespace EndogenousMoney

/-! ## The household problem (stage 369, with a general return and old-age income) -/

/-- Lifetime utility with return `R` and old-age income `y` when holding real balances `s`. -/
def U (u : ℝ → ℝ) (β R e1 y s : ℝ) : ℝ := u (e1 - s) + β * u (y + R * s)

/-- The Euler expression (derivative of `U` in `s`). -/
def E (γ β R e1 y s : ℝ) : ℝ := -(e1 - s) ^ (-γ) + β * R * (y + R * s) ^ (-γ)

/-- Both consumptions are positive. -/
def Feas (R e1 y s : ℝ) : Prop := 0 < e1 - s ∧ 0 < y + R * s

theorem E_anti (γ β R e1 y s t : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hst : s < t)
    (hs : Feas R e1 y s) (ht : Feas R e1 y t) : E γ β R e1 y t < E γ β R e1 y s := by
  unfold E
  have h1 := Real.rpow_lt_rpow_of_neg ht.1 (by linarith : e1 - t < e1 - s) (by linarith : -γ < 0)
  have h2 := Real.rpow_lt_rpow_of_neg hs.2
    (by linarith [mul_lt_mul_of_pos_left hst hR] : y + R * s < y + R * t) (by linarith : -γ < 0)
  have h3 := mul_lt_mul_of_pos_left h2 (mul_pos hβ hR)
  linarith

theorem feas_between (R e1 y s t x : ℝ) (hR : 0 < R) (h1 : s ≤ x) (h2 : x ≤ t)
    (hs : Feas R e1 y s) (ht : Feas R e1 y t) : Feas R e1 y x :=
  ⟨by linarith [ht.1], by linarith [hs.2, mul_le_mul_of_nonneg_left h1 hR.le]⟩

theorem hasDeriv_U (γ β R e1 y x : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hF : Feas R e1 y x) :
    HasDerivAt (fun s => U u β R e1 y s) (E γ β R e1 y x) x := by
  have h1 : HasDerivAt (fun s => e1 - s) (-1) x := (hasDerivAt_id' x).const_sub e1
  have h2 : HasDerivAt (fun s => y + R * s) R x :=
    (((hasDerivAt_id' x).const_mul R).const_add y).congr_deriv (mul_one R)
  have a := (hu _ hF.1).comp x h1
  have b := ((hu _ hF.2).comp x h2).const_mul β
  unfold U E
  exact (a.add b).congr_deriv (by ring)

/-- A zero of the Euler expression is the strict maximiser of lifetime utility. -/
theorem strict_opt (γ β R e1 y m s : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R)
    (hFm : Feas R e1 y m) (hE : E γ β R e1 y m = 0) (hFs : Feas R e1 y s) (hne : s ≠ m) :
    U u β R e1 y s < U u β R e1 y m := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : ∀ x ∈ Icc s m, HasDerivAt (fun t => U u β R e1 y t) (E γ β R e1 y x) x :=
      fun x hx => hasDeriv_U γ β R e1 y x u hu (feas_between R e1 y s m x hR hx.1 hx.2 hFs hFm)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun t => U u β R e1 y t)
      (fun x => E γ β R e1 y x) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between R e1 y s m c hR hc.1.le hc.2.le hFs hFm
    have hEc : 0 < E γ β R e1 y c := by
      have := E_anti γ β R e1 y c m hγ hβ hR hc.2 hcF hFm
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_pos hEc (sub_pos.2 h)]
  · have hd : ∀ x ∈ Icc m s, HasDerivAt (fun t => U u β R e1 y t) (E γ β R e1 y x) x :=
      fun x hx => hasDeriv_U γ β R e1 y x u hu (feas_between R e1 y m s x hR hx.1 hx.2 hFm hFs)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun t => U u β R e1 y t)
      (fun x => E γ β R e1 y x) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between R e1 y m s c hR hc.1.le hc.2.le hFm hFs
    have hEc : E γ β R e1 y c < 0 := by
      have := E_anti γ β R e1 y m c hγ hβ hR hc.1 hFm hcF
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_neg_of_neg_of_pos hEc (sub_pos.2 h)]

theorem optimal (γ β R e1 y m s : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R)
    (hFm : Feas R e1 y m) (hE : E γ β R e1 y m = 0) (hFs : Feas R e1 y s) :
    U u β R e1 y s ≤ U u β R e1 y m := by
  by_cases h : s = m
  · rw [h]
  · exact (strict_opt γ β R e1 y m s u hu hγ hβ hR hFm hE hFs h).le

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

/-! ## Money growth: prices, transfers and feasibility -/

/-- The gross real return on money when the stock grows at rate `μ`. -/
def ret (G μ : ℝ) : ℝ := G / (1 + μ)

/-- The real lump-sum transfer per old person. -/
def tr (G μ m : ℝ) : ℝ := μ * ret G μ * m

def Mstock (M0 μ : ℝ) (t : ℕ) : ℝ := M0 * (1 + μ) ^ t

def Npop (N0 G : ℝ) (t : ℕ) : ℝ := N0 * G ^ t

/-- The stationary price level: the young of date `t` hold real balances `m` each. -/
def price (M0 N0 G μ m : ℝ) (t : ℕ) : ℝ := Mstock M0 μ t / (Npop N0 G t * m)

theorem ret_pos (G μ : ℝ) (hG : 0 < G) (hμ : -1 < μ) : 0 < ret G μ :=
  div_pos hG (by linarith)

/-- The young hold the whole money stock: real balances per young person are `m`. -/
theorem young_balances (M0 N0 G μ m : ℝ) (hM : 0 < M0) (hN : 0 < N0) (hG : 0 < G)
    (hμ : -1 < μ) (hm : 0 < m) (t : ℕ) :
    Mstock M0 μ t / Npop N0 G t / price M0 N0 G μ m t = m := by
  have h1 : 0 < (1 + μ) ^ t := pow_pos (by linarith) t
  have h2 : 0 < G ^ t := pow_pos hG t
  unfold price Mstock Npop
  field_simp

/-- **Money returns `G / (1 + μ)`**: `p t / p (t + 1) = R`. -/
theorem price_return (M0 N0 G μ m : ℝ) (hM : 0 < M0) (hN : 0 < N0) (hG : 0 < G)
    (hμ : -1 < μ) (hm : 0 < m) (t : ℕ) :
    price M0 N0 G μ m t / price M0 N0 G μ m (t + 1) = ret G μ := by
  have h0 : 0 < 1 + μ := by linarith
  have h1 : 0 < (1 + μ) ^ t := pow_pos h0 t
  have h2 : 0 < G ^ t := pow_pos hG t
  unfold price Mstock Npop ret
  rw [pow_succ, pow_succ]
  field_simp

/-- The money an old person bought when young is worth `R m`. -/
theorem own_money (M0 N0 G μ m : ℝ) (hM : 0 < M0) (hN : 0 < N0) (hG : 0 < G)
    (hμ : -1 < μ) (hm : 0 < m) (t : ℕ) :
    Mstock M0 μ t / Npop N0 G t / price M0 N0 G μ m (t + 1) = ret G μ * m := by
  have h0 : 0 < 1 + μ := by linarith
  have h1 : 0 < (1 + μ) ^ t := pow_pos h0 t
  have h2 : 0 < G ^ t := pow_pos hG t
  unfold price Mstock Npop ret
  rw [pow_succ, pow_succ]
  field_simp

/-- The new money, shared among the old, is worth `τ = μ R m` per old person. -/
theorem transfer_value (M0 N0 G μ m : ℝ) (hM : 0 < M0) (hN : 0 < N0) (hG : 0 < G)
    (hμ : -1 < μ) (hm : 0 < m) (t : ℕ) :
    (Mstock M0 μ (t + 1) - Mstock M0 μ t) / Npop N0 G t / price M0 N0 G μ m (t + 1) =
      tr G μ m := by
  have h0 : 0 < 1 + μ := by linarith
  have h1 : 0 < (1 + μ) ^ t := pow_pos h0 t
  have h2 : 0 < G ^ t := pow_pos hG t
  unfold price Mstock Npop tr ret
  rw [pow_succ, pow_succ]
  field_simp
  ring

/-- Real wealth from money of an old person is `G m`. -/
theorem cons_id (G μ y m : ℝ) (hμ : -1 < μ) : y + tr G μ m + ret G μ * m = y + G * m := by
  have h : (1 + μ) * ret G μ = G := by
    have hne : (1 + μ) ≠ 0 := ne_of_gt (by linarith)
    unfold ret
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
  calc y + tr G μ m + ret G μ * m = y + ((1 + μ) * ret G μ) * m := by unfold tr; ring
    _ = y + G * m := by rw [h]

theorem old_total (M0 N0 G μ m : ℝ) (hM : 0 < M0) (hN : 0 < N0) (hG : 0 < G)
    (hμ : -1 < μ) (hm : 0 < m) (t : ℕ) :
    Mstock M0 μ t / Npop N0 G t / price M0 N0 G μ m (t + 1) +
      (Mstock M0 μ (t + 1) - Mstock M0 μ t) / Npop N0 G t / price M0 N0 G μ m (t + 1) =
      G * m := by
  rw [own_money M0 N0 G μ m hM hN hG hμ hm, transfer_value M0 N0 G μ m hM hN hG hμ hm]
  have := cons_id G μ 0 m hμ
  linarith

/-! ## Stationary equilibrium with money growth -/

/-- The equilibrium Euler expression with money growth `μ`. -/
def Φ (γ β G μ e1 e2 m : ℝ) : ℝ := -(e1 - m) ^ (-γ) + β * ret G μ * (e2 + G * m) ^ (-γ)

/-- A stationary monetary equilibrium with money growth `μ`: positive real balances `m`, and `m`
is optimal for a young household that takes the transfer `τ = μ R m` as given. -/
def IsEq (u : ℝ → ℝ) (β G μ e1 e2 m : ℝ) : Prop :=
  0 < m ∧ m < e1 ∧ ∀ s, 0 ≤ s → Feas (ret G μ) e1 (e2 + tr G μ m) s →
    U u β (ret G μ) e1 (e2 + tr G μ m) s ≤ U u β (ret G μ) e1 (e2 + tr G μ m) m

theorem E_at (γ β G μ e1 e2 m : ℝ) (hμ : -1 < μ) :
    E γ β (ret G μ) e1 (e2 + tr G μ m) m = Φ γ β G μ e1 e2 m := by
  unfold E Φ
  rw [cons_id G μ e2 m hμ]

theorem Φ_anti (γ β G μ e1 e2 s t : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G) (hμ : -1 < μ)
    (hst : s < t) (ht : 0 < e1 - t) (hs : 0 < e2 + G * s) :
    Φ γ β G μ e1 e2 t < Φ γ β G μ e1 e2 s := by
  unfold Φ
  have h1 := Real.rpow_lt_rpow_of_neg ht (by linarith : e1 - t < e1 - s) (by linarith : -γ < 0)
  have h2 := Real.rpow_lt_rpow_of_neg hs
    (by linarith [mul_lt_mul_of_pos_left hst hG] : e2 + G * s < e2 + G * t) (by linarith : -γ < 0)
  have h3 := mul_lt_mul_of_pos_left h2 (mul_pos hβ (ret_pos G μ hG hμ))
  linarith

theorem Φ_zero (γ β G μ e1 e2 : ℝ) :
    Φ γ β G μ e1 e2 0 = -e1 ^ (-γ) + β * ret G μ * e2 ^ (-γ) := by
  unfold Φ
  simp only [sub_zero, mul_zero, add_zero]

/-- **Equilibrium is the Euler equation.** -/
theorem eq_iff (γ β G μ e1 e2 m : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hμ : -1 < μ) (he2 : 0 < e2) :
    IsEq u β G μ e1 e2 m ↔ 0 < m ∧ m < e1 ∧ Φ γ β G μ e1 e2 m = 0 := by
  have hR := ret_pos G μ hG hμ
  have hFm : 0 < m → m < e1 → Feas (ret G μ) e1 (e2 + tr G μ m) m := fun hm0 hm1 =>
    ⟨by linarith, by rw [cons_id G μ e2 m hμ]; have := mul_pos hG hm0; linarith⟩
  constructor
  · rintro ⟨hm0, hm1, hopt⟩
    refine ⟨hm0, hm1, ?_⟩
    rw [← E_at γ β G μ e1 e2 m hμ]
    have hpos : 0 < e2 + tr G μ m + ret G μ * m := (hFm hm0 hm1).2
    have hc : ContinuousAt (fun s => e2 + tr G μ m + ret G μ * s) m := by fun_prop
    have hev : ∀ᶠ s in 𝓝 m, 0 < e2 + tr G μ m + ret G μ * s := hc.eventually_const_lt hpos
    have hloc : IsLocalMax (fun s => U u β (ret G μ) e1 (e2 + tr G μ m) s) m := by
      filter_upwards [Ioo_mem_nhds hm0 hm1, hev] with s hs hs2
      exact hopt s hs.1.le ⟨by linarith [hs.2], hs2⟩
    exact hloc.hasDerivAt_eq_zero (hasDeriv_U γ β _ e1 _ m u hu (hFm hm0 hm1))
  · rintro ⟨hm0, hm1, hΦ⟩
    refine ⟨hm0, hm1, fun s _ hFs => ?_⟩
    exact optimal γ β _ e1 _ m s u hu hγ hβ hR (hFm hm0 hm1)
      (by rw [E_at γ β G μ e1 e2 m hμ]; exact hΦ) hFs

/-- **The equilibrium is unique.** -/
theorem eq_unique (γ β G μ e1 e2 m m' : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hμ : -1 < μ) (he2 : 0 < e2) (h : IsEq u β G μ e1 e2 m) (h' : IsEq u β G μ e1 e2 m') :
    m = m' := by
  obtain ⟨hm0, hm1, hΦ⟩ := (eq_iff γ β G μ e1 e2 m u hu hγ hβ hG hμ he2).1 h
  obtain ⟨hm0', hm1', hΦ'⟩ := (eq_iff γ β G μ e1 e2 m' u hu hγ hβ hG hμ he2).1 h'
  rcases lt_trichotomy m m' with hl | hl | hl
  · have := Φ_anti γ β G μ e1 e2 m m' hγ hβ hG hμ hl (by linarith)
      (by have := mul_pos hG hm0; linarith)
    linarith
  · exact hl
  · have := Φ_anti γ β G μ e1 e2 m' m hγ hβ hG hμ hl (by linarith)
      (by have := mul_pos hG hm0'; linarith)
    linarith

/-- **Real balances fall as money growth rises** (the inflation tax). -/
theorem balances_anti (γ β G μ μ' e1 e2 m m' : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hμ : -1 < μ) (hμμ : μ < μ') (he2 : 0 < e2) (h : IsEq u β G μ e1 e2 m)
    (h' : IsEq u β G μ' e1 e2 m') : m' < m := by
  have hμ' : -1 < μ' := by linarith
  obtain ⟨hm0, hm1, hΦ⟩ := (eq_iff γ β G μ e1 e2 m u hu hγ hβ hG hμ he2).1 h
  obtain ⟨hm0', hm1', hΦ'⟩ := (eq_iff γ β G μ' e1 e2 m' u hu hγ hβ hG hμ' he2).1 h'
  have hR : ret G μ' < ret G μ := by
    unfold ret
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left hμμ hG]
  have hX : 0 < (e2 + G * m') ^ (-γ) :=
    Real.rpow_pos_of_pos (by have := mul_pos hG hm0'; linarith) _
  have key : 0 < Φ γ β G μ e1 e2 m' := by
    unfold Φ at hΦ' ⊢
    have := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hR hβ) hX
    linarith
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hl | hl
  · have := Φ_anti γ β G μ e1 e2 m m' hγ hβ hG hμ hl (by linarith)
      (by have := mul_pos hG hm0; linarith)
    linarith
  · rw [← hl] at key
    linarith

/-- **The golden rule**: among stationary equilibria, steady-state welfare is highest with a
constant money stock, and strictly lower for any `μ ≠ 0`. -/
theorem golden_rule (γ β G μ e1 e2 m0 m : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hμ : -1 < μ) (he2 : 0 < e2) (h0 : IsEq u β G 0 e1 e2 m0) (h : IsEq u β G μ e1 e2 m) :
    U u β G e1 e2 m ≤ U u β G e1 e2 m0 ∧ (μ ≠ 0 → U u β G e1 e2 m < U u β G e1 e2 m0) := by
  have h01 : (-1 : ℝ) < 0 := by norm_num
  obtain ⟨hm00, hm01, hΦ0⟩ := (eq_iff γ β G 0 e1 e2 m0 u hu hγ hβ hG h01 he2).1 h0
  obtain ⟨hm0, hm1, -⟩ := (eq_iff γ β G μ e1 e2 m u hu hγ hβ hG hμ he2).1 h
  have hr : ret G 0 = G := by
    unfold ret
    simp
  have hE0 : E γ β G e1 e2 m0 = 0 := by
    unfold Φ at hΦ0
    rw [hr] at hΦ0
    unfold E
    exact hΦ0
  have hF0 : Feas G e1 e2 m0 := ⟨by linarith, by have := mul_pos hG hm00; linarith⟩
  have hFm : Feas G e1 e2 m := ⟨by linarith, by have := mul_pos hG hm0; linarith⟩
  refine ⟨optimal γ β G e1 e2 m0 m u hu hγ hβ hG hF0 hE0 hFm, fun hne => ?_⟩
  have hmm : m ≠ m0 := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact (balances_anti γ β G μ 0 e1 e2 m m0 u hu hγ hβ hG hμ hl he2 h h0).ne'
    · exact (balances_anti γ β G 0 μ e1 e2 m0 m u hu hγ hβ hG h01 hl he2 h0 h).ne
  exact strict_opt γ β G e1 e2 m0 m u hu hγ hβ hG hF0 hE0 hFm hmm

/-! ## A money supply that responds to real balances -/

/-- **Existence with a feedback rule.** If money grows at rate `f m` when real balances are `m`,
with `f` continuous and above `−1` on `[0, e1]`, and the Samuelson condition holds at the rate
`f 0`, there is a stationary equilibrium. -/
theorem feedback_exists (γ β G e1 e2 : ℝ) (f : ℝ → ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he1 : 0 < e1) (he2 : 0 < e2) (hf : ContinuousOn f (Icc 0 e1))
    (hf1 : ∀ m ∈ Icc 0 e1, -1 < f m) (hS : e1 ^ (-γ) < β * ret G (f 0) * e2 ^ (-γ)) :
    ∃ m, IsEq u β G (f m) e1 e2 m := by
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 he1.le) hf
  set κ := 1 + f x0 with hκ
  have hκ0 : 0 < κ := by linarith [hf1 x0 hx0]
  have hκle : ∀ m ∈ Icc 0 e1, κ ≤ 1 + f m := fun m hm => by
    have := isMinOn_iff.1 hmin m hm
    linarith
  have hRle : ∀ m ∈ Icc 0 e1, ret G (f m) ≤ G / κ := fun m hm => by
    unfold ret
    rw [div_le_div_iff₀ (by linarith [hf1 m hm]) hκ0]
    exact mul_le_mul_of_nonneg_left (hκle m hm) hG.le
  have hK : 0 ≤ β * (G / κ) * e2 ^ (-γ) :=
    mul_nonneg (mul_nonneg hβ.le (div_nonneg hG.le hκ0.le)) (Real.rpow_nonneg he2.le _)
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta e1 _ γ he1 hK hγ
  set b := e1 - δ with hb
  have hb0 : 0 ≤ b := by linarith
  have hbI : Icc 0 b ⊆ Icc 0 e1 := Icc_subset_Icc le_rfl (by linarith)
  have h0I : (0 : ℝ) ∈ Icc 0 e1 := ⟨le_rfl, he1.le⟩
  have hbI' : b ∈ Icc 0 e1 := ⟨hb0, by linarith⟩
  have hΨ0 : 0 < Φ γ β G (f 0) e1 e2 0 := by
    rw [Φ_zero]
    linarith
  have hΨb : Φ γ β G (f b) e1 e2 b < 0 := by
    unfold Φ
    have h1 : e1 - b = δ := by rw [hb]; ring
    have h2 : (e2 + G * b) ^ (-γ) ≤ e2 ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos he2 (by nlinarith [mul_nonneg hG.le hb0]) (by linarith)
    have h3 : β * ret G (f b) * (e2 + G * b) ^ (-γ) ≤ β * (G / κ) * e2 ^ (-γ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hRle b hbI') hβ.le) h2
        (Real.rpow_nonneg (by nlinarith [mul_nonneg hG.le hb0]) _)
        (mul_nonneg hβ.le (div_nonneg hG.le hκ0.le))
    rw [h1]
    linarith
  have hfb : ContinuousOn f (Icc 0 b) := hf.mono hbI
  have hcont : ContinuousOn (fun m => Φ γ β G (f m) e1 e2 m) (Icc 0 b) := by
    unfold Φ ret
    refine ContinuousOn.add ?_ ?_
    · exact ((by fun_prop : ContinuousOn (fun x : ℝ => e1 - x) (Icc 0 b)).rpow_const
        fun x hx => Or.inl (ne_of_gt (by linarith [hx.2]))).neg
    · refine (continuousOn_const.mul (continuousOn_const.div (continuousOn_const.add hfb)
        fun x hx => by
          show (1 : ℝ) + f x ≠ 0
          exact ne_of_gt (by linarith [hf1 x (hbI hx)]))).mul ?_
      exact (by fun_prop : ContinuousOn (fun x : ℝ => e2 + G * x) (Icc 0 b)).rpow_const
        fun x hx => Or.inl (ne_of_gt (by nlinarith [mul_nonneg hG.le hx.1]))
  obtain ⟨m, hm, hm0⟩ := intermediate_value_Icc' hb0 hcont ⟨hΨb.le, hΨ0.le⟩
  have hmpos : 0 < m := by
    rcases hm.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hm0
      linarith
  have hmI : m ∈ Icc 0 e1 := hbI hm
  exact ⟨m, (eq_iff γ β G (f m) e1 e2 m u hu hγ hβ hG (hf1 m hmI) he2).2
    ⟨hmpos, by linarith [hm.2], hm0⟩⟩

theorem feedback_anti (γ β G e1 e2 : ℝ) (f : ℝ → ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he2 : 0 < e2) (hfm : MonotoneOn f (Icc 0 e1)) (hf1 : ∀ m ∈ Icc 0 e1, -1 < f m)
    (s t : ℝ) (hs : s ∈ Icc 0 e1) (ht : t ∈ Icc 0 e1) (hte : t < e1) (hst : s < t) :
    Φ γ β G (f t) e1 e2 t < Φ γ β G (f s) e1 e2 s := by
  unfold Φ ret
  have hs0 : 0 < e2 + G * s := by nlinarith [mul_nonneg hG.le hs.1]
  have h1 := Real.rpow_lt_rpow_of_neg (by linarith : 0 < e1 - t) (by linarith : e1 - t < e1 - s)
    (by linarith : -γ < 0)
  have hX : (e2 + G * t) ^ (-γ) ≤ (e2 + G * s) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos hs0 (by nlinarith [mul_lt_mul_of_pos_left hst hG])
      (by linarith)
  have hps : 0 < 1 + f s := by linarith [hf1 s hs]
  have hpt : 0 < 1 + f t := by linarith [hf1 t ht]
  have hR : G / (1 + f t) ≤ G / (1 + f s) := by
    rw [div_le_div_iff₀ hpt hps]
    exact mul_le_mul_of_nonneg_left (by linarith [hfm hs ht hst.le]) hG.le
  have h2 : β * (G / (1 + f t)) * (e2 + G * t) ^ (-γ) ≤ β * (G / (1 + f s)) * (e2 + G * s) ^ (-γ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hR hβ.le) hX
      (Real.rpow_nonneg (by nlinarith [mul_nonneg hG.le ht.1]) _)
      (mul_nonneg hβ.le (div_nonneg hG.le hps.le))
  linarith

/-- **Uniqueness with a non-decreasing feedback rule.** -/
theorem feedback_unique (γ β G e1 e2 m m' : ℝ) (f : ℝ → ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (he2 : 0 < e2) (hfm : MonotoneOn f (Icc 0 e1)) (hf1 : ∀ m ∈ Icc 0 e1, -1 < f m)
    (h : IsEq u β G (f m) e1 e2 m) (h' : IsEq u β G (f m') e1 e2 m') : m = m' := by
  have hmI : m ∈ Icc 0 e1 := ⟨h.1.le, h.2.1.le⟩
  have hmI' : m' ∈ Icc 0 e1 := ⟨h'.1.le, h'.2.1.le⟩
  obtain ⟨-, hm1, hΦ⟩ := (eq_iff γ β G (f m) e1 e2 m u hu hγ hβ hG (hf1 m hmI) he2).1 h
  obtain ⟨-, hm1', hΦ'⟩ := (eq_iff γ β G (f m') e1 e2 m' u hu hγ hβ hG (hf1 m' hmI') he2).1 h'
  rcases lt_trichotomy m m' with hl | hl | hl
  · have := feedback_anti γ β G e1 e2 f hγ hβ hG he2 hfm hf1 m m' hmI hmI' hm1' hl
    linarith
  · exact hl
  · have := feedback_anti γ β G e1 e2 f hγ hβ hG he2 hfm hf1 m' m hmI' hmI hm1 hl
    linarith

/-- **Existence iff the growth-adjusted Samuelson condition holds.** -/
theorem exists_iff (γ β G μ e1 e2 : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hγ : 0 < γ) (hβ : 0 < β) (hG : 0 < G)
    (hμ : -1 < μ) (he1 : 0 < e1) (he2 : 0 < e2) :
    (∃ m, IsEq u β G μ e1 e2 m) ↔ e1 ^ (-γ) < β * ret G μ * e2 ^ (-γ) := by
  constructor
  · rintro ⟨m, h⟩
    obtain ⟨hm0, hm1, hΦ⟩ := (eq_iff γ β G μ e1 e2 m u hu hγ hβ hG hμ he2).1 h
    have := Φ_anti γ β G μ e1 e2 0 m hγ hβ hG hμ hm0 (by linarith) (by rw [mul_zero, add_zero]; exact he2)
    rw [Φ_zero] at this
    linarith
  · intro hS
    exact feedback_exists γ β G e1 e2 (fun _ => μ) u hu hγ hβ hG he1 he2 continuousOn_const
      (fun _ _ => hμ) hS

end EndogenousMoney

end

#print axioms EndogenousMoney.young_balances
#print axioms EndogenousMoney.price_return
#print axioms EndogenousMoney.own_money
#print axioms EndogenousMoney.transfer_value
#print axioms EndogenousMoney.old_total
#print axioms EndogenousMoney.eq_iff
#print axioms EndogenousMoney.exists_iff
#print axioms EndogenousMoney.eq_unique
#print axioms EndogenousMoney.balances_anti
#print axioms EndogenousMoney.golden_rule
#print axioms EndogenousMoney.feedback_exists
#print axioms EndogenousMoney.feedback_unique
