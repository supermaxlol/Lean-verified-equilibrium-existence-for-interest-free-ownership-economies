import Mathlib

/-!
Stage 253: issuance dynamics as a trading equilibrium.

Each period the stock of ownership units grows by the factor `1 + g`; a fraction `σ` of
the new units is issued equally (equal share `c`), the rest pro rata.  Each unit pays a
dividend `d`.  Households then trade units at price `q`.  A household with wealth `W`
chooses consumption and units to maximise `log c + β log a` (a two-period log saver).

* `saver_optimal` — the optimal plan spends `β/(1+β)` of wealth on units;
* `equilibrium_price` — market clearing pins the unit price at `β d / (1 + g)`;
* `post_trade_share`, `wealth_share` — after trade each household's share of units is
  its share of wealth, which is `eqNext` of its previous share;
* `equal_issuance_equilibrium_converges` — for any positive price, if `σ > 0` every
  share converges to the equal share; `pro_rata_equilibrium_preserves` — if `σ = 0`
  shares never move.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace EquilibriumIssuance

variable {H : Type*} [Fintype H]

/-- A log saver's optimal plan: consume `W/(1+β)`, hold `β W / ((1+β) q)` units. -/
theorem saver_optimal (β q W c a : ℝ) (hβ : 0 < β) (hq : 0 < q) (hW : 0 < W)
    (hc : 0 < c) (ha : 0 < a) (hbud : c + q * a ≤ W) :
    Real.log c + β * Real.log a
      ≤ Real.log (W / (1 + β)) + β * Real.log (β * W / ((1 + β) * q)) := by
  have h1β : 0 < 1 + β := by linarith
  have hcs : 0 < W / (1 + β) := div_pos hW h1β
  have has : 0 < β * W / ((1 + β) * q) := div_pos (mul_pos hβ hW) (mul_pos h1β hq)
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hcs)
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha has)
  rw [Real.log_div hc.ne' hcs.ne'] at h1
  rw [Real.log_div ha.ne' has.ne'] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
  have h4 : c / (W / (1 + β)) - 1 + β * (a / (β * W / ((1 + β) * q)) - 1)
      = (1 + β) * ((c + q * a) / W - 1) := by
    have := hβ.ne'
    have := hq.ne'
    have := hW.ne'
    have := h1β.ne'
    field_simp
    ring
  have h5 : (c + q * a) / W ≤ 1 := (div_le_one hW).2 hbud
  have h6 : (1 + β) * ((c + q * a) / W - 1) ≤ 0 := by
    nlinarith [mul_nonneg h1β.le (show (0:ℝ) ≤ 1 - (c + q * a) / W by linarith)]
  linarith

/-- Market clearing for units (savings `β/(1+β)` of total wealth equal the value of all
units) pins the unit price. -/
theorem equilibrium_price (β d g K q : ℝ) (hK : 0 < K) (hg : 0 < 1 + g)
    (hclear : β * (q * ((1 + g) * K) + d * K) = (1 + β) * q * ((1 + g) * K)) :
    q = β * d / (1 + g) := by
  have h : K * ((1 + g) * q - β * d) = 0 := by nlinarith
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd h0 hK.ne'
  · rw [eq_div_iff hg.ne']
    linarith

/-- With a common savings rule `a h = κ * W h`, the post-trade share of units equals the
share of wealth. -/
theorem post_trade_share (κ : ℝ) (W : H → ℝ) (K' : ℝ) (hκ : κ ≠ 0)
    (hWsum : ∑ h, W h ≠ 0) (hclear : ∑ h, κ * W h = K') (h : H) :
    κ * W h / K' = W h / ∑ k, W k := by
  rw [← hclear, ← Finset.mul_sum]
  field_simp

/-- Next-period share of a household that enters with share `x`. -/
def eqNext (q d g σ c x : ℝ) : ℝ :=
  (q * (x + g * ((1 - σ) * x + σ * c)) + d * x) / (q * (1 + g) + d)

/-- Total wealth after issuance and dividends. -/
theorem wealth_total (q d g σ c K : ℝ) (θ : H → ℝ) (hθ : ∑ h, θ h = 1)
    (hc : (Fintype.card H : ℝ) * c = 1) :
    ∑ h, (q * K * (θ h + g * ((1 - σ) * θ h + σ * c)) + d * K * θ h)
      = K * (q * (1 + g) + d) := by
  have h1 : ∀ h, q * K * (θ h + g * ((1 - σ) * θ h + σ * c)) + d * K * θ h
      = (q * K * (1 + g * (1 - σ)) + d * K) * θ h + q * K * g * σ * c := by
    intro h
    ring
  rw [Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_add_distrib, ← Finset.mul_sum, hθ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : (Fintype.card H : ℝ) * (q * K * g * σ * c)
      = q * K * g * σ * ((Fintype.card H : ℝ) * c) := by ring
  rw [h2, hc]
  ring

/-- A household's wealth share is `eqNext` of its previous ownership share. -/
theorem wealth_share (q d g σ c K x : ℝ) (hK : K ≠ 0) :
    (q * K * (x + g * ((1 - σ) * x + σ * c)) + d * K * x) / (K * (q * (1 + g) + d))
      = eqNext q d g σ c x := by
  have h1 : q * K * (x + g * ((1 - σ) * x + σ * c)) + d * K * x
      = K * (q * (x + g * ((1 - σ) * x + σ * c)) + d * x) := by ring
  rw [h1, mul_div_mul_left _ _ hK]
  rfl

def eqShareAt (q d g σ c x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => eqNext q d g σ c (eqShareAt q d g σ c x0 t)

/-- Contraction factor of the distance from the equal share under trade. -/
def eqRate (q d g σ : ℝ) : ℝ := (q * (1 + g * (1 - σ)) + d) / (q * (1 + g) + d)

theorem eqNext_dev (q d g σ c x : ℝ) (hden : q * (1 + g) + d ≠ 0) :
    eqNext q d g σ c x - c = eqRate q d g σ * (x - c) := by
  unfold eqNext eqRate
  field_simp
  ring

theorem eqShareAt_dev (q d g σ c x0 : ℝ) (hden : q * (1 + g) + d ≠ 0) :
    ∀ t, eqShareAt q d g σ c x0 t - c = eqRate q d g σ ^ t * (x0 - c)
  | 0 => by simp [eqShareAt]
  | t + 1 => by
      rw [eqShareAt, eqNext_dev q d g σ c _ hden, eqShareAt_dev q d g σ c x0 hden t, pow_succ]
      ring

theorem eqRate_lt_one (q d g σ : ℝ) (hq : 0 < q) (hd : 0 ≤ d) (hg : 0 < g) (hσ : 0 < σ) :
    eqRate q d g σ < 1 := by
  unfold eqRate
  have hden : 0 < q * (1 + g) + d := by nlinarith [mul_pos hq hg]
  rw [div_lt_one hden]
  nlinarith [mul_pos (mul_pos hq hg) hσ]

theorem eqRate_nonneg (q d g σ : ℝ) (hq : 0 < q) (hd : 0 ≤ d) (hg : 0 < g) (hσ1 : σ ≤ 1) :
    0 ≤ eqRate q d g σ := by
  unfold eqRate
  apply div_nonneg
  · nlinarith [mul_nonneg hq.le (mul_nonneg hg.le (sub_nonneg.2 hσ1))]
  · nlinarith [mul_pos hq hg]

/-- **Equilibrium convergence.** With trade at any positive unit price, if a positive
fraction of new units is issued equally, every household's share converges to the equal
share. -/
theorem equal_issuance_equilibrium_converges (q d g σ c x0 : ℝ) (hq : 0 < q) (hd : 0 ≤ d)
    (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (eqShareAt q d g σ c x0) atTop (𝓝 c) := by
  have hden : q * (1 + g) + d ≠ 0 := by nlinarith [mul_pos hq hg]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (eqRate_nonneg q d g σ hq hd hg hσ1)
    (eqRate_lt_one q d g σ hq hd hg hσ)
  have h2 : Tendsto (fun t => eqRate q d g σ ^ t * (x0 - c) + c) atTop (𝓝 c) := by
    have := (hpow.mul_const (x0 - c)).add_const c
    simpa using this
  refine h2.congr (fun t => ?_)
  have := eqShareAt_dev q d g σ c x0 hden t
  linarith

/-- **Pro-rata issuance under trade** leaves every share unchanged. -/
theorem pro_rata_equilibrium_preserves (q d g c x0 : ℝ) (hden : q * (1 + g) + d ≠ 0)
    (t : ℕ) : eqShareAt q d g 0 c x0 t = x0 := by
  have hr : eqRate q d g 0 = 1 := by
    unfold eqRate
    rw [sub_zero, mul_one]
    exact div_self hden
  have := eqShareAt_dev q d g 0 c x0 hden t
  rw [hr, one_pow, one_mul] at this
  linarith

end EquilibriumIssuance

end

#print axioms EquilibriumIssuance.saver_optimal
#print axioms EquilibriumIssuance.equilibrium_price
#print axioms EquilibriumIssuance.post_trade_share
#print axioms EquilibriumIssuance.wealth_total
#print axioms EquilibriumIssuance.wealth_share
#print axioms EquilibriumIssuance.eqNext_dev
#print axioms EquilibriumIssuance.eqShareAt_dev
#print axioms EquilibriumIssuance.eqRate_lt_one
#print axioms EquilibriumIssuance.eqRate_nonneg
#print axioms EquilibriumIssuance.equal_issuance_equilibrium_converges
#print axioms EquilibriumIssuance.pro_rata_equilibrium_preserves
