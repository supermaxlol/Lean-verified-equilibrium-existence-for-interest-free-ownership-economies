import Mathlib

/-!
Stage 251 (Study C): automation, ownership and issuance.

Revenue `R` is split between labour (share `lam`) and capital (share `1 - lam`).
Household `h` receives wage share `wsh h` and ownership share `θ h`.

* total household income equals `R` for every labour share: automation changes who
  receives purchasing power, not how much there is;
* as the labour share tends to zero, each household's income tends to its ownership
  share of revenue; an assetless household's income tends to zero;
* an ownership floor gives an income floor;
* issuance dynamics: if new ownership units are issued pro rata, shares never change;
  if any positive fraction `σ` of new units is issued equally, every share converges to
  the equal share.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace AutomationOwnership

variable {H : Type*} [Fintype H]

/-- Household income at labour share `lam`. -/
def income (wsh θ : H → ℝ) (R lam : ℝ) (h : H) : ℝ :=
  lam * wsh h * R + (1 - lam) * θ h * R

theorem income_total (wsh θ : H → ℝ) (R lam : ℝ) (hw : ∑ h, wsh h = 1)
    (hθ : ∑ h, θ h = 1) : ∑ h, income wsh θ R lam h = R := by
  simp only [income, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hw, hθ]
  ring

/-- As the labour share vanishes, income converges to the ownership share of revenue. -/
theorem income_tendsto (wsh θ : H → ℝ) (R : ℝ) (h : H) :
    Tendsto (fun lam => income wsh θ R lam h) (𝓝 0) (𝓝 (θ h * R)) := by
  have hc : Continuous (fun lam : ℝ => income wsh θ R lam h) := by
    unfold income
    fun_prop
  have h0 : income wsh θ R 0 h = θ h * R := by simp [income]
  rw [← h0]
  exact hc.tendsto 0

theorem assetless_income (wsh θ : H → ℝ) (R lam : ℝ) (h : H) (h0 : θ h = 0) :
    income wsh θ R lam h = lam * wsh h * R := by
  simp [income, h0]

/-- An assetless household's income vanishes with the labour share. -/
theorem assetless_tendsto_zero (wsh θ : H → ℝ) (R : ℝ) (h : H) (h0 : θ h = 0) :
    Tendsto (fun lam => income wsh θ R lam h) (𝓝 0) (𝓝 0) := by
  have := income_tendsto wsh θ R h
  rw [h0, zero_mul] at this
  exact this

/-- An ownership floor `m` guarantees an income floor `(1 - lam) * m * R`. -/
theorem income_floor (wsh θ : H → ℝ) (R lam m : ℝ) (h : H) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hw : 0 ≤ wsh h) (hR : 0 ≤ R) (hfloor : m ≤ θ h) :
    (1 - lam) * m * R ≤ income wsh θ R lam h := by
  unfold income
  have h1 : 0 ≤ lam * wsh h * R := mul_nonneg (mul_nonneg hlam0 hw) hR
  have h2 : (1 - lam) * m * R ≤ (1 - lam) * θ h * R :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor (by linarith)) hR
  linarith

/-! ### Issuance dynamics -/

/-- One period: the capital stock grows by the factor `1 + g`; a fraction `σ` of the new
units is issued equally (each household receiving the equal share `c`), the rest pro
rata to existing holdings. -/
def nextShare (g σ c x : ℝ) : ℝ := (x + g * ((1 - σ) * x + σ * c)) / (1 + g)

def shareAt (g σ c x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => nextShare g σ c (shareAt g σ c x0 t)

/-- Per-period contraction factor of the distance from the equal share. -/
def rate (g σ : ℝ) : ℝ := (1 + g * (1 - σ)) / (1 + g)

theorem nextShare_dev (g σ c x : ℝ) (hg : 1 + g ≠ 0) :
    nextShare g σ c x - c = rate g σ * (x - c) := by
  unfold nextShare rate
  field_simp
  ring

theorem shareAt_dev (g σ c x0 : ℝ) (hg : 1 + g ≠ 0) :
    ∀ t, shareAt g σ c x0 t - c = rate g σ ^ t * (x0 - c)
  | 0 => by simp [shareAt]
  | t + 1 => by
      rw [shareAt, nextShare_dev g σ c _ hg, shareAt_dev g σ c x0 hg t, pow_succ]
      ring

/-- Pro-rata issuance (`σ = 0`) leaves every ownership share unchanged forever. -/
theorem pro_rata_preserves (g c x0 : ℝ) (hg : 1 + g ≠ 0) (t : ℕ) :
    shareAt g 0 c x0 t = x0 := by
  have hr : rate g 0 = 1 := by
    unfold rate
    rw [sub_zero, mul_one]
    exact div_self hg
  have := shareAt_dev g 0 c x0 hg t
  rw [hr, one_pow, one_mul] at this
  linarith

theorem rate_lt_one (g σ : ℝ) (hg : 0 < g) (hσ : 0 < σ) : rate g σ < 1 := by
  unfold rate
  rw [div_lt_one (by linarith)]
  nlinarith [mul_pos hg hσ]

theorem rate_nonneg (g σ : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) : 0 ≤ rate g σ := by
  unfold rate
  apply div_nonneg
  · nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]
  · linarith

/-- If any positive fraction of new ownership is issued equally, every household's share
converges to the equal share, whatever the initial distribution. -/
theorem universal_issuance_converges (g σ c x0 : ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) : Tendsto (shareAt g σ c x0) atTop (𝓝 c) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (rate_nonneg g σ hg hσ1)
    (rate_lt_one g σ hg hσ)
  have h2 : Tendsto (fun t => rate g σ ^ t * (x0 - c) + c) atTop (𝓝 c) := by
    have := (hpow.mul_const (x0 - c)).add_const c
    simpa using this
  refine h2.congr (fun t => ?_)
  have := shareAt_dev g σ c x0 (by linarith) t
  linarith

end AutomationOwnership

end

#print axioms AutomationOwnership.income_total
#print axioms AutomationOwnership.income_tendsto
#print axioms AutomationOwnership.assetless_income
#print axioms AutomationOwnership.assetless_tendsto_zero
#print axioms AutomationOwnership.income_floor
#print axioms AutomationOwnership.nextShare_dev
#print axioms AutomationOwnership.shareAt_dev
#print axioms AutomationOwnership.pro_rata_preserves
#print axioms AutomationOwnership.rate_lt_one
#print axioms AutomationOwnership.rate_nonneg
#print axioms AutomationOwnership.universal_issuance_converges
