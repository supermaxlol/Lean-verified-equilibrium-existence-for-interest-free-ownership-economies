import Mathlib

/-!
Stage 313: random audits with a bounded penalty.

Stage 308 used the maximal penalty (full surrender on a detected lie).  Here a detected misreport
costs the true repayment plus a fine `F ≥ 0`.  A borrower in state `s` who reports `m` saves the gap
`D = R s − R m` unless audited (probability `a`).

* `ic_iff`: truthful reporting holds iff `(1 − a)·D ≤ a·F`.
* `need`: the least audit probability is `D / (D + F)`; it suffices (`ic_of_need`) and is necessary
  (`need_le_of_ic`).
* `need_lt_one`: with any positive fine, audits need not be certain.
* `need_zero_fine`: with no fine and a positive gap, audits must be certain (`a = 1`).
* `need_anti`, `need_tendsto`: the requirement falls as the fine grows and tends to `0` (Becker).
* `need_mono`: the requirement rises with the gap.
* Contracts: under profit sharing `R = θ y` the gap is at most `θ·Δ` where `Δ` bounds output
  differences, so a uniform audit probability `θΔ/(θΔ + F)` suffices (`ps_uniform_ic`); its cost
  `c·θΔ/(θΔ + F)` is below debt's `c·G/(G + F)` whenever `θΔ ≤ G` (`ps_cost_le_debt`), and tends to
  `0` as `θ → 0` (`ps_need_tendsto`).

Honest limits: the fine is assumed collectable (no limited liability on the fine); audit
commitment is assumed; uniform audit rules, not the optimal report-dependent rule.
-/

open Filter Topology

noncomputable section

namespace BoundedPenalty

/-- Lying payoff `(1 − a)(y + D) + a(y − F)` versus truthful payoff `y` (net of true repayment). -/
theorem ic_iff (a D F y : ℝ) :
    (1 - a) * (y + D) + a * (y - F) ≤ y ↔ (1 - a) * D ≤ a * F := by
  constructor <;> intro h <;> nlinarith

/-- Least audit probability. -/
def need (D F : ℝ) : ℝ := D / (D + F)

theorem ic_of_need (a D F : ℝ) (hD : 0 ≤ D) (hF : 0 < F) (ha : need D F ≤ a) :
    (1 - a) * D ≤ a * F := by
  unfold need at ha
  rw [div_le_iff₀ (by linarith)] at ha
  nlinarith

theorem need_le_of_ic (a D F : ℝ) (hD : 0 ≤ D) (hF : 0 < F) (h : (1 - a) * D ≤ a * F) :
    need D F ≤ a := by
  unfold need
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem need_nonneg (D F : ℝ) (hD : 0 ≤ D) (hF : 0 < F) : 0 ≤ need D F :=
  div_nonneg hD (by linarith)

theorem need_lt_one (D F : ℝ) (hD : 0 ≤ D) (hF : 0 < F) : need D F < 1 := by
  unfold need
  rw [div_lt_one (by linarith)]
  linarith

theorem need_zero_fine (a D : ℝ) (hD : 0 < D) (h : (1 - a) * D ≤ a * 0) : 1 ≤ a := by
  rw [mul_zero] at h
  by_contra hc
  have : 0 < (1 - a) * D := mul_pos (by linarith) hD
  linarith

theorem need_anti (D F F' : ℝ) (hD : 0 ≤ D) (hF : 0 < F) (hFF : F ≤ F') :
    need D F' ≤ need D F := by
  unfold need
  exact div_le_div_of_nonneg_left hD (by linarith) (by linarith)

theorem need_mono (D D' F : ℝ) (hD : 0 ≤ D) (hF : 0 < F) (hDD : D ≤ D') :
    need D F ≤ need D' F := by
  unfold need
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem need_tendsto (D : ℝ) : Tendsto (fun F => need D F) atTop (𝓝 0) := by
  unfold need
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ D tendsto_id)

/-- **Profit sharing with a uniform audit rule is incentive compatible.** -/
theorem ps_uniform_ic {S : Type*} (y : S → ℝ) (θ Δ F : ℝ) (hθ : 0 ≤ θ) (hF : 0 < F)
    (hΔ : ∀ s m, y s - y m ≤ Δ) (s m : S) (hgap : 0 ≤ θ * y s - θ * y m) :
    (1 - need (θ * Δ) F) * (θ * y s - θ * y m) ≤ need (θ * Δ) F * F := by
  have h1 : θ * y s - θ * y m ≤ θ * Δ := by
    have := mul_le_mul_of_nonneg_left (hΔ s m) hθ; linarith
  exact ic_of_need _ _ F hgap hF (need_mono _ _ F hgap hF h1)

theorem ps_cost_le_debt (c θ Δ G F : ℝ) (hc : 0 ≤ c) (hθΔ : 0 ≤ θ * Δ) (hF : 0 < F)
    (h : θ * Δ ≤ G) : c * need (θ * Δ) F ≤ c * need G F :=
  mul_le_mul_of_nonneg_left (need_mono _ _ F hθΔ hF h) hc

theorem ps_need_tendsto (Δ F : ℝ) (hF : 0 < F) :
    Tendsto (fun θ => need (θ * Δ) F) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun θ : ℝ => θ * Δ / (θ * Δ + F)) 0 := by
    apply ContinuousAt.div (continuousAt_id.mul continuousAt_const)
      ((continuousAt_id.mul continuousAt_const).add continuousAt_const)
    simp; exact hF.ne'
  have := hc.tendsto
  simp only [zero_mul, zero_div] at this
  exact this

end BoundedPenalty

end

#print axioms BoundedPenalty.ic_iff
#print axioms BoundedPenalty.ic_of_need
#print axioms BoundedPenalty.need_le_of_ic
#print axioms BoundedPenalty.need_nonneg
#print axioms BoundedPenalty.need_lt_one
#print axioms BoundedPenalty.need_zero_fine
#print axioms BoundedPenalty.need_anti
#print axioms BoundedPenalty.need_mono
#print axioms BoundedPenalty.need_tendsto
#print axioms BoundedPenalty.ps_uniform_ic
#print axioms BoundedPenalty.ps_cost_le_debt
#print axioms BoundedPenalty.ps_need_tendsto
