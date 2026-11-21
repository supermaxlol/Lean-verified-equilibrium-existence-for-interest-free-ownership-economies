import Mathlib

/-!
# Stage 358: the Ramsey rule is paid by ownership, not by a loan

The Euler (Ramsey) condition for consumption, `u'(C_t) = β R u'(C_{t+1})`, says that waiting
must earn the gross real return `R`. It is often read as proving that *interest* must be
positive. This file shows the required return is delivered in full by ownership of output.

* `ramsey_log`: with `u = log` and consumption growing by `1 + g`, the Euler condition holds
  exactly when `R = (1 + g) / β`.
* `ramsey_crra`: with marginal utility `c ^ (-γ)`, exactly when `R = (1 + g) ^ γ / β`.
* `ramsey_example`: `β = 0.96`, `g = 0.05`: `R = 1.09375` (a 9.375% real return).
* `ownership_clearing`: in a growing ownership economy where households consume `1 − β` of
  wealth and all output `D_t` is paid as dividends, the units market clears at value
  `Q_t = β D_t / (1 − β)`.
* `ownership_pays_ramsey`: the gross return on ownership, `(Q_{t+1} + D_{t+1}) / Q_t`, is then
  `(1 + g) / β`: exactly the Ramsey return for log utility. No lending contract is involved.
* `ownership_real`: a common change in the price level leaves the real return on ownership
  unchanged, because units are claims on output.
* `fisher_real`: a fixed nominal claim earns the real gross return `(1 + i) / (1 + π)`.
* `fisher_example_deflation`: `r = 5%`, `π = −3%` gives nominal `1 + i = 1.0185`.
* `hyperinflation_example`: `i = 50%`, `π = 500%` gives a real return of `0.25` on a nominal
  claim, while ownership still pays the Ramsey return.
* `cash_dominated`: whenever a nominal claim's real return is below the ownership return, a
  saver strictly gains by holding ownership instead.

Reading: impatience and diminishing marginal utility give waiting a positive time value. That
value is a return on ownership; it does not require an interest-bearing loan, and a claim on
output keeps it under inflation, where a nominal claim loses it.
-/

noncomputable section

namespace RamseyOwnership

/-- **Ramsey rule, log utility.** -/
theorem ramsey_log (β R g C : ℝ) (hβ : 0 < β) (hC : 0 < C) (hg : 0 < 1 + g) :
    1 / C = β * R * (1 / ((1 + g) * C)) ↔ R = (1 + g) / β := by
  have hC' : (1 + g) * C ≠ 0 := (mul_pos hg hC).ne'
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hβ.ne']
    linarith
  · intro h
    rw [h]
    field_simp

/-- **Ramsey rule, CRRA.** -/
theorem ramsey_crra (β R g C γ : ℝ) (hβ : 0 < β) (hC : 0 < C) (hg : 0 < 1 + g) :
    C ^ (-γ) = β * R * ((1 + g) * C) ^ (-γ) ↔ R = (1 + g) ^ γ / β := by
  have hgC : ((1 + g) * C) ^ (-γ) = (1 + g) ^ (-γ) * C ^ (-γ) :=
    Real.mul_rpow hg.le hC.le
  have hCp : 0 < C ^ (-γ) := Real.rpow_pos_of_pos hC _
  have hgp : 0 < (1 + g) ^ γ := Real.rpow_pos_of_pos hg _
  have hinv : (1 + g) ^ (-γ) = ((1 + g) ^ γ)⁻¹ := Real.rpow_neg hg.le γ
  rw [hgC, hinv]
  constructor
  · intro h
    rw [eq_div_iff hβ.ne']
    have := h
    field_simp at this
    nlinarith [this]
  · intro h
    rw [h]
    field_simp

theorem ramsey_example : ((1:ℝ) + 0.05) / 0.96 = 1.09375 := by norm_num

/-- Units market clearing in a growing ownership economy. -/
theorem ownership_clearing (β Q D : ℝ) (hβ1 : β < 1) (h : (1 - β) * (Q + D) = D) :
    Q = β * D / (1 - β) := by
  have h1 : (0:ℝ) < 1 - β := by linarith
  rw [eq_div_iff h1.ne']
  linarith

/-- **Ownership pays the Ramsey return.** -/
theorem ownership_pays_ramsey (β g D : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hD : 0 < D)
    (hg : 0 < 1 + g) :
    (β * ((1 + g) * D) / (1 - β) + (1 + g) * D) / (β * D / (1 - β)) = (1 + g) / β := by
  have h1 : (1:ℝ) - β ≠ 0 := by linarith
  field_simp
  ring

/-- Ownership's real return does not depend on the price level. -/
theorem ownership_real (P P' Q Q' D' : ℝ) (hP : P ≠ 0) (hP' : P' ≠ 0) (hQ : Q ≠ 0) :
    (P' * (Q' + D')) / (P * Q) / (P' / P) = (Q' + D') / Q := by
  field_simp

/-- A fixed nominal claim's real gross return. -/
theorem fisher_real (i π : ℝ) (hπ : 0 < 1 + π) :
    (1 + i) / (1 + π) * (1 + π) = 1 + i := by
  field_simp

theorem fisher_example_deflation : ((1:ℝ) + 0.05) * (1 + (-0.03)) = 1.0185 := by norm_num

theorem hyperinflation_example : ((1:ℝ) + 0.5) / (1 + 5) = 0.25 := by norm_num

/-- **Cash is dominated** whenever its real return is below ownership's. -/
theorem cash_dominated (W ρ R : ℝ) (hW : 0 < W) (hlt : ρ < R) : ρ * W < R * W :=
  mul_lt_mul_of_pos_right hlt hW

end RamseyOwnership

end

#print axioms RamseyOwnership.ramsey_log
#print axioms RamseyOwnership.ramsey_crra
#print axioms RamseyOwnership.ramsey_example
#print axioms RamseyOwnership.ownership_clearing
#print axioms RamseyOwnership.ownership_pays_ramsey
#print axioms RamseyOwnership.ownership_real
#print axioms RamseyOwnership.fisher_real
#print axioms RamseyOwnership.fisher_example_deflation
#print axioms RamseyOwnership.hyperinflation_example
#print axioms RamseyOwnership.cash_dominated
