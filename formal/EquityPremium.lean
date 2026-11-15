import Mathlib

/-!
Stage 271: the shadow riskless return is below the expected return on ownership.

Setting of stage 266: states `S`, probabilities `π s > 0` summing to one, output `Y s > 0`,
state prices `π s / Y s`.  The claim to all output costs one (stage 266, `equity_budget`),
so its expected gross return is `∑ s, π s * Y s`.  A claim paying one unit in every state
costs `∑ s, π s / Y s`, so its gross return is the reciprocal of that.

* `inv_tangent`, `inv_tangent_strict` — tangent-line bound for `1 / y`;
* `riskless_price_ge` — the sure claim costs at least `1 / E[Y]`;
* `premium_nonneg` — the riskless return is at most the expected return on ownership;
* `premium_pos` — strictly below it when output differs across two states.
-/

noncomputable section

open Finset BigOperators

namespace EquityPremium

variable {S : Type*} [Fintype S]

theorem inv_tangent (y μ : ℝ) (hy : 0 < y) (hμ : 0 < μ) :
    2 / μ - y * (1 / μ ^ 2) ≤ 1 / y := by
  have e : 1 / y - (2 / μ - y * (1 / μ ^ 2)) = (y - μ) ^ 2 / (y * μ ^ 2) := by
    field_simp
    ring
  have h0 : 0 ≤ (y - μ) ^ 2 / (y * μ ^ 2) := by positivity
  linarith

theorem inv_tangent_strict (y μ : ℝ) (hy : 0 < y) (hμ : 0 < μ) (hne : y ≠ μ) :
    2 / μ - y * (1 / μ ^ 2) < 1 / y := by
  have e : 1 / y - (2 / μ - y * (1 / μ ^ 2)) = (y - μ) ^ 2 / (y * μ ^ 2) := by
    field_simp
    ring
  have hsq : 0 < (y - μ) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have h0 : 0 < (y - μ) ^ 2 / (y * μ ^ 2) := div_pos hsq (by positivity)
  linarith

theorem tangent_sum (π Y : S → ℝ) (μ : ℝ) (hμ : 0 < μ) (hπ1 : ∑ s, π s = 1)
    (hμeq : ∑ s, π s * Y s = μ) :
    ∑ s, π s * (2 / μ - Y s * (1 / μ ^ 2)) = 1 / μ := by
  have e1 : ∀ s, π s * (2 / μ - Y s * (1 / μ ^ 2))
      = π s * (2 / μ) - π s * Y s * (1 / μ ^ 2) := fun s => by ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, hπ1, hμeq]
  field_simp
  ring

theorem mean_pos [Nonempty S] (π Y : S → ℝ) (hπ : ∀ s, 0 < π s) (hY : ∀ s, 0 < Y s) :
    0 < ∑ s, π s * Y s :=
  Finset.sum_pos (fun s _ => mul_pos (hπ s) (hY s)) Finset.univ_nonempty

/-- The sure claim costs at least the reciprocal of expected output. -/
theorem riskless_price_ge [Nonempty S] (π Y : S → ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) :
    1 / (∑ s, π s * Y s) ≤ ∑ s, π s / Y s := by
  have hμ := mean_pos π Y hπ hY
  have hterm : ∀ s, π s * (2 / (∑ t, π t * Y t) - Y s * (1 / (∑ t, π t * Y t) ^ 2))
      ≤ π s / Y s := by
    intro s
    have h := mul_le_mul_of_nonneg_left (inv_tangent (Y s) _ (hY s) hμ) (hπ s).le
    have e : π s * (1 / Y s) = π s / Y s := mul_one_div _ _
    rw [e] at h
    exact h
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rwa [tangent_sum π Y _ hμ hπ1 rfl] at hsum

/-- **The riskless return is at most the expected return on ownership.** -/
theorem premium_nonneg [Nonempty S] (π Y : S → ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) :
    1 / (∑ s, π s / Y s) ≤ ∑ s, π s * Y s := by
  have hμ := mean_pos π Y hπ hY
  have hq : 0 < ∑ s, π s / Y s :=
    Finset.sum_pos (fun s _ => div_pos (hπ s) (hY s)) Finset.univ_nonempty
  have h := riskless_price_ge π Y hπ hπ1 hY
  rw [div_le_iff₀ hμ] at h
  rw [div_le_iff₀ hq]
  linarith [mul_comm (∑ s, π s / Y s) (∑ s, π s * Y s)]

/-- **Strict premium.** If output differs across two states the riskless return is
strictly below the expected return on ownership. -/
theorem premium_pos [Nonempty S] (π Y : S → ℝ) (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) (hY : ∀ s, 0 < Y s) (s1 s2 : S) (hvar : Y s1 ≠ Y s2) :
    1 / (∑ s, π s / Y s) < ∑ s, π s * Y s := by
  have hμ := mean_pos π Y hπ hY
  have hq : 0 < ∑ s, π s / Y s :=
    Finset.sum_pos (fun s _ => div_pos (hπ s) (hY s)) Finset.univ_nonempty
  have hex : ∃ s0, Y s0 ≠ ∑ t, π t * Y t := by
    by_cases h1 : Y s1 = ∑ t, π t * Y t
    · exact ⟨s2, fun h2 => hvar (h1.trans h2.symm)⟩
    · exact ⟨s1, h1⟩
  obtain ⟨s0, hs0⟩ := hex
  have hterm : ∀ s, π s * (2 / (∑ t, π t * Y t) - Y s * (1 / (∑ t, π t * Y t) ^ 2))
      ≤ π s / Y s := by
    intro s
    have h := mul_le_mul_of_nonneg_left (inv_tangent (Y s) _ (hY s) hμ) (hπ s).le
    have e : π s * (1 / Y s) = π s / Y s := mul_one_div _ _
    rw [e] at h
    exact h
  have hstr : π s0 * (2 / (∑ t, π t * Y t) - Y s0 * (1 / (∑ t, π t * Y t) ^ 2))
      < π s0 / Y s0 := by
    have h := mul_lt_mul_of_pos_left (inv_tangent_strict (Y s0) _ (hY s0) hμ hs0) (hπ s0)
    have e : π s0 * (1 / Y s0) = π s0 / Y s0 := mul_one_div _ _
    rw [e] at h
    exact h
  have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
    ⟨s0, Finset.mem_univ s0, hstr⟩
  rw [tangent_sum π Y _ hμ hπ1 rfl, div_lt_iff₀ hμ] at hsum
  rw [div_lt_iff₀ hq]
  linarith [mul_comm (∑ s, π s / Y s) (∑ s, π s * Y s)]

end EquityPremium

end

#print axioms EquityPremium.inv_tangent
#print axioms EquityPremium.inv_tangent_strict
#print axioms EquityPremium.riskless_price_ge
#print axioms EquityPremium.premium_nonneg
#print axioms EquityPremium.premium_pos
