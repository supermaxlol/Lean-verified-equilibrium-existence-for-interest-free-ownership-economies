import Mathlib

/-!
# Stage 354: equity and debt with heterogeneous CRRA — the bond is traded

Stage 285: with a share of output and a bond paying one in every state, and a *common*
homothetic felicity, no household issues or holds the bond. This file treats different CRRA
coefficients `γ i` (marginal utility `c ^ (-γ i)`, which covers log and every power utility).

* `euler_necessary`: an interior optimum over all affordable `(θ, b)` satisfies the Euler
  condition `Σ π_s u'(c_s) (q_B Y_s − q_E) = 0` (from a local maximum along the budget line).
* `crra_euler_zero_bond`: at a zero bond position this gives
  `q_B E[Y^{1−γ}] = q_E E[Y^{−γ}]`.
* `cheb_strict`, `tilted_strict`: the tilted mean `E[Y^{1−γ}] / E[Y^{−γ}]` is strictly
  decreasing in `γ` when output takes two values with positive probability.
* `hetero_crra_debt_traded`: hence, at any prices where every household is at an interior
  optimum, if two households have different `γ`, some bond position is non-zero.
* `issuer_and_holder`, `hetero_crra_issuer_holder`: with bond market clearing `Σ b_i = 0`,
  some household issues the bond and another holds it.

Reading: under heterogeneous risk attitudes the fixed claim is not redundant; it is traded in
every equilibrium. With consumption at one date only, prices are relative and `q_B` can be
normalised to one, so the traded claim is a fixed repayment at par. This is about the
*shape* of the claim, not about interest.

Limits: one date, two assets, common beliefs `π`, interior consumption. Existence of the
incomplete-market equilibrium is not proved here; this is a property of any equilibrium that
exists. Only the direction (debt is traded) is shown, not the size of positions.
-/

open Finset Filter Topology

namespace HeteroCRRADebt

variable {S : Type*} [Fintype S]

/-- **Euler condition.** If `(θ, b)` is optimal among all `(θ', b')` with the same cost and
positive consumption, then `Σ π_s u'(c_s) (q_B Y_s − q_E) = 0`. -/
theorem euler_necessary (π Y : S → ℝ) (u u' : ℝ → ℝ) (hu : ∀ c > 0, HasDerivAt u (u' c) c)
    (qE qB θ b : ℝ) (hpos : ∀ s, 0 < θ * Y s + b)
    (hopt : ∀ θ' b', qE * θ' + qB * b' = qE * θ + qB * b → (∀ s, 0 < θ' * Y s + b') →
      ∑ s, π s * u (θ' * Y s + b') ≤ ∑ s, π s * u (θ * Y s + b)) :
    ∑ s, π s * (u' (θ * Y s + b) * (qB * Y s - qE)) = 0 := by
  have hd : HasDerivAt (fun t : ℝ => ∑ s, π s * u ((θ + t * qB) * Y s + (b - t * qE)))
      (∑ s, π s * (u' (θ * Y s + b) * (qB * Y s - qE))) 0 := by
    apply HasDerivAt.fun_sum
    intro s _
    have hin : HasDerivAt (fun t : ℝ => (θ + t * qB) * Y s + (b - t * qE)) (qB * Y s - qE) 0 :=
      ((((hasDerivAt_id' (x := (0:ℝ))).mul_const qB).const_add θ).mul_const (Y s)).add
        (((hasDerivAt_id' (x := (0:ℝ))).mul_const qE).const_sub b) |>.congr_deriv (by ring)
    have e0 : (θ + 0 * qB) * Y s + (b - 0 * qE) = θ * Y s + b := by ring
    have hout := hu _ (hpos s)
    rw [← e0] at hout
    have h := (hout.comp 0 hin).const_mul (π s)
    rw [e0] at h
    exact h
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ s, 0 < (θ + t * qB) * Y s + (b - t * qE) := by
    rw [Filter.eventually_all]
    intro s
    have hc : Continuous (fun t : ℝ => (θ + t * qB) * Y s + (b - t * qE)) := by fun_prop
    exact (hc.tendsto 0).eventually_const_lt (by simpa using hpos s)
  have hmax : IsLocalMax (fun t : ℝ => ∑ s, π s * u ((θ + t * qB) * Y s + (b - t * qE))) 0 :=
    hev.mono fun t ht => by
      simpa using hopt (θ + t * qB) (b - t * qE) (by ring) ht
  exact hmax.hasDerivAt_eq_zero hd

/-- At a zero bond position, the CRRA Euler condition fixes the price ratio. -/
theorem crra_euler_zero_bond (π Y : S → ℝ) (hY : ∀ s, 0 < Y s) (γ θ qE qB : ℝ) (hθ : 0 < θ)
    (h : ∑ s, π s * ((θ * Y s + 0) ^ (-γ) * (qB * Y s - qE)) = 0) :
    qB * (∑ s, π s * (Y s ^ (-γ) * Y s)) = qE * ∑ s, π s * Y s ^ (-γ) := by
  have e : ∀ s, π s * ((θ * Y s + 0) ^ (-γ) * (qB * Y s - qE)) =
      θ ^ (-γ) * (qB * (π s * (Y s ^ (-γ) * Y s)) - qE * (π s * Y s ^ (-γ))) := by
    intro s
    rw [add_zero, Real.mul_rpow hθ.le (hY s).le]
    ring
  rw [Finset.sum_congr rfl fun s _ => e s, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at h
  have hθg : 0 < θ ^ (-γ) := Real.rpow_pos_of_pos hθ _
  have := (mul_eq_zero.mp h).resolve_left hθg.ne'
  linarith

/-- **Chebyshev's sum inequality, strict.** If `r` is increasing in `Y` (strictly on strict
increases) and two states with positive weight have different `Y`, then
`(Σ a r)(Σ a Y) < (Σ a r Y)(Σ a)`. -/
theorem cheb_strict (a r Y : S → ℝ) (ha : ∀ s, 0 ≤ a s)
    (hmono : ∀ s t, Y s ≤ Y t → r s ≤ r t) (hsm : ∀ s t, Y s < Y t → r s < r t)
    (hvar : ∃ s t, 0 < a s ∧ 0 < a t ∧ Y s < Y t) :
    (∑ s, a s * r s) * (∑ s, a s * Y s) < (∑ s, a s * r s * Y s) * ∑ s, a s := by
  have key : ∑ s, ∑ t, a s * a t * ((r s - r t) * (Y s - Y t)) =
      2 * ((∑ s, a s * r s * Y s) * (∑ s, a s) - (∑ s, a s * r s) * (∑ s, a s * Y s)) := by
    have h1 : ∀ s t, a s * a t * ((r s - r t) * (Y s - Y t)) =
        a s * r s * Y s * a t - a s * r s * (a t * Y t) - a s * Y s * (a t * r t) +
          a s * (a t * r t * Y t) := by
      intro s t
      ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
    ring
  have hterm : ∀ s t, 0 ≤ a s * a t * ((r s - r t) * (Y s - Y t)) := by
    intro s t
    apply mul_nonneg (mul_nonneg (ha s) (ha t))
    rcases le_total (Y s) (Y t) with h | h
    · have := hmono s t h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have := hmono t s h
      exact mul_nonneg (by linarith) (by linarith)
  obtain ⟨s0, t0, hs0, ht0, hlt⟩ := hvar
  have hpos : 0 < ∑ s, ∑ t, a s * a t * ((r s - r t) * (Y s - Y t)) := by
    apply Finset.sum_pos' (fun s _ => Finset.sum_nonneg fun t _ => hterm s t)
    refine ⟨s0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun t _ => hterm s0 t)
    refine ⟨t0, Finset.mem_univ _, ?_⟩
    have hr := hsm s0 t0 hlt
    have : 0 < (r s0 - r t0) * (Y s0 - Y t0) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    exact mul_pos (mul_pos hs0 ht0) this
  linarith

/-- **The tilted mean `E[Y^{1−γ}] / E[Y^{−γ}]` is strictly decreasing in `γ`.** -/
theorem tilted_strict (π Y : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (hY : ∀ s, 0 < Y s)
    (hvar : ∃ s t, 0 < π s ∧ 0 < π t ∧ Y s < Y t) (γ1 γ2 : ℝ) (hγ : γ1 < γ2) :
    (∑ s, π s * (Y s ^ (-γ2) * Y s)) * (∑ s, π s * Y s ^ (-γ1)) <
      (∑ s, π s * (Y s ^ (-γ1) * Y s)) * (∑ s, π s * Y s ^ (-γ2)) := by
  have hsplit : ∀ s, Y s ^ (-γ1) = Y s ^ (-γ2) * Y s ^ (γ2 - γ1) := by
    intro s
    rw [← Real.rpow_add (hY s)]
    congr 1
    ring
  obtain ⟨s0, t0, hs0, ht0, hlt⟩ := hvar
  have h := cheb_strict (fun s => π s * Y s ^ (-γ2)) (fun s => Y s ^ (γ2 - γ1)) Y
    (fun s => mul_nonneg (hπ s) (Real.rpow_nonneg (hY s).le _))
    (fun s t hst => Real.rpow_le_rpow (hY s).le hst (by linarith))
    (fun s t hst => Real.rpow_lt_rpow (hY s).le hst (by linarith))
    ⟨s0, t0, mul_pos hs0 (Real.rpow_pos_of_pos (hY s0) _),
      mul_pos ht0 (Real.rpow_pos_of_pos (hY t0) _), hlt⟩
  beta_reduce at h
  have e1 : ∑ s, π s * Y s ^ (-γ2) * Y s ^ (γ2 - γ1) = ∑ s, π s * Y s ^ (-γ1) :=
    Finset.sum_congr rfl fun s _ => by rw [hsplit s]; ring
  have e2 : ∑ s, π s * Y s ^ (-γ2) * Y s = ∑ s, π s * (Y s ^ (-γ2) * Y s) :=
    Finset.sum_congr rfl fun s _ => by ring
  have e3 : ∑ s, π s * Y s ^ (-γ2) * Y s ^ (γ2 - γ1) * Y s =
      ∑ s, π s * (Y s ^ (-γ1) * Y s) :=
    Finset.sum_congr rfl fun s _ => by rw [hsplit s]; ring
  rw [e1, e2, e3] at h
  linarith

/-- **Heterogeneous CRRA: the bond is traded.** At prices `(q_E, q_B)` with `q_B > 0`, if
every household `i` (marginal utility `c ^ (-γ i)`) is at an interior optimum `(θ i, b i)`
and two households have different `γ`, then some bond position is non-zero. -/
theorem hetero_crra_debt_traded {I : Type*} (π Y : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hvar : ∃ s t, 0 < π s ∧ 0 < π t ∧ Y s < Y t) (qE qB : ℝ)
    (hqB : 0 < qB) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i, ∀ c > 0, HasDerivAt (u i) (c ^ (-γ i)) c)
    (θ b : I → ℝ) (hpos : ∀ i s, 0 < θ i * Y s + b i)
    (hopt : ∀ i θ' b', qE * θ' + qB * b' = qE * θ i + qB * b i → (∀ s, 0 < θ' * Y s + b') →
      ∑ s, π s * u i (θ' * Y s + b') ≤ ∑ s, π s * u i (θ i * Y s + b i))
    (hγ : ∃ i j, γ i < γ j) : ∃ i, b i ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨i, j, hij⟩ := hγ
  obtain ⟨s0, -, -, -, -⟩ := id hvar
  have hθ : ∀ k, 0 < θ k := by
    intro k
    have h1 := hpos k s0
    rw [hc k, add_zero] at h1
    by_contra hn
    push Not at hn
    nlinarith [hY s0]
  have euler : ∀ k, qB * (∑ s, π s * (Y s ^ (-γ k) * Y s)) =
      qE * ∑ s, π s * Y s ^ (-γ k) := by
    intro k
    have h := euler_necessary π Y (u k) (fun c => c ^ (-γ k)) (hu k) qE qB (θ k) (b k)
      (hpos k) (hopt k)
    rw [hc k] at h
    exact crra_euler_zero_bond π Y hY (γ k) (θ k) qE qB (hθ k) h
  have ht := tilted_strict π Y hπ hY hvar (γ i) (γ j) hij
  have ei := euler i
  have ej := euler j
  have h1 : qB * ((∑ s, π s * (Y s ^ (-γ i) * Y s)) * (∑ s, π s * Y s ^ (-γ j))) =
      qE * ((∑ s, π s * Y s ^ (-γ i)) * (∑ s, π s * Y s ^ (-γ j))) := by
    rw [← mul_assoc, ei]
    ring
  have h2 : qB * ((∑ s, π s * (Y s ^ (-γ j) * Y s)) * (∑ s, π s * Y s ^ (-γ i))) =
      qE * ((∑ s, π s * Y s ^ (-γ i)) * (∑ s, π s * Y s ^ (-γ j))) := by
    rw [← mul_assoc, ej]
    ring
  have h3 := mul_lt_mul_of_pos_left ht hqB
  linarith

/-- With market clearing, a non-zero position means someone issues and someone holds. -/
theorem issuer_and_holder {I : Type*} [Fintype I] (b : I → ℝ) (hb : ∑ i, b i = 0)
    (h : ∃ i, b i ≠ 0) : ∃ i j, b i < 0 ∧ 0 < b j := by
  obtain ⟨i, hi⟩ := h
  by_contra hc
  push Not at hc
  rcases lt_or_gt_of_ne hi with h1 | h1
  · have hall : ∀ j, 0 ≤ -b j := fun j => by linarith [hc i j h1]
    have h2 := Finset.single_le_sum (f := fun j => -b j) (fun j _ => hall j) (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib, hb] at h2
    linarith
  · have hall : ∀ j, 0 ≤ b j := fun j => by
      by_contra hn
      push Not at hn
      linarith [hc j i hn]
    have h2 := Finset.single_le_sum (f := b) (fun j _ => hall j) (Finset.mem_univ i)
    rw [hb] at h2
    linarith

/-- **Capstone.** With bond-market clearing and two different CRRA coefficients, in any
interior equilibrium some household issues the bond and another holds it. -/
theorem hetero_crra_issuer_holder {I : Type*} [Fintype I] (π Y : S → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hvar : ∃ s t, 0 < π s ∧ 0 < π t ∧ Y s < Y t) (qE qB : ℝ)
    (hqB : 0 < qB) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i, ∀ c > 0, HasDerivAt (u i) (c ^ (-γ i)) c)
    (θ b : I → ℝ) (hpos : ∀ i s, 0 < θ i * Y s + b i)
    (hopt : ∀ i θ' b', qE * θ' + qB * b' = qE * θ i + qB * b i → (∀ s, 0 < θ' * Y s + b') →
      ∑ s, π s * u i (θ' * Y s + b') ≤ ∑ s, π s * u i (θ i * Y s + b i))
    (hγ : ∃ i j, γ i < γ j) (hclear : ∑ i, b i = 0) : ∃ i j, b i < 0 ∧ 0 < b j :=
  issuer_and_holder b hclear
    (hetero_crra_debt_traded π Y hπ hY hvar qE qB hqB γ u hu θ b hpos hopt hγ)

end HeteroCRRADebt

#print axioms HeteroCRRADebt.euler_necessary
#print axioms HeteroCRRADebt.crra_euler_zero_bond
#print axioms HeteroCRRADebt.cheb_strict
#print axioms HeteroCRRADebt.tilted_strict
#print axioms HeteroCRRADebt.hetero_crra_debt_traded
#print axioms HeteroCRRADebt.issuer_and_holder
#print axioms HeteroCRRADebt.hetero_crra_issuer_holder
