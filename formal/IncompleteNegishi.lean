import FixedPointTheorems.brouwer
import Mathlib

/-!
# Stage 386: existence of equilibrium with incomplete markets and heterogeneous CRRA

Stage 375 proved existence with many assets and heterogeneous CRRA only under COMPLETE markets;
stage 382 reduced the incomplete-markets case to a Negishi-type fixed point but left existence
open. This file closes that case for the one-period, one-good asset economy below, by the
Negishi method run on the marketed span.

Setup: households `i` with beliefs `π i s > 0`, marginal utility `c ^ (−γ i)` (`γ i > 0`) on
`c > 0`, endowment portfolios `e i` whose payoff is positive in every state; `J` assets with
arbitrary payoffs `d j s` (any number, possibly redundant, possibly incomplete). Consumption is
the portfolio payoff; budgets are `cost (qp ψ d) θ ≤ cost (qp ψ d) (e i)`.

* `planner_foc`, `common_projection`: at a weighted planner optimum on the marketed span, the
  weighted marginal utilities of all households have the same value against every marketed
  payoff.
* `equilibrium_of_planner`: a planner optimum with zero transfers is an equilibrium.
* `planner_exists`, `planner_unique`: for positive weights the planner optimum exists (a floor
  that the Inada property shows never binds, plus concavity) and is unique.
* `plan_floor`, `planner_continuous`: a uniform floor for weights in a band, and continuity of the
  planner allocation in the weights.
* `small_weight`: a household with small enough weight consumes below a given level in every
  state (compactness of marketed bundles plus the common projection).
* **`exists_equilibrium_incomplete`**: Brouwer on weights bounded away from zero gives zero
  transfers, hence positive state prices `ψ` and portfolios `θ` such that every asset market
  clears, each portfolio pays a positive amount in every state, is affordable, and is optimal
  among all affordable portfolios with positive payoff.

Limits: one period, one good, consumption equal to the portfolio payoff (no date-0 consumption),
CRRA-type marginal utility, positive endowment payoffs. Optimality is among portfolios with
strictly positive payoff in every state. With one good the incomplete-markets existence result is
classical (no rank-drop problem); this file is a machine-checked proof of it in this setting, not
a new theorem. Uniqueness of equilibrium, multi-good or multi-period economies, and nominal
assets are not covered.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace IncompleteNegishi

/-- Strict concavity, from marginal utility `c ^ (−γ)`. -/
theorem concave_lt (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) : u b - u a < a ^ (-γ) * (b - a) := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope u (fun x => x ^ (-γ)) h
      (fun x hx => (hu x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hu x (by linarith [hx.1]))
    have h1 : c ^ (-γ) < a ^ (-γ) := Real.rpow_lt_rpow_of_neg ha hc.1 (by linarith)
    rw [eq_div_iff (by linarith)] at hcs
    have := mul_lt_mul_of_pos_right h1 (sub_pos.2 h)
    linarith
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope u (fun x => x ^ (-γ)) h
      (fun x hx => (hu x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hu x (by linarith [hx.1]))
    have h1 : a ^ (-γ) < c ^ (-γ) :=
      Real.rpow_lt_rpow_of_neg (by linarith [hc.1]) hc.2 (by linarith)
    rw [eq_div_iff (by linarith)] at hcs
    have := mul_lt_mul_of_pos_right h1 (sub_pos.2 h)
    linarith

theorem concave_le (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    u b - u a ≤ a ^ (-γ) * (b - a) := by
  rcases eq_or_ne a b with h | h
  · subst h
    simp
  · exact (concave_lt γ hγ u hu ha hb h).le


/-- Strict midpoint concavity. -/
theorem mid_strict (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) : u a + u b < 2 * u ((a + b) / 2) := by
  have hm : 0 < (a + b) / 2 := by linarith
  have h1 : (a + b) / 2 ≠ a := by
    intro h
    apply hab
    linarith
  have h2 : (a + b) / 2 ≠ b := by
    intro h
    apply hab
    linarith
  have e1 := concave_lt γ hγ u hu hm ha h1
  have e2 := concave_lt γ hγ u hu hm hb h2
  have : ((a + b) / 2) ^ (-γ) * (a - (a + b) / 2) +
      ((a + b) / 2) ^ (-γ) * (b - (a + b) / 2) = 0 := by ring
  linarith

/-- A level small enough that its marginal utility exceeds any bound. -/
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

/-- A function with a derivative at `0` that is not exceeded just to the right of `0` has a
nonpositive derivative there. -/
theorem deriv_nonpos (g : ℝ → ℝ) (D : ℝ) (hg : HasDerivAt g D 0)
    (hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≤ g 0) : D ≤ 0 := by
  by_contra hD
  push Not at hD
  have h1 := hg.tendsto_slope_zero_right
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (g (0 + t) - g 0) :=
    h1.eventually (lt_mem_nhds hD)
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht1, ht2, ht3⟩ := (hle.and (h2.and h3)).exists
  rw [zero_add, smul_eq_mul] at ht2
  have h4 : 0 < t * (t⁻¹ * (g t - g 0)) := mul_pos ht3 ht2
  rw [← mul_assoc, mul_inv_cancel₀ ht3.ne', one_mul] at h4
  linarith

variable {S J : Type*} [Fintype S] [Fintype J]

/-- State-`s` payoff of portfolio `θ`. -/
def pay (d : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * d j s

/-- Cost of portfolio `θ` at prices `q`. -/
def cost (q θ : J → ℝ) : ℝ := ∑ j, q j * θ j

/-- Expected utility of portfolio `θ`. -/
def EU (π : S → ℝ) (u : ℝ → ℝ) (d : J → S → ℝ) (θ : J → ℝ) : ℝ := ∑ s, π s * u (pay d θ s)

/-- Arbitrage-free asset prices generated by state prices `ψ`. -/
def qp (ψ : S → ℝ) (d : J → S → ℝ) (j : J) : ℝ := ∑ s, ψ s * d j s

/-- Expected utility of a payoff vector. -/
def V (π : S → ℝ) (u : ℝ → ℝ) (x : S → ℝ) : ℝ := ∑ s, π s * u (x s)

/-- The marketed payoffs (the span of the asset payoffs). -/
def Mset (d : J → S → ℝ) : Set (S → ℝ) := Set.range fun θ : J → ℝ => fun s => pay d θ s

theorem cost_qp (ψ : S → ℝ) (d : J → S → ℝ) (θ : J → ℝ) :
    cost (qp ψ d) θ = ∑ s, ψ s * pay d θ s := by
  unfold cost qp pay
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
theorem pay_line (d : J → S → ℝ) (θ v : J → ℝ) (t : ℝ) (s : S) :
    pay d (fun i => θ i + t * v i) s = pay d θ s + t * pay d v s := by
  unfold pay
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
theorem pay_sub (d : J → S → ℝ) (θ e : J → ℝ) (s : S) :
    pay d (fun j => e j - θ j) s = pay d e s - pay d θ s := by
  unfold pay
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
theorem mem_Mset (d : J → S → ℝ) (θ : J → ℝ) : (fun s => pay d θ s) ∈ Mset d := by
  unfold Mset
  exact ⟨θ, rfl⟩

omit [Fintype S] in
theorem pay_add (d : J → S → ℝ) (a b : J → ℝ) (s : S) :
    pay d (a + b) s = pay d a s + pay d b s := by
  unfold pay
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_mul]

omit [Fintype S] in
theorem pay_sum {I : Type*} [Fintype I] (d : J → S → ℝ) (f : I → J → ℝ) (s : S) :
    pay d (∑ i, f i) s = ∑ i, pay d (f i) s := by
  unfold pay
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Concavity of expected utility in payoffs. -/
theorem V_diff_le (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (x y : S → ℝ) (hx : ∀ s, 0 < x s)
    (hy : ∀ s, 0 < y s) :
    V π u y - V π u x ≤ ∑ s, π s * x s ^ (-γ) * (y s - x s) := by
  unfold V
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := concave_le γ hγ u hu (hx s) (hy s)
  have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
  linarith

/-- `x` is an optimal marketed payoff at state prices `ψ` with wealth `W`. -/
def Opt (π : S → ℝ) (u : ℝ → ℝ) (d : J → S → ℝ) (ψ : S → ℝ) (W : ℝ) (x : S → ℝ) : Prop :=
  x ∈ Mset d ∧ (∀ s, 0 < x s) ∧ ∑ s, ψ s * x s ≤ W ∧
    ∀ y ∈ Mset d, (∀ s, 0 < y s) → ∑ s, ψ s * y s ≤ W → V π u y ≤ V π u x


/-- **Payoff clearing gives an equilibrium**, also with redundant assets: if optimal payoffs add
up to the aggregate endowment payoff at `ψ`, there are portfolios that clear every asset market
exactly, each paying the optimal payoff, each affordable at `q = qp ψ d`, and each optimal
among all affordable portfolios with positive consumption. -/
theorem equilibrium_of_payoff_clearing {I : Type*} [Fintype I] (i0 : I)
    (π : I → S → ℝ) (u : I → ℝ → ℝ) (d : J → S → ℝ) (e : I → J → ℝ) (ψ : S → ℝ)
    (x : I → S → ℝ) (hopt : ∀ i, Opt (π i) (u i) d ψ (∑ s, ψ s * pay d (e i) s) (x i))
    (hclear : ∀ s, ∑ i, x i s = ∑ i, pay d (e i) s) :
    ∃ θ : I → J → ℝ, ∑ i, θ i = ∑ i, e i ∧ ∀ i, (∀ s, pay d (θ i) s = x i s) ∧
      cost (qp ψ d) (θ i) ≤ cost (qp ψ d) (e i) ∧
      ∀ θ' : J → ℝ, cost (qp ψ d) θ' ≤ cost (qp ψ d) (e i) → (∀ s, 0 < pay d θ' s) →
        EU (π i) (u i) d θ' ≤ EU (π i) (u i) d (θ i) := by
  have hch : ∀ i, ∃ θ : J → ℝ, ∀ s, pay d θ s = x i s := fun i => by
    obtain ⟨θ, hθ⟩ := (hopt i).1
    exact ⟨θ, fun s => congrFun hθ s⟩
  choose θ0 hθ0 using hch
  set c : J → ℝ := ∑ i, e i - ∑ i, θ0 i with hc
  have hpc : ∀ s, pay d c s = 0 := fun s => by
    have h1 : pay d c s + pay d (∑ i, θ0 i) s = pay d (∑ i, e i) s := by
      rw [← pay_add, hc, sub_add_cancel]
    rw [pay_sum, pay_sum] at h1
    simp only [hθ0] at h1
    linarith [hclear s]
  refine ⟨fun i => θ0 i + if i = i0 then c else 0, ?_, fun i => ?_⟩
  · simp [Finset.sum_add_distrib, hc]
  · have hpay : ∀ s, pay d (θ0 i + if i = i0 then c else 0) s = x i s := fun s => by
      rw [pay_add, hθ0]
      split_ifs
      · rw [hpc, add_zero]
      · simp [pay]
    refine ⟨hpay, ?_, fun θ' hc' hp' => ?_⟩
    · rw [cost_qp, cost_qp]
      simp only [hpay]
      exact (hopt i).2.2.1
    · rw [cost_qp, cost_qp] at hc'
      have h := (hopt i).2.2.2 (fun s => pay d θ' s) (mem_Mset d θ') hp' hc'
      have e2 : EU (π i) (u i) d (θ0 i + if i = i0 then c else 0) = V (π i) (u i) (x i) := by
        unfold EU V
        simp only [hpay]
      exact h.trans_eq e2.symm


/-- The payoff map as a linear map. -/
def payL (d : J → S → ℝ) : (J → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun θ s := pay d θ s
  map_add' a b := by
    funext s
    simp only [pay, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext s
    simp only [pay, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

omit [Fintype S] in
/-- The marketed payoffs form a closed set. -/
theorem isClosed_Mset (d : J → S → ℝ) : IsClosed (Mset d) := by
  have h := Submodule.closed_of_finiteDimensional (LinearMap.range (payL d))
  exact h

/-! ## The marketed span is a subspace -/

omit [Fintype S] in
theorem Mset_zero (d : J → S → ℝ) : (fun _ : S => (0 : ℝ)) ∈ Mset d :=
  ⟨fun _ => 0, funext fun s => by simp [pay]⟩

omit [Fintype S] in
theorem Mset_sub (d : J → S → ℝ) (a b : S → ℝ) (ha : a ∈ Mset d) (hb : b ∈ Mset d) :
    (fun s => a s - b s) ∈ Mset d := by
  obtain ⟨θ, hθ⟩ := ha
  obtain ⟨ω, hω⟩ := hb
  refine ⟨fun j => θ j - ω j, funext fun s => ?_⟩
  have h1 : pay d θ s = a s := congrFun hθ s
  have h2 : pay d ω s = b s := congrFun hω s
  show pay d (fun j => θ j - ω j) s = a s - b s
  rw [pay_sub, h1, h2]

omit [Fintype S] in
theorem Mset_line (d : J → S → ℝ) (a b : S → ℝ) (t : ℝ) (ha : a ∈ Mset d) (hb : b ∈ Mset d) :
    (fun s => a s + t * b s) ∈ Mset d := by
  obtain ⟨θ, hθ⟩ := ha
  obtain ⟨ω, hω⟩ := hb
  refine ⟨fun j => θ j + t * ω j, funext fun s => ?_⟩
  have h1 : pay d θ s = a s := congrFun hθ s
  have h2 : pay d ω s = b s := congrFun hω s
  show pay d (fun j => θ j + t * ω j) s = a s + t * b s
  rw [pay_line, h1, h2]

/-- Derivative of expected utility along a direction `w`. -/
theorem V_dir (π : S → ℝ) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (x w : S → ℝ) (hx : ∀ s, 0 < x s) :
    HasDerivAt (fun t => V π u (fun s => x s + t * w s)) (∑ s, π s * x s ^ (-γ) * w s) 0 := by
  show HasDerivAt (fun t => ∑ s, π s * u (x s + t * w s)) _ 0
  apply HasDerivAt.fun_sum
  intro s _
  have hin : HasDerivAt (fun t => x s + t * w s) (w s) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (w s)).const_add (x s)).congr_deriv (one_mul _)
  have hpos : 0 < x s + 0 * w s := by simpa using hx s
  exact (((hu _ hpos).comp (0 : ℝ) hin).const_mul (π s)).congr_deriv
    (by rw [zero_mul, add_zero]; ring)

/-! ## The planner problem on the marketed span -/

variable {I : Type*} [Fintype I]

/-- Feasible allocations: marketed, strictly positive, adding up to the aggregate payoff `W`. -/
def Feas (d : J → S → ℝ) (W : S → ℝ) (y : I → S → ℝ) : Prop :=
  (∀ i, y i ∈ Mset d) ∧ (∀ i s, 0 < y i s) ∧ ∀ s, ∑ i, y i s = W s

/-- Weighted welfare. -/
def Wel (l : I → ℝ) (π : I → S → ℝ) (u : I → ℝ → ℝ) (y : I → S → ℝ) : ℝ :=
  ∑ i, l i * V (π i) (u i) (y i)

/-- `x` maximises weighted welfare among feasible allocations. -/
def PlanOpt (l : I → ℝ) (π : I → S → ℝ) (u : I → ℝ → ℝ) (d : J → S → ℝ) (W : S → ℝ)
    (x : I → S → ℝ) : Prop :=
  Feas d W x ∧ ∀ y, Feas d W y → Wel l π u y ≤ Wel l π u x

/-- Weighted marginal utility of household `i` in state `s`. -/
def mu (l : I → ℝ) (π : I → S → ℝ) (γ : I → ℝ) (x : I → S → ℝ) (i : I) (s : S) : ℝ :=
  l i * π i s * x i s ^ (-γ i)

omit [Fintype S] [Fintype I] in
theorem mu_pos (l : I → ℝ) (hl : ∀ i, 0 < l i) (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s)
    (γ : I → ℝ) (x : I → S → ℝ) (hx : ∀ i s, 0 < x i s) (i : I) (s : S) :
    0 < mu l π γ x i s :=
  mul_pos (mul_pos (hl i) (hπ i s)) (Real.rpow_pos_of_pos (hx i s) _)

/-- **First-order condition of the planner**: along every feasible direction (each household's
change marketed, changes adding up to zero) the weighted marginal utilities are orthogonal to
the change. -/
theorem planner_foc (l : I → ℝ) (π : I → S → ℝ) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (x : I → S → ℝ) (hx : PlanOpt l π u d W x) (w : I → S → ℝ) (hwM : ∀ i, w i ∈ Mset d)
    (hw0 : ∀ s, ∑ i, w i s = 0) :
    ∑ i, ∑ s, mu l π γ x i s * w i s = 0 := by
  obtain ⟨⟨hxM, hxp, hxW⟩, hopt⟩ := hx
  set g : ℝ → ℝ := fun t => Wel l π u (fun i s => x i s + t * w i s) with hg
  have hd : HasDerivAt g (∑ i, ∑ s, mu l π γ x i s * w i s) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (V_dir (π i) (γ i) (u i) (hu i) (x i) (w i) (hxp i)).const_mul (l i))
    refine h.congr_deriv ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by unfold mu; ring
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i s, 0 < x i s + t * w i s := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro s
    have hc : Continuous fun t : ℝ => x i s + t * w i s := by fun_prop
    have h0 : 0 < x i s + 0 * w i s := by simpa using hxp i s
    exact (hc.tendsto 0).eventually (lt_mem_nhds h0)
  have hmax : IsLocalMax g 0 := by
    refine hev.mono fun t ht => ?_
    have hF : Feas d W (fun i s => x i s + t * w i s) := by
      refine ⟨fun i => Mset_line d (x i) (w i) t (hxM i) (hwM i), ht, fun s => ?_⟩
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw0 s, hxW s, mul_zero, add_zero]
    have h0 : (fun i s => x i s + (0 : ℝ) * w i s) = x := by
      funext i s
      ring
    have := hopt _ hF
    simp only [hg, h0]
    exact this
  exact hmax.hasDerivAt_eq_zero hd

/-- **Common projection**: at a planner optimum, all households' weighted marginal utilities
agree on the marketed span. -/
theorem common_projection (l : I → ℝ) (π : I → S → ℝ) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (x : I → S → ℝ) (hx : PlanOpt l π u d W x) (i k : I) (v : S → ℝ) (hv : v ∈ Mset d) :
    ∑ s, mu l π γ x i s * v s = ∑ s, mu l π γ x k s * v s := by
  have hite : ∀ (m j : I), (fun s => if j = m then v s else 0) ∈ Mset d := by
    intro m j
    by_cases h : j = m
    · simpa [h] using hv
    · simpa [h] using Mset_zero d
  set w : I → S → ℝ := fun j s => (if j = i then v s else 0) - (if j = k then v s else 0)
    with hw
  have hwM : ∀ j, w j ∈ Mset d := fun j => Mset_sub d _ _ (hite i j) (hite k j)
  have hw0 : ∀ s, ∑ j, w j s = 0 := fun s => by
    simp [hw, Finset.sum_sub_distrib]
  have h := planner_foc l π γ u hu d W x hx w hwM hw0
  rw [Finset.sum_comm] at h
  simp only [hw, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  linarith

/-- **Supporting prices**: at a planner optimum with positive weights, the state prices
`ψ = mu i0` (household `i0`'s weighted marginal utility, strictly positive) support every
household's planner bundle: it is optimal among marketed positive bundles costing at most its
own value at `ψ`. -/
theorem planner_supports (l : I → ℝ) (hl : ∀ i, 0 < l i) (π : I → S → ℝ)
    (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (x : I → S → ℝ) (hx : PlanOpt l π u d W x) (i0 i : I) :
    Opt (π i) (u i) d (mu l π γ x i0) (∑ s, mu l π γ x i0 s * x i s) (x i) := by
  obtain ⟨⟨hxM, hxp, hxW⟩, hopt⟩ := hx
  refine ⟨hxM i, hxp i, le_refl _, fun y hyM hyp hyb => ?_⟩
  have hdiff := V_diff_le (π i) (fun s => (hπ i s).le) (γ i) (hγ i) (u i) (hu i) (x i) y
    (hxp i) hyp
  have hc := common_projection l π γ u hu d W x ⟨⟨hxM, hxp, hxW⟩, hopt⟩ i i0
    (fun s => y s - x i s) (Mset_sub d y (x i) hyM (hxM i))
  have e1 : ∑ s, mu l π γ x i s * (y s - x i s) =
      l i * ∑ s, π i s * x i s ^ (-γ i) * (y s - x i s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by unfold mu; ring
  have e2 : ∑ s, mu l π γ x i0 s * (y s - x i s) =
      ∑ s, mu l π γ x i0 s * y s - ∑ s, mu l π γ x i0 s * x i s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have h3 : l i * ∑ s, π i s * x i s ^ (-γ i) * (y s - x i s) ≤ 0 := by
    rw [← e1, hc, e2]
    linarith
  have h4 : ∑ s, π i s * x i s ^ (-γ i) * (y s - x i s) ≤ 0 := by
    by_contra hne
    have := mul_pos (hl i) (lt_of_not_ge hne)
    linarith
  linarith

/-- Transfers at the supporting prices add up to zero (clearing of the planner allocation). -/
theorem transfers_sum_zero (l : I → ℝ) (π : I → S → ℝ) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (d : J → S → ℝ) (e : I → J → ℝ) (x : I → S → ℝ)
    (hx : PlanOpt l π u d (fun s => ∑ i, pay d (e i) s) x) (i0 : I) :
    ∑ i, (∑ s, mu l π γ x i0 s * x i s - ∑ s, mu l π γ x i0 s * pay d (e i) s) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (f := fun i s => _ * pay d _ s)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero fun s _ => by rw [hx.1.2.2 s]; ring


/-! ## Existence and uniqueness of the planner optimum for positive weights -/

/-- Derivative of weighted welfare along a direction. -/
theorem Wel_dir (l : I → ℝ) (π : I → S → ℝ) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (x w : I → S → ℝ)
    (hx : ∀ i s, 0 < x i s) :
    HasDerivAt (fun t => Wel l π u (fun i s => x i s + t * w i s))
      (∑ i, ∑ s, mu l π γ x i s * w i s) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (V_dir (π i) (γ i) (u i) (hu i) (x i) (w i) (hx i)).const_mul (l i))
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by unfold mu; ring

/-- Concavity of weighted welfare. -/
theorem Wel_concave (l : I → ℝ) (hl : ∀ i, 0 ≤ l i) (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s)
    (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (x y : I → S → ℝ)
    (hx : ∀ i s, 0 < x i s) (hy : ∀ i s, 0 < y i s) :
    Wel l π u y - Wel l π u x ≤ ∑ i, ∑ s, mu l π γ x i s * (y i s - x i s) := by
  unfold Wel
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := V_diff_le (π i) (fun s => (hπ i s).le) (γ i) (hγ i) (u i) (hu i) (x i) (y i)
    (hx i) (hy i)
  have h2 := mul_le_mul_of_nonneg_left h (hl i)
  have e : l i * ∑ s, π i s * x i s ^ (-γ i) * (y i s - x i s) =
      ∑ s, mu l π γ x i s * (y i s - x i s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by unfold mu; ring
  rw [← e]
  linarith

/-- **The planner optimum is unique** for positive weights (strict concavity). -/
theorem planner_unique (l : I → ℝ) (hl : ∀ i, 0 < l i) (π : I → S → ℝ)
    (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (x x' : I → S → ℝ) (hx : PlanOpt l π u d W x) (hx' : PlanOpt l π u d W x') : x = x' := by
  by_contra hne
  obtain ⟨i0, s0, h0⟩ : ∃ i s, x i s ≠ x' i s := by
    by_contra h
    apply hne
    funext i s
    by_contra h'
    exact h ⟨i, s, h'⟩
  set m : I → S → ℝ := fun i s => (x i s + x' i s) / 2 with hm
  have hmF : Feas d W m := by
    refine ⟨fun i => ?_, fun i s => by simp only [hm]; linarith [hx.1.2.1 i s, hx'.1.2.1 i s], fun s => ?_⟩
    · have := Mset_line d (x i) (fun s => x' i s - x i s) (1 / 2) (hx.1.1 i)
        (Mset_sub d (x' i) (x i) (hx'.1.1 i) (hx.1.1 i))
      convert this using 1
      funext s
      simp only [hm]
      ring
    · simp only [hm, ← Finset.sum_div, Finset.sum_add_distrib, hx.1.2.2 s, hx'.1.2.2 s]
      ring
  have hstrict : Wel l π u x + Wel l π u x' < 2 * Wel l π u m := by
    unfold Wel V
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    have key : ∀ i s, π i s * u i (x i s) + π i s * u i (x' i s) ≤
        2 * (π i s * u i (m i s)) := fun i s => by
      rcases eq_or_ne (x i s) (x' i s) with h | h
      · simp only [hm, h, add_self_div_two]
        linarith
      · have := mul_le_mul_of_nonneg_left (mid_strict (γ i) (hγ i) (u i) (hu i)
          (hx.1.2.1 i s) (hx'.1.2.1 i s) h).le (hπ i s).le
        simp only [hm]
        linarith
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have := mul_le_mul_of_nonneg_left (key i s) (hl i).le
      linarith
    · rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ _, ?_⟩
      · have := mul_le_mul_of_nonneg_left (key i0 s) (hl i0).le
        linarith
      · have hs := mul_lt_mul_of_pos_left (mid_strict (γ i0) (hγ i0) (u i0) (hu i0)
          (hx.1.2.1 i0 s0) (hx'.1.2.1 i0 s0) h0) (hπ i0 s0)
        have := mul_lt_mul_of_pos_left hs (hl i0)
        simp only [hm]
        linarith
  have a1 := hx.2 m hmF
  have a2 := hx.2 x' hx'.1
  have a3 := hx'.2 x hx.1
  linarith

/-- **The planner optimum exists** for positive weights, on the marketed span, for any
strictly positive marketed aggregate `W`. The proof maximises welfare over the compact set of
feasible allocations with a floor `δ`, uses the Inada property of CRRA marginal utility to show
the floor does not bind, and concavity to pass from the floor set to all feasible
allocations. -/
theorem planner_exists [Nonempty I] [Nonempty S] (l : I → ℝ) (hl : ∀ i, 0 < l i)
    (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i)
    (u : I → ℝ → ℝ) (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c)
    (d : J → S → ℝ) (W : S → ℝ) (hWM : W ∈ Mset d) (hWp : ∀ s, 0 < W s) :
    ∃ x, PlanOpt l π u d W x := by
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  obtain ⟨s1, -, hs1⟩ := Finset.exists_min_image Finset.univ W Finset.univ_nonempty
  set zm : ℝ := W s1 / n with hzm_def
  have hzm : 0 < zm := div_pos (hWp s1) hn
  set z : I → S → ℝ := fun _ s => W s / n with hz
  have hzge : ∀ i s, zm ≤ z i s := fun i s =>
    div_le_div_of_nonneg_right (hs1 s (Finset.mem_univ _)) hn.le
  have hzM : ∀ i, z i ∈ Mset d := fun i => by
    have := Mset_line d (fun _ => 0) W (1 / n) (Mset_zero d) hWM
    convert this using 1
    funext s
    simp only [hz]
    ring
  have hzsum : ∀ s, ∑ i, z i s = W s := fun s => by
    simp only [hz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hn_def]
    field_simp
  set Wb : ℝ := ∑ s, W s with hWb_def
  have hWb : ∀ s, W s ≤ Wb := fun s =>
    Finset.single_le_sum (f := W) (fun s _ => (hWp s).le) (Finset.mem_univ s)
  set N : ℝ := ∑ i, ∑ s, l i * π i s * zm ^ (-γ i) * Wb with hN_def
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (mul_pos (hl i) (hπ i s)).le (Real.rpow_pos_of_pos hzm _).le)
      (le_trans (hWp s1).le (hWb s1))
  set Q : ℝ := ∑ i, ∑ s, 2 * N / (l i * π i s * zm) with hQ_def
  have hQterm : ∀ i s, 0 ≤ 2 * N / (l i * π i s * zm) := fun i s =>
    div_nonneg (by linarith) (mul_pos (mul_pos (hl i) (hπ i s)) hzm).le
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => hQterm i s
  have hQge : ∀ i s, 2 * N / (l i * π i s * zm) ≤ Q := fun i s =>
    le_trans (Finset.single_le_sum (f := fun s => 2 * N / (l i * π i s * zm))
        (fun s _ => hQterm i s) (Finset.mem_univ s))
      (Finset.single_le_sum (f := fun i => ∑ s, 2 * N / (l i * π i s * zm))
        (fun i _ => Finset.sum_nonneg fun s _ => hQterm i s) (Finset.mem_univ i))
  obtain ⟨g0, -, hg0⟩ := Finset.exists_min_image Finset.univ γ Finset.univ_nonempty
  obtain ⟨δ, hδ0, hδA, hδQ⟩ := small_delta (min (zm / 2) 1) Q (γ g0)
    (lt_min (by linarith) one_pos) hQ0 (hγ g0)
  have hδz : δ ≤ zm / 2 := hδA.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδA.trans (min_le_right _ _)
  have hδγ : ∀ i, Q < δ ^ (-γ i) := fun i => lt_of_lt_of_le hδQ
    (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg (hg0 i (Finset.mem_univ _))))
  set F : Set (I → S → ℝ) :=
    {x | (∀ i, x i ∈ Mset d) ∧ (∀ i s, δ ≤ x i s) ∧ ∀ s, ∑ i, x i s = W s} with hF_def
  have hFsub : ∀ x ∈ F, ∀ i s, x i s ≤ W s := fun x hx i s => by
    have := Finset.single_le_sum (f := fun j => x j s)
      (fun j _ => le_trans hδ0.le (hx.2.1 j s)) (Finset.mem_univ i)
    rw [hx.2.2 s] at this
    exact this
  have hFc : IsCompact F := by
    have hbox : IsCompact (Set.univ.pi fun _ : I => Set.univ.pi fun s : S => Set.Icc δ (W s)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun s => isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · have h1 : IsClosed {x : I → S → ℝ | ∀ i, x i ∈ Mset d} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => (isClosed_Mset d).preimage (continuous_apply i)
      have h2 : IsClosed {x : I → S → ℝ | ∀ i s, δ ≤ x i s} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun s =>
          isClosed_le continuous_const (by fun_prop)
      have h3 : IsClosed {x : I → S → ℝ | ∀ s, ∑ i, x i s = W s} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun s => isClosed_eq (by fun_prop) continuous_const
      exact h1.inter (h2.inter h3)
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      exact fun i s => ⟨hx.2.1 i s, hFsub x hx i s⟩
  have hzF : z ∈ F := ⟨hzM, fun i s => le_trans (by linarith) (hzge i s), hzsum⟩
  have hcont : ContinuousOn (Wel l π u) F := by
    intro x hx
    have hc : ∀ i s, ContinuousAt (fun y : I → S → ℝ => u i (y i s)) x := fun i s =>
      ContinuousAt.comp (x := x) (hu i _ (lt_of_lt_of_le hδ0 (hx.2.1 i s))).continuousAt
        ((by fun_prop : Continuous fun y : I → S → ℝ => y i s).continuousAt)
    have h : ContinuousAt (Wel l π u) x := by
      unfold Wel V
      exact tendsto_finsetSum _ fun i _ => Filter.Tendsto.const_mul (l i)
        (tendsto_finsetSum _ fun s _ => Filter.Tendsto.const_mul (π i s) (hc i s))
    exact h.continuousWithinAt
  obtain ⟨x, hxF, hxmax⟩ := hFc.exists_isMaxOn ⟨z, hzF⟩ hcont
  have hxpos : ∀ i s, 0 < x i s := fun i s => lt_of_lt_of_le hδ0 (hxF.2.1 i s)
  -- the floor does not bind
  have hint : ∀ i s, δ < x i s := by
    by_contra hne
    obtain ⟨i0, s0, h0⟩ : ∃ i s, x i s ≤ δ := by
      by_contra h
      apply hne
      intro i s
      by_contra h'
      exact h ⟨i, s, not_lt.1 h'⟩
    have hx0 : x i0 s0 = δ := le_antisymm h0 (hxF.2.1 i0 s0)
    set w : I → S → ℝ := fun i s => z i s - x i s with hw
    have hD := Wel_dir l π γ u hu x w hxpos
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Wel l π u (fun i s => x i s + t * w i s) ≤ Wel l π u (fun i s => x i s + 0 * w i s) := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have hmem : (fun i s => x i s + t * w i s) ∈ F := by
        refine ⟨fun i => Mset_line d (x i) (w i) t (hxF.1 i)
          (Mset_sub d (z i) (x i) (hzM i) (hxF.1 i)), fun i s => ?_, fun s => ?_⟩
        · have h1 := hxF.2.1 i s
          have h2 := hzge i s
          simp only [hw]
          nlinarith [ht.1, ht.2]
        · simp only [hw]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hzsum s,
            hxF.2.2 s, sub_self, mul_zero, add_zero]
      have h0' : (fun i s => x i s + (0 : ℝ) * w i s) = x := by
        funext i s
        ring
      rw [h0']
      exact hxmax hmem
    have hDle := deriv_nonpos _ _ hD hle
    set B : I → S → ℝ := fun i s => l i * π i s * zm ^ (-γ i) * Wb with hB
    have hterm : ∀ i s, 0 ≤ mu l π γ x i s * w i s + B i s := by
      intro i s
      have ha : 0 < l i * π i s := mul_pos (hl i) (hπ i s)
      have hB0 : 0 ≤ B i s := by
        simp only [hB]
        exact mul_nonneg (mul_nonneg ha.le (Real.rpow_pos_of_pos hzm _).le)
          (le_trans (hWp s1).le (hWb s1))
      rcases le_or_gt (x i s) (z i s) with h | h
      · have : 0 ≤ mu l π γ x i s * w i s :=
          mul_nonneg (mu_pos l hl π hπ γ x hxpos i s).le (by simp only [hw]; linarith)
        linarith
      · have hp0 : 0 ≤ x i s ^ (-γ i) := (Real.rpow_pos_of_pos (hxpos i s) _).le
        have hpP : x i s ^ (-γ i) ≤ zm ^ (-γ i) :=
          Real.rpow_le_rpow_of_nonpos hzm (le_trans (hzge i s) h.le) (by linarith [hγ i])
        have hxz : x i s - z i s ≤ Wb := by
          have := hFsub x hxF i s
          have := hWb s
          linarith [hzm, hzge i s]
        have h1 : x i s ^ (-γ i) * (x i s - z i s) ≤ zm ^ (-γ i) * Wb :=
          mul_le_mul hpP hxz (by linarith) (Real.rpow_pos_of_pos hzm _).le
        have h2 := mul_le_mul_of_nonneg_left h1 ha.le
        have e : mu l π γ x i s * w i s =
            -(l i * π i s * (x i s ^ (-γ i) * (x i s - z i s))) := by
          simp only [hw, mu]
          ring
        have e2 : B i s = l i * π i s * (zm ^ (-γ i) * Wb) := by
          simp only [hB]
          ring
        rw [e, e2]
        linarith
    have hsum : mu l π γ x i0 s0 * w i0 s0 + B i0 s0 ≤
        ∑ i, ∑ s, (mu l π γ x i s * w i s + B i s) :=
      le_trans (Finset.single_le_sum (f := fun s => mu l π γ x i0 s * w i0 s + B i0 s)
          (fun s _ => hterm i0 s) (Finset.mem_univ s0))
        (Finset.single_le_sum (f := fun i => ∑ s, (mu l π γ x i s * w i s + B i s))
          (fun i _ => Finset.sum_nonneg fun s _ => hterm i s) (Finset.mem_univ i0))
    have hsplit : ∑ i, ∑ s, (mu l π γ x i s * w i s + B i s) =
        ∑ i, ∑ s, mu l π γ x i s * w i s + N := by
      rw [hN_def, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    have hB00 : 0 ≤ B i0 s0 := by
      simp only [hB]
      exact mul_nonneg (mul_nonneg (mul_pos (hl i0) (hπ i0 s0)).le
        (Real.rpow_pos_of_pos hzm _).le) (le_trans (hWp s1).le (hWb s1))
    -- the floor term exceeds N
    have ha0 : 0 < l i0 * π i0 s0 := mul_pos (hl i0) (hπ i0 s0)
    have hfloor : N < mu l π γ x i0 s0 * w i0 s0 := by
      have hw0 : zm / 2 ≤ w i0 s0 := by
        simp only [hw, hx0]
        linarith [hzge i0 s0]
      have hq := hQge i0 s0
      have hd := hδγ i0
      have e : mu l π γ x i0 s0 = l i0 * π i0 s0 * δ ^ (-γ i0) := by
        simp only [mu, hx0]
      rw [e]
      have hk : 0 < l i0 * π i0 s0 * zm := mul_pos ha0 hzm
      have h1 : 2 * N / (l i0 * π i0 s0 * zm) < δ ^ (-γ i0) := lt_of_le_of_lt hq hd
      rw [div_lt_iff₀ hk] at h1
      have hdp : 0 < δ ^ (-γ i0) := Real.rpow_pos_of_pos hδ0 _
      have h2 : l i0 * π i0 s0 * δ ^ (-γ i0) * (zm / 2) ≤
          l i0 * π i0 s0 * δ ^ (-γ i0) * w i0 s0 :=
        mul_le_mul_of_nonneg_left hw0 (mul_pos ha0 hdp).le
      nlinarith
    linarith
  -- global optimality by concavity
  refine ⟨x, ⟨hxF.1, hxpos, hxF.2.2⟩, fun y hy => ?_⟩
  set w : I → S → ℝ := fun i s => y i s - x i s with hw
  have hD := Wel_dir l π γ u hu x w hxpos
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i s, δ < x i s + t * w i s := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro s
    have hc : Continuous fun t : ℝ => x i s + t * w i s := by fun_prop
    have h0 : δ < x i s + 0 * w i s := by simpa using hint i s
    exact (hc.tendsto 0).eventually (lt_mem_nhds h0)
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Wel l π u (fun i s => x i s + t * w i s) ≤ Wel l π u (fun i s => x i s + 0 * w i s) := by
    filter_upwards [nhdsWithin_le_nhds hev] with t ht
    have hmem : (fun i s => x i s + t * w i s) ∈ F := by
      refine ⟨fun i => Mset_line d (x i) (w i) t (hxF.1 i)
        (Mset_sub d (y i) (x i) (hy.1 i) (hxF.1 i)), fun i s => (ht i s).le, fun s => ?_⟩
      simp only [hw]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hy.2.2 s,
        hxF.2.2 s, sub_self, mul_zero, add_zero]
    have h0' : (fun i s => x i s + (0 : ℝ) * w i s) = x := by
      funext i s
      ring
    rw [h0']
    exact hxmax hmem
  have hDle := deriv_nonpos _ _ hD hle
  have hc := Wel_concave l (fun i => (hl i).le) π hπ γ hγ u hu x y hxpos hy.2.1
  linarith


/-! ## Continuity of the planner allocation in the weights -/

omit [Fintype S] in
/-- The feasible set with a floor is compact. -/
theorem floor_compact (d : J → S → ℝ) (W : S → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    IsCompact {x : I → S → ℝ | (∀ i, x i ∈ Mset d) ∧ (∀ i s, δ ≤ x i s) ∧
      ∀ s, ∑ i, x i s = W s} := by
  have hbox : IsCompact (Set.univ.pi fun _ : I => Set.univ.pi fun s : S => Set.Icc δ (W s)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun s => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {x : I → S → ℝ | ∀ i, x i ∈ Mset d} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => (isClosed_Mset d).preimage (continuous_apply i)
    have h2 : IsClosed {x : I → S → ℝ | ∀ i s, δ ≤ x i s} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun s =>
        isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {x : I → S → ℝ | ∀ s, ∑ i, x i s = W s} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun s => isClosed_eq (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  · intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    refine fun i s => ⟨hx.2.1 i s, ?_⟩
    have := Finset.single_le_sum (f := fun j => x j s)
      (fun j _ => le_trans hδ (hx.2.1 j s)) (Finset.mem_univ i)
    rw [hx.2.2 s] at this
    exact this

/-- **Uniform floor.** For weights in a band `[a, b]` with `a > 0`, every planner optimum is
bounded below by one `δ > 0`. -/
theorem plan_floor [Nonempty I] [Nonempty S] (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i)
    (u : I → ℝ → ℝ) (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c)
    (d : J → S → ℝ) (W : S → ℝ) (hWM : W ∈ Mset d) (hWp : ∀ s, 0 < W s) :
    ∃ δ, 0 < δ ∧ ∀ l : I → ℝ, (∀ i, a ≤ l i ∧ l i ≤ b) → ∀ x, PlanOpt l π u d W x →
      ∀ i s, δ ≤ x i s := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  obtain ⟨s1, -, hs1⟩ := Finset.exists_min_image Finset.univ W Finset.univ_nonempty
  set zm : ℝ := W s1 / n with hzm_def
  have hzm : 0 < zm := div_pos (hWp s1) hn
  set z : I → S → ℝ := fun _ s => W s / n with hz
  have hzge : ∀ i s, zm ≤ z i s := fun i s =>
    div_le_div_of_nonneg_right (hs1 s (Finset.mem_univ _)) hn.le
  have hzM : ∀ i, z i ∈ Mset d := fun i => by
    have := Mset_line d (fun _ => 0) W (1 / n) (Mset_zero d) hWM
    convert this using 1
    funext s
    simp only [hz]
    ring
  have hzsum : ∀ s, ∑ i, z i s = W s := fun s => by
    simp only [hz, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hn_def]
    field_simp
  set Wb : ℝ := ∑ s, W s with hWb_def
  have hWb : ∀ s, W s ≤ Wb := fun s =>
    Finset.single_le_sum (f := W) (fun s _ => (hWp s).le) (Finset.mem_univ s)
  have hWb0 : 0 ≤ Wb := le_trans (hWp s1).le (hWb s1)
  set N : ℝ := ∑ i, ∑ s, b * π i s * zm ^ (-γ i) * Wb with hN_def
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (mul_pos hb (hπ i s)).le (Real.rpow_pos_of_pos hzm _).le) hWb0
  set Q : ℝ := ∑ i, ∑ s, 2 * N / (a * π i s * zm) with hQ_def
  have hQterm : ∀ i s, 0 ≤ 2 * N / (a * π i s * zm) := fun i s =>
    div_nonneg (by linarith) (mul_pos (mul_pos ha (hπ i s)) hzm).le
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => hQterm i s
  have hQge : ∀ i s, 2 * N / (a * π i s * zm) ≤ Q := fun i s =>
    le_trans (Finset.single_le_sum (f := fun s => 2 * N / (a * π i s * zm))
        (fun s _ => hQterm i s) (Finset.mem_univ s))
      (Finset.single_le_sum (f := fun i => ∑ s, 2 * N / (a * π i s * zm))
        (fun i _ => Finset.sum_nonneg fun s _ => hQterm i s) (Finset.mem_univ i))
  obtain ⟨g0, -, hg0⟩ := Finset.exists_min_image Finset.univ γ Finset.univ_nonempty
  obtain ⟨δ, hδ0, hδA, hδQ⟩ := small_delta (min (zm / 2) 1) Q (γ g0)
    (lt_min (by linarith) one_pos) hQ0 (hγ g0)
  have hδz : δ ≤ zm / 2 := hδA.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδA.trans (min_le_right _ _)
  have hδγ : ∀ i, Q < δ ^ (-γ i) := fun i => lt_of_lt_of_le hδQ
    (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg (hg0 i (Finset.mem_univ _))))
  refine ⟨δ, hδ0, fun l hl x hx => ?_⟩
  have hlpos : ∀ i, 0 < l i := fun i => lt_of_lt_of_le ha (hl i).1
  have hxpos := hx.1.2.1
  have hxW : ∀ i s, x i s ≤ W s := fun i s => by
    have := Finset.single_le_sum (f := fun j => x j s)
      (fun j _ => (hxpos j s).le) (Finset.mem_univ i)
    rw [hx.1.2.2 s] at this
    exact this
  by_contra hne
  obtain ⟨i0, s0, h0⟩ : ∃ i s, x i s < δ := by
    by_contra h
    apply hne
    intro i s
    by_contra h'
    exact h ⟨i, s, not_le.1 h'⟩
  set w : I → S → ℝ := fun i s => z i s - x i s with hw
  have hD := Wel_dir l π γ u hu x w hxpos
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Wel l π u (fun i s => x i s + t * w i s) ≤ Wel l π u (fun i s => x i s + 0 * w i s) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have hmem : Feas d W (fun i s => x i s + t * w i s) := by
      refine ⟨fun i => Mset_line d (x i) (w i) t (hx.1.1 i)
        (Mset_sub d (z i) (x i) (hzM i) (hx.1.1 i)), fun i s => ?_, fun s => ?_⟩
      · have h1 := hxpos i s
        have h2 := hzge i s
        simp only [hw]
        nlinarith [ht.1, ht.2]
      · simp only [hw]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hzsum s,
          hx.1.2.2 s, sub_self, mul_zero, add_zero]
    have h0' : (fun i s => x i s + (0 : ℝ) * w i s) = x := by
      funext i s
      ring
    rw [h0']
    exact hx.2 _ hmem
  have hDle := deriv_nonpos _ _ hD hle
  set B : I → S → ℝ := fun i s => b * π i s * zm ^ (-γ i) * Wb with hB
  have hB0 : ∀ i s, 0 ≤ B i s := fun i s => by
    simp only [hB]
    exact mul_nonneg (mul_nonneg (mul_pos hb (hπ i s)).le (Real.rpow_pos_of_pos hzm _).le) hWb0
  have hterm : ∀ i s, 0 ≤ mu l π γ x i s * w i s + B i s := by
    intro i s
    have ha' : 0 < l i * π i s := mul_pos (hlpos i) (hπ i s)
    rcases le_or_gt (x i s) (z i s) with h | h
    · have : 0 ≤ mu l π γ x i s * w i s :=
        mul_nonneg (mu_pos l hlpos π hπ γ x hxpos i s).le (by simp only [hw]; linarith)
      linarith [hB0 i s]
    · have hpP : x i s ^ (-γ i) ≤ zm ^ (-γ i) :=
        Real.rpow_le_rpow_of_nonpos hzm (le_trans (hzge i s) h.le) (by linarith [hγ i])
      have hxz : x i s - z i s ≤ Wb := by
        have := hxW i s
        have := hWb s
        linarith [hzm, hzge i s]
      have h1 : x i s ^ (-γ i) * (x i s - z i s) ≤ zm ^ (-γ i) * Wb :=
        mul_le_mul hpP hxz (by linarith) (Real.rpow_pos_of_pos hzm _).le
      have h2 := mul_le_mul_of_nonneg_left h1 ha'.le
      have h3 : l i * π i s * (zm ^ (-γ i) * Wb) ≤ b * π i s * (zm ^ (-γ i) * Wb) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hl i).2 (hπ i s).le)
          (mul_nonneg (Real.rpow_pos_of_pos hzm _).le hWb0)
      have e : mu l π γ x i s * w i s =
          -(l i * π i s * (x i s ^ (-γ i) * (x i s - z i s))) := by
        simp only [hw, mu]
        ring
      have e2 : B i s = b * π i s * (zm ^ (-γ i) * Wb) := by
        simp only [hB]
        ring
      rw [e, e2]
      linarith
  have hsum : mu l π γ x i0 s0 * w i0 s0 + B i0 s0 ≤
      ∑ i, ∑ s, (mu l π γ x i s * w i s + B i s) :=
    le_trans (Finset.single_le_sum (f := fun s => mu l π γ x i0 s * w i0 s + B i0 s)
        (fun s _ => hterm i0 s) (Finset.mem_univ s0))
      (Finset.single_le_sum (f := fun i => ∑ s, (mu l π γ x i s * w i s + B i s))
        (fun i _ => Finset.sum_nonneg fun s _ => hterm i s) (Finset.mem_univ i0))
  have hsplit : ∑ i, ∑ s, (mu l π γ x i s * w i s + B i s) =
      ∑ i, ∑ s, mu l π γ x i s * w i s + N := by
    rw [hN_def, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hfloor : N < mu l π γ x i0 s0 * w i0 s0 := by
    have hw0 : zm / 2 ≤ w i0 s0 := by
      simp only [hw]
      linarith [hzge i0 s0]
    have hdp : 0 < δ ^ (-γ i0) := Real.rpow_pos_of_pos hδ0 _
    have hpow : δ ^ (-γ i0) ≤ x i0 s0 ^ (-γ i0) :=
      Real.rpow_le_rpow_of_nonpos (hxpos i0 s0) h0.le (by linarith [hγ i0])
    have h3 : a * π i0 s0 * δ ^ (-γ i0) ≤ mu l π γ x i0 s0 := by
      unfold mu
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hl i0).1 (hπ i0 s0).le) hpow hdp.le
        (mul_pos (hlpos i0) (hπ i0 s0)).le
    have h4 : a * π i0 s0 * δ ^ (-γ i0) * (zm / 2) ≤ mu l π γ x i0 s0 * w i0 s0 :=
      mul_le_mul h3 hw0 (by linarith) (mu_pos l hlpos π hπ γ x hxpos i0 s0).le
    have hk : 0 < a * π i0 s0 * zm := mul_pos (mul_pos ha (hπ i0 s0)) hzm
    have h1 : 2 * N / (a * π i0 s0 * zm) < δ ^ (-γ i0) := lt_of_le_of_lt (hQge i0 s0) (hδγ i0)
    rw [div_lt_iff₀ hk] at h1
    have e : a * π i0 s0 * δ ^ (-γ i0) * (zm / 2) = δ ^ (-γ i0) * (a * π i0 s0 * zm) / 2 := by
      ring
    linarith
  linarith [hB0 i0 s0]

/-- Joint continuity of weighted welfare in (weights, allocation) at a positive allocation. -/
theorem Wel_contAt (π : I → S → ℝ) (γ : I → ℝ) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (l0 : I → ℝ) (x0 : I → S → ℝ)
    (hx0 : ∀ i s, 0 < x0 i s) :
    ContinuousAt (fun p : (I → ℝ) × (I → S → ℝ) => Wel p.1 π u p.2) (l0, x0) := by
  have hc : ∀ i s, ContinuousAt (fun p : (I → ℝ) × (I → S → ℝ) => u i (p.2 i s)) (l0, x0) :=
    fun i s => ContinuousAt.comp (x := (l0, x0)) (hu i _ (hx0 i s)).continuousAt
      ((by fun_prop : Continuous fun p : (I → ℝ) × (I → S → ℝ) => p.2 i s).continuousAt)
  have hl : ∀ i, ContinuousAt (fun p : (I → ℝ) × (I → S → ℝ) => p.1 i) (l0, x0) :=
    fun i => (by fun_prop : Continuous fun p : (I → ℝ) × (I → S → ℝ) => p.1 i).continuousAt
  simp only [Wel, V]
  exact tendsto_finsetSum _ fun i _ => Filter.Tendsto.mul (hl i)
    (tendsto_finsetSum _ fun s _ => Filter.Tendsto.const_mul (π i s) (hc i s))

/-- **The planner allocation is continuous in the weights** on the open set of strictly
positive weights: any selection `X` of planner optima (which is unique there) is continuous
at every positive weight vector. -/
theorem planner_continuous [Nonempty I] [Nonempty S] (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s)
    (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (hWM : W ∈ Mset d) (hWp : ∀ s, 0 < W s) (X : (I → ℝ) → I → S → ℝ)
    (hX : ∀ l, (∀ i, 0 < l i) → PlanOpt l π u d W (X l)) (l0 : I → ℝ)
    (hl0 : ∀ i, 0 < l0 i) : ContinuousAt X l0 := by
  obtain ⟨i1, -, hi1⟩ := Finset.exists_min_image Finset.univ l0 Finset.univ_nonempty
  obtain ⟨i2, -, hi2⟩ := Finset.exists_max_image Finset.univ l0 Finset.univ_nonempty
  set a : ℝ := l0 i1 / 2 with ha_def
  set b : ℝ := 2 * l0 i2 with hb_def
  have ha : 0 < a := by have := hl0 i1; rw [ha_def]; linarith
  have hab : a ≤ b := by
    have := hi1 i2 (Finset.mem_univ _)
    have := hl0 i1
    rw [ha_def, hb_def]
    linarith
  obtain ⟨δ, hδ0, hfl⟩ := plan_floor a b ha hab π hπ γ hγ u hu d W hWM hWp
  have hnear : ∀ᶠ l in 𝓝 l0, ∀ i, a ≤ l i ∧ l i ≤ b := by
    rw [Filter.eventually_all]
    intro i
    have h1 : a < l0 i := by
      have := hi1 i (Finset.mem_univ _)
      have := hl0 i1
      rw [ha_def]
      linarith
    have h2 : l0 i < b := by
      have := hi2 i (Finset.mem_univ _)
      have := hl0 i
      rw [hb_def]
      linarith
    exact ((continuous_apply i).tendsto l0).eventually (Icc_mem_nhds h1 h2)
  have hposl : ∀ l : I → ℝ, (∀ i, a ≤ l i ∧ l i ≤ b) → ∀ i, 0 < l i :=
    fun l hl i => lt_of_lt_of_le ha (hl i).1
  have hK := floor_compact (I := I) d W δ hδ0.le
  have hmem : ∀ᶠ l in 𝓝 l0, X l ∈ {x : I → S → ℝ | (∀ i, x i ∈ Mset d) ∧
      (∀ i s, δ ≤ x i s) ∧ ∀ s, ∑ i, x i s = W s} :=
    hnear.mono fun l hl => ⟨(hX l (hposl l hl)).1.1, hfl l hl (X l) (hX l (hposl l hl)),
      (hX l (hposl l hl)).1.2.2⟩
  refine hK.tendsto_nhds_of_unique_mapClusterPt hmem fun xs hxs hcl => ?_
  have hxsF : Feas d W xs := ⟨hxs.1, fun i s => lt_of_lt_of_le hδ0 (hxs.2.1 i s), hxs.2.2⟩
  have hopt : PlanOpt l0 π u d W xs := by
    refine ⟨hxsF, fun y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hf := Wel_contAt π γ u hu l0 xs hxsF.2.1
    have hg : ContinuousAt (fun p : (I → ℝ) × (I → S → ℝ) => Wel p.1 π u y) (l0, xs) :=
      (Wel_contAt π γ u hu l0 y hy.2.1).comp_of_eq
        (f := fun p : (I → ℝ) × (I → S → ℝ) => (p.1, y))
        ((by fun_prop : Continuous fun p : (I → ℝ) × (I → S → ℝ) => (p.1, y)).continuousAt) rfl
    have hev : ∀ᶠ p in 𝓝 (l0, xs), Wel p.1 π u p.2 - Wel p.1 π u y < 0 :=
      (hf.sub hg).eventually (gt_mem_nhds (by show Wel l0 π u xs - Wel l0 π u y < 0; linarith))
    rw [nhds_prod_eq] at hev
    obtain ⟨pa, hpa, pb, hpb, hprod⟩ := Filter.eventually_prod_iff.1 hev
    have hfr := (hcl.frequently hpb).and_eventually (hpa.and hnear)
    obtain ⟨l, hlb, hla, hlab⟩ := hfr.exists
    have h1 := hprod hla hlb
    have h2 := (hX l (hposl l hlab)).2 y hy
    simp only at h1
    linarith
  exact planner_unique l0 hl0 π hπ γ hγ u hu d W xs (X l0) hopt (hX l0 hl0)

/-- **Negishi step: a planner optimum with zero transfers is an equilibrium.** If positive
welfare weights give a planner optimum on the marketed span at which every household's planner
bundle costs exactly its endowment at the supporting prices `ψ = mu i0`, then `ψ` is strictly
positive and there are portfolios clearing every asset market exactly, each paying the planner
bundle (strictly positive), each affordable at the arbitrage-free asset prices `qp ψ d` and
each optimal among ALL affordable portfolios with positive consumption. -/
theorem equilibrium_of_planner (l : I → ℝ) (hl : ∀ i, 0 < l i) (π : I → S → ℝ)
    (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (e : I → J → ℝ)
    (x : I → S → ℝ) (hx : PlanOpt l π u d (fun s => ∑ i, pay d (e i) s) x) (i0 : I)
    (hT : ∀ i, ∑ s, mu l π γ x i0 s * x i s = ∑ s, mu l π γ x i0 s * pay d (e i) s) :
    ∃ ψ : S → ℝ, (∀ s, 0 < ψ s) ∧ ∃ θ : I → J → ℝ, ∑ i, θ i = ∑ i, e i ∧
      ∀ i, (∀ s, 0 < pay d (θ i) s) ∧ (∀ s, pay d (θ i) s = x i s) ∧
        cost (qp ψ d) (θ i) ≤ cost (qp ψ d) (e i) ∧
        ∀ θ' : J → ℝ, cost (qp ψ d) θ' ≤ cost (qp ψ d) (e i) → (∀ s, 0 < pay d θ' s) →
          EU (π i) (u i) d θ' ≤ EU (π i) (u i) d (θ i) := by
  refine ⟨mu l π γ x i0, mu_pos l hl π hπ γ x hx.1.2.1 i0, ?_⟩
  have hO : ∀ i, Opt (π i) (u i) d (mu l π γ x i0)
      (∑ s, mu l π γ x i0 s * pay d (e i) s) (x i) := fun i => by
    rw [← hT i]
    exact planner_supports l hl π hπ γ hγ u hu d _ x hx i0 i
  obtain ⟨θ, hs, hi⟩ := equilibrium_of_payoff_clearing i0 π u d e _ x hO hx.1.2.2
  refine ⟨θ, hs, fun i => ⟨fun s => ?_, (hi i).1, (hi i).2.1, (hi i).2.2⟩⟩
  rw [(hi i).1 s]
  exact hx.1.2.1 i s


/-! ## Small weight forces small consumption -/

/-- **Small weight, small consumption.** There is `ε > 0` such that, at any planner optimum with
weights on the simplex, a household whose weight is below `ε` consumes less than `emin` in every
state. The proof covers the compact set of marketed bundles that reach `emin` somewhere by
finitely many neighbourhoods on which marginal utility against a fixed marketed bundle is
bounded, and uses the common projection of weighted marginal utilities. -/
theorem small_weight [Nonempty I] [Nonempty S] (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s)
    (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (W : S → ℝ)
    (hWp : ∀ s, 0 < W s) (emin : ℝ) (hemin : 0 < emin) :
    ∃ ε, 0 < ε ∧ ∀ l : I → ℝ, (∀ i, 0 < l i) → ∑ i, l i = 1 → ∀ x, PlanOpt l π u d W x →
      ∀ i, l i < ε → ∀ s, x i s < emin := by
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  obtain ⟨p0, -, hp0⟩ := Finset.exists_min_image (Finset.univ : Finset (I × S))
    (fun p => π p.1 p.2 * W p.2 ^ (-γ p.1) / n) Finset.univ_nonempty
  set c : ℝ := π p0.1 p0.2 * W p0.2 ^ (-γ p0.1) / n with hc_def
  have hc : 0 < c := div_pos (mul_pos (hπ _ _) (Real.rpow_pos_of_pos (hWp _) _)) hn
  set C : Set (S → ℝ) := {y | y ∈ Mset d ∧ (∀ s, 0 ≤ y s ∧ y s ≤ W s) ∧ ∃ s, emin ≤ y s}
    with hC_def
  have hCc : IsCompact C := by
    have hbox : IsCompact (Set.univ.pi fun s : S => Set.Icc 0 (W s)) :=
      isCompact_univ_pi fun s => isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · have h2 : IsClosed {y : S → ℝ | ∀ s, 0 ≤ y s ∧ y s ≤ W s} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun s =>
          (isClosed_le continuous_const (continuous_apply s)).inter
            (isClosed_le (continuous_apply s) continuous_const)
      have h3 : IsClosed {y : S → ℝ | ∃ s, emin ≤ y s} := by
        have e : {y : S → ℝ | ∃ s, emin ≤ y s} = ⋃ s, {y : S → ℝ | emin ≤ y s} := by
          ext y
          simp
        rw [e]
        exact isClosed_iUnion_of_finite fun s => isClosed_le continuous_const (continuous_apply s)
      exact (isClosed_Mset d).inter (h2.inter h3)
    · intro y hy
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      exact fun s => hy.2.1 s
  set U : (S → ℝ) → Set (S → ℝ) := fun y => {x | ∀ s, 0 < y s → y s / 2 < x s} with hU_def
  have hU : ∀ y ∈ C, U y ∈ 𝓝 y := by
    intro y _
    have : ∀ᶠ x in 𝓝 y, ∀ s, 0 < y s → y s / 2 < x s := by
      rw [Filter.eventually_all]
      intro s
      by_cases h : 0 < y s
      · exact (((continuous_apply s).tendsto y).eventually (lt_mem_nhds (half_lt_self h))).mono
          fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h' => absurd h' h
    exact this
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover U hU
  set Bd : (S → ℝ) → I → ℝ := fun y i => ∑ s, π i s * (y s / 2) ^ (-γ i) * y s with hBd
  have hBd0 : ∀ y ∈ C, ∀ i, 0 ≤ Bd y i := fun y hy i => Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (hπ i s).le
      (Real.rpow_nonneg (div_nonneg (hy.2.1 s).1 two_pos.le) _)) (hy.2.1 s).1
  set B : ℝ := 1 + ∑ y ∈ t, ∑ i, Bd y i with hB_def
  have hsum0 : 0 ≤ ∑ y ∈ t, ∑ i, Bd y i :=
    Finset.sum_nonneg fun y hy => Finset.sum_nonneg fun i _ => hBd0 y (htC y hy) i
  have hB : 0 < B := by linarith
  have hBge : ∀ y ∈ t, ∀ i, Bd y i ≤ B := fun y hy i => by
    have h1 := Finset.single_le_sum (f := fun i => Bd y i)
      (fun i _ => hBd0 y (htC y hy) i) (Finset.mem_univ i)
    have h2 := Finset.single_le_sum (f := fun y => ∑ i, Bd y i)
      (fun y hy => Finset.sum_nonneg fun i _ => hBd0 y (htC y hy) i) hy
    linarith
  refine ⟨c * emin / B, div_pos (mul_pos hc hemin) hB, fun l hl hl1 x hx i hli s0 => ?_⟩
  by_contra hge
  rw [not_lt] at hge
  have hxpos := hx.1.2.1
  have hxW : ∀ i s, x i s ≤ W s := fun i s => by
    have := Finset.single_le_sum (f := fun j => x j s)
      (fun j _ => (hxpos j s).le) (Finset.mem_univ i)
    rw [hx.1.2.2 s] at this
    exact this
  have hxC : x i ∈ C := ⟨hx.1.1 i, fun s => ⟨(hxpos i s).le, hxW i s⟩, s0, hge⟩
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxC)
  have hyC := htC y hyt
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
  have hlk : 1 / n ≤ l k := by
    have h1 : ∑ i, l i ≤ ∑ _i : I, l k := Finset.sum_le_sum fun i _ => hk i (Finset.mem_univ _)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    rw [hl1, ← hn_def] at h1
    rw [div_le_iff₀ hn]
    linarith
  have hcp := common_projection l π γ u hu d W x hx i k y hyC.1
  have hup : ∑ s, mu l π γ x i s * y s ≤ l i * Bd y i := by
    simp only [hBd]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rcases (hyC.2.1 s).1.lt_or_eq with h | h
    · have hp : x i s ^ (-γ i) ≤ (y s / 2) ^ (-γ i) :=
        Real.rpow_le_rpow_of_nonpos (half_pos h) (hxy s h).le (by linarith [hγ i])
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (hπ i s).le) (hyC.2.1 s).1) (hl i).le
      unfold mu
      linarith [this]
    · rw [← h]
      simp
  have hlow : c * emin ≤ ∑ s, mu l π γ x k s * y s := by
    have hterm : ∀ s, c ≤ mu l π γ x k s := fun s => by
      have h1 := hp0 (k, s) (Finset.mem_univ _)
      have hW' : W s ^ (-γ k) ≤ x k s ^ (-γ k) :=
        Real.rpow_le_rpow_of_nonpos (hxpos k s) (hxW k s) (by linarith [hγ k])
      have h2 : 1 / n * (π k s * W s ^ (-γ k)) ≤ l k * (π k s * x k s ^ (-γ k)) :=
        mul_le_mul hlk (mul_le_mul_of_nonneg_left hW' (hπ k s).le)
          (mul_pos (hπ k s) (Real.rpow_pos_of_pos (hWp s) _)).le (hl k).le
      have e1 : π k s * W s ^ (-γ k) / n = 1 / n * (π k s * W s ^ (-γ k)) := by ring
      have e2 : mu l π γ x k s = l k * (π k s * x k s ^ (-γ k)) := by unfold mu; ring
      simp only at h1
      rw [e2]
      linarith
    have h1 : ∑ s, c * y s ≤ ∑ s, mu l π γ x k s * y s :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hterm s) (hyC.2.1 s).1
    obtain ⟨s1, hs1⟩ := hyC.2.2
    have h2 : y s1 ≤ ∑ s, y s :=
      Finset.single_le_sum (f := y) (fun s _ => (hyC.2.1 s).1) (Finset.mem_univ s1)
    rw [← Finset.mul_sum] at h1
    nlinarith
  have h3 : l i * Bd y i ≤ l i * B := mul_le_mul_of_nonneg_left (hBge y hyt i) (hl i).le
  have h4 : l i * B < c * emin := (lt_div_iff₀ hB).1 hli
  linarith

/-! ## Brouwer on the weights -/

/-- Weights bounded below by `η` on the simplex. -/
def Dset (I : Type*) [Fintype I] (η : ℝ) : Set (I → ℝ) := {l | (∀ i, η ≤ l i) ∧ ∑ i, l i = 1}

theorem convex_Dset (η : ℝ) : Convex ℝ (Dset I η) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun h => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_le_mul_of_nonneg_left (hx.1 h) ha
    have := mul_le_mul_of_nonneg_left (hy.1 h) hb
    have e : a * η + b * η = η := by rw [← add_mul, hab, one_mul]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    linarith

theorem compact_Dset (η : ℝ) (hη : 0 ≤ η) : IsCompact (Dset I η) := by
  have hsub : Dset I η ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
    intro x hx h _
    refine ⟨le_trans hη (hx.1 h), ?_⟩
    rw [← hx.2]
    exact Finset.single_le_sum (fun k _ => le_trans hη (hx.1 k)) (Finset.mem_univ h)
  have hcl : IsClosed (Dset I η) := by
    have e : Dset I η = (⋂ h, {x : I → ℝ | η ≤ x h}) ∩ {x | ∑ h, x h = 1} := by
      ext x
      simp [Dset]
    rw [e]
    exact (isClosed_iInter fun h => isClosed_le continuous_const (continuous_apply h)).inter
      (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

/-- **Existence of equilibrium with incomplete markets and heterogeneous CRRA.** With any
number of assets (payoffs `d`), households with CRRA marginal utility `c ^ (−γ i)`, `γ i > 0`,
heterogeneous beliefs `π i s > 0`, and endowment portfolios paying a positive amount in every
state, there are positive state prices `ψ` (asset prices `qp ψ d`) and portfolios `θ` such that
every asset market clears, each portfolio pays a positive amount in every state, costs no more
than the endowment portfolio, and is optimal among all affordable portfolios with positive
payoff. -/
theorem exists_equilibrium_incomplete [Nonempty I] [Nonempty S] (π : I → S → ℝ)
    (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ) (e : I → J → ℝ)
    (he : ∀ i s, 0 < pay d (e i) s) :
    ∃ ψ : S → ℝ, (∀ s, 0 < ψ s) ∧ ∃ θ : I → J → ℝ, ∑ i, θ i = ∑ i, e i ∧
      ∀ i, (∀ s, 0 < pay d (θ i) s) ∧ cost (qp ψ d) (θ i) ≤ cost (qp ψ d) (e i) ∧
        ∀ θ' : J → ℝ, cost (qp ψ d) θ' ≤ cost (qp ψ d) (e i) → (∀ s, 0 < pay d θ' s) →
          EU (π i) (u i) d θ' ≤ EU (π i) (u i) d (θ i) := by
  set W : S → ℝ := fun s => ∑ i, pay d (e i) s with hW
  have hWM : W ∈ Mset d := ⟨∑ i, e i, funext fun s => pay_sum d e s⟩
  have hWp : ∀ s, 0 < W s := fun s => Finset.sum_pos (fun i _ => he i s) Finset.univ_nonempty
  obtain ⟨p1, -, hp1⟩ := Finset.exists_min_image (Finset.univ : Finset (I × S))
    (fun p => pay d (e p.1) p.2) Finset.univ_nonempty
  set emin : ℝ := pay d (e p1.1) p1.2 with hemin_def
  have hemin : 0 < emin := he _ _
  have hemin_le : ∀ i s, emin ≤ pay d (e i) s := fun i s => hp1 (i, s) (Finset.mem_univ _)
  obtain ⟨εb, hεb, hsmall⟩ := small_weight π hπ γ hγ u hu d W hWp emin hemin
  set ε : ℝ := min (εb / 2) 1 with hε_def
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hεb' : ε < εb := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : ε ≤ 1 := min_le_right _ _
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have hn1 : 1 ≤ n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  set η : ℝ := ε / (2 * n) with hη_def
  have hη0 : 0 < η := div_pos hε0 (by linarith)
  have hex : ∀ l : I → ℝ, ∃ x, (∀ i, 0 < l i) → PlanOpt l π u d W x := fun l => by
    by_cases h : ∀ i, 0 < l i
    · obtain ⟨x, hx⟩ := planner_exists l h π hπ γ hγ u hu d W hWM hWp
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose X hX using hex
  obtain ⟨k0⟩ := ‹Nonempty I›
  set t : (I → ℝ) → I → ℝ := fun l i =>
    ∑ s, mu l π γ (X l) k0 s * pay d (e i) s - ∑ s, mu l π γ (X l) k0 s * X l i s with ht_def
  set den : (I → ℝ) → ℝ := fun l => 1 + ∑ j, |t l j| with hden_def
  have hden : ∀ l, 0 < den l := fun l => by
    have : 0 ≤ ∑ j, |t l j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [hden_def]
    linarith
  set tn : (I → ℝ) → I → ℝ := fun l i => t l i / den l with htn_def
  have htn1 : ∀ l i, |tn l i| ≤ 1 := fun l i => by
    simp only [htn_def]
    rw [abs_div, abs_of_pos (hden l), div_le_iff₀ (hden l), one_mul]
    have := Finset.single_le_sum (f := fun j => |t l j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    simp only [hden_def]
    linarith
  set Z : (I → ℝ) → ℝ := fun l => ∑ j, max ε (l j + tn l j) with hZ_def
  set G : (I → ℝ) → I → ℝ := fun l i => max ε (l i + tn l i) / Z l with hG_def
  set D := Dset I η with hD_def
  have hDpos : ∀ l ∈ D, ∀ i, 0 < l i := fun l hl i => lt_of_lt_of_le hη0 (hl.1 i)
  have hDle1 : ∀ l ∈ D, ∀ i, l i ≤ 1 := fun l hl i => by
    rw [← hl.2]
    exact Finset.single_le_sum (fun k _ => (hDpos l hl k).le) (Finset.mem_univ i)
  have htsum : ∀ l ∈ D, ∑ i, t l i = 0 := fun l hl => by
    have := transfers_sum_zero l π γ u d e (X l) (hX l (hDpos l hl)) k0
    rw [Finset.sum_sub_distrib] at this
    simp only [ht_def]
    rw [Finset.sum_sub_distrib]
    linarith
  have htnsum : ∀ l ∈ D, ∑ i, tn l i = 0 := fun l hl => by
    simp only [htn_def]
    rw [← Finset.sum_div, htsum l hl, zero_div]
  have hZ1 : ∀ l ∈ D, 1 ≤ Z l := fun l hl => by
    have h1 : ∑ j, (l j + tn l j) ≤ Z l :=
      Finset.sum_le_sum fun j _ => le_max_right _ _
    rw [Finset.sum_add_distrib, hl.2, htnsum l hl] at h1
    linarith
  have hZle : ∀ l ∈ D, Z l ≤ 2 * n := fun l hl => by
    have h1 : Z l ≤ ∑ _j : I, (2 : ℝ) := Finset.sum_le_sum fun j _ =>
      max_le (by linarith) (by linarith [hDle1 l hl j, (abs_le.1 (htn1 l j)).2])
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    rw [← hn_def] at h1
    linarith
  have hsign : ∀ l ∈ D, ∀ i, l i ≤ ε → 0 < tn l i := fun l hl i hli => by
    have hlp := hDpos l hl
    have hxo := hX l hlp
    have hxs := hsmall l hlp hl.2 (X l) hxo i (lt_of_le_of_lt hli hεb')
    have hv : (fun s => pay d (e i) s - X l i s) ∈ Mset d :=
      Mset_sub d _ _ (mem_Mset d (e i)) (hxo.1.1 i)
    have hcp := common_projection l π γ u hu d W (X l) hxo i k0 _ hv
    have hpos : 0 < ∑ s, mu l π γ (X l) i s * (pay d (e i) s - X l i s) :=
      Finset.sum_pos (fun s _ => mul_pos (mu_pos l hlp π hπ γ (X l) hxo.1.2.1 i s)
        (by linarith [hxs s, hemin_le i s])) Finset.univ_nonempty
    have ht : t l i = ∑ s, mu l π γ (X l) k0 s * (pay d (e i) s - X l i s) := by
      simp only [ht_def, mul_sub, Finset.sum_sub_distrib]
    simp only [htn_def]
    exact div_pos (by rw [ht, ← hcp]; exact hpos) (hden l)
  have hmaps : ∀ l ∈ D, G l ∈ D := fun l hl => by
    have hZp : 0 < Z l := by linarith [hZ1 l hl]
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : η ≤ ε / Z l :=
        div_le_div_of_nonneg_left hε0.le hZp (by linarith [hZle l hl])
      have h2 : ε / Z l ≤ max ε (l i + tn l i) / Z l :=
        div_le_div_of_nonneg_right (le_max_left _ _) hZp.le
      exact h1.trans h2
    · simp only [hG_def]
      rw [← Finset.sum_div]
      exact div_self hZp.ne'
  have hDn : D.Nonempty := by
    refine ⟨fun _ => 1 / n, fun i => ?_, ?_⟩
    · simp only [hη_def]
      rw [div_le_div_iff₀ (by linarith) hn]
      nlinarith
    · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hn_def]
      field_simp
  -- continuity
  have cq : ∀ i, Continuous fun q : D => q.1 i := fun i =>
    (continuous_apply i).comp continuous_subtype_val
  have cX : Continuous fun q : D => X q.1 := by
    refine continuous_iff_continuousAt.2 fun q => ?_
    exact ContinuousAt.comp (x := q)
      (planner_continuous π hπ γ hγ u hu d W hWM hWp X (fun l hl => hX l hl) q.1
        (hDpos q.1 q.2)) continuous_subtype_val.continuousAt
  have cXis : ∀ i s, Continuous fun q : D => X q.1 i s := fun i s =>
    (continuous_apply s).comp ((continuous_apply i).comp cX)
  have cmu : ∀ s, Continuous fun q : D => mu q.1 π γ (X q.1) k0 s := fun s => by
    simp only [mu]
    exact ((cq k0).mul continuous_const).mul ((cXis k0 s).rpow_const fun q =>
      Or.inl ((hX q.1 (hDpos q.1 q.2)).1.2.1 k0 s).ne')
  have ct : ∀ i, Continuous fun q : D => t q.1 i := fun i => by
    simp only [ht_def]
    exact (continuous_finsetSum _ fun s _ => (cmu s).mul continuous_const).sub
      (continuous_finsetSum _ fun s _ => (cmu s).mul (cXis i s))
  have ctn : ∀ i, Continuous fun q : D => tn q.1 i := fun i =>
    (ct i).div (continuous_const.add (continuous_finsetSum _ fun j _ => (ct j).abs))
      fun q => (hden q.1).ne'
  have cZ : Continuous fun q : D => Z q.1 :=
    continuous_finsetSum _ fun j _ => continuous_const.max ((cq j).add (ctn j))
  have cG : Continuous fun q : D => G q.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_const.max ((cq i).add (ctn i))).div cZ
      fun q => by linarith [hZ1 q.1 q.2]
  let f : C(D, D) := ⟨fun q => ⟨G q.1, hmaps q.1 q.2⟩, cG.subtype_mk _⟩
  obtain ⟨q, hq⟩ := brouwer_fixed_point D (convex_Dset η) (compact_Dset η hη0.le) hDn f
  have hfix : G q.1 = q.1 := congrArg Subtype.val hq
  set l := q.1 with hl_def
  have hl : l ∈ D := q.2
  have hlp := hDpos l hl
  have hZp : 0 < Z l := by linarith [hZ1 l hl]
  have hmx : ∀ i, max ε (l i + tn l i) = l i * Z l := fun i => by
    have h := congrFun hfix i
    simp only [hG_def] at h
    rw [div_eq_iff hZp.ne'] at h
    exact h
  have hZ : Z l ≤ 1 := by
    by_contra hZ
    rw [not_le] at hZ
    have hall : ∀ i ∈ Finset.univ, (fun _ => (0 : ℝ)) i < tn l i := by
      intro i _
      by_cases hli : l i ≤ ε
      · exact hsign l hl i hli
      · rw [not_le] at hli
        have h1 : l i < l i * Z l := by nlinarith [hlp i]
        have h2 : ε < max ε (l i + tn l i) := by rw [hmx i]; linarith
        have h3 : ε < l i + tn l i := by
          rcases lt_max_iff.1 h2 with h | h
          · exact absurd h (lt_irrefl _)
          · exact h
        have h4 := hmx i
        rw [max_eq_right h3.le] at h4
        show 0 < tn l i
        nlinarith [hlp i]
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hall
    rw [htnsum l hl] at this
    simp at this
  have hnp : ∀ i, tn l i ≤ 0 := fun i => by
    have h1 : l i + tn l i ≤ l i * Z l := by rw [← hmx i]; exact le_max_right _ _
    nlinarith [hlp i]
  have hz : ∀ i, tn l i = 0 := fun i => by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun i => -tn l i)
      (fun i _ => by linarith [hnp i])).1 (by rw [Finset.sum_neg_distrib, htnsum l hl]; simp)
      i (Finset.mem_univ _)
    linarith
  have hT : ∀ i, ∑ s, mu l π γ (X l) k0 s * X l i s =
      ∑ s, mu l π γ (X l) k0 s * pay d (e i) s := fun i => by
    have h := hz i
    simp only [htn_def] at h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · simp only [ht_def] at h
      linarith
    · exact absurd h (hden l).ne'
  obtain ⟨ψ, hψ, θ, hθ, hall⟩ :=
    equilibrium_of_planner l hlp π hπ γ hγ u hu d e (X l) (hX l hlp) k0 hT
  exact ⟨ψ, hψ, θ, hθ, fun i => ⟨(hall i).1, (hall i).2.2.1, (hall i).2.2.2⟩⟩

end IncompleteNegishi

end

#print axioms IncompleteNegishi.planner_foc
#print axioms IncompleteNegishi.common_projection
#print axioms IncompleteNegishi.planner_supports
#print axioms IncompleteNegishi.transfers_sum_zero
#print axioms IncompleteNegishi.equilibrium_of_planner
#print axioms IncompleteNegishi.planner_unique
#print axioms IncompleteNegishi.planner_exists
#print axioms IncompleteNegishi.plan_floor
#print axioms IncompleteNegishi.planner_continuous
#print axioms IncompleteNegishi.small_weight
#print axioms IncompleteNegishi.exists_equilibrium_incomplete
