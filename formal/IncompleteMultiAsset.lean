import Mathlib

/-!
# Stage 380: incomplete markets with many assets: the household optimum exists at every
# arbitrage-free price

Stages 366, 371 and 375 left open the existence of equilibrium with many assets, incomplete
markets and heterogeneous risk aversion. Stages 371 and 375 named the missing ingredients:
existence of each household's optimal portfolio at arbitrary arbitrage-free prices, continuity
of portfolio demand in a multi-dimensional price, and a fixed point argument. This file proves
the first ingredient in full generality and its uniqueness; it does NOT prove existence of
equilibrium.

Setup: one date, finitely many states `s` with common probabilities `π s > 0`, finitely many
assets `j` with ANY payoffs `d j s` (any sign; markets may be incomplete, assets may be
redundant). Asset prices are arbitrage-free: `q j = qp ψ d j = Σ_s ψ s d j s` with strictly
positive state prices `ψ s`. A household has marginal utility `c ^ (−γ)` with any `γ > 0` (log
and every power utility) and an endowment portfolio `e` paying a positive amount in every state.

* `exists_optimum`: there is a portfolio `θ` that costs no more than the endowment portfolio,
  gives positive consumption in every state, and maximises expected utility among ALL portfolios
  that cost no more than the endowment portfolio and give positive consumption.
  Proof: in payoff space, the budget set intersected with the span of the payoffs and with
  `{x ≥ δ}` is compact (`K_compact`; the span is closed, `isClosed_Mset`), so expected utility
  has a maximiser there. If the maximiser touched the floor `δ` in some state, moving toward
  the endowment payoff would raise utility at rate at least `π_min δ ^ (−γ) m / 2 − A` (an Inada
  bound with explicit constants), which is positive for `δ` small (`small_delta`); so the
  maximiser is interior, the directional derivative toward every affordable positive payoff is
  nonpositive (`deriv_nonpos`), and concavity (`V_diff_le`) makes it a global maximiser.
* `optimum_payoff_unique`: any two optimal portfolios (for the same prices and budget) pay the
  same in every state (strict concavity, `mid_strict`).
* `portfolio_unique`: if no nonzero portfolio pays zero in every state, the optimal portfolio
  itself is unique.

Limits: this is a household-level result. Existence of a general equilibrium with many assets,
incomplete markets and heterogeneous CRRA coefficients remains NOT proved: continuity of the
optimal portfolio in the state prices (which needs a uniform interiority bound and a
closed-graph argument) and the fixed point over prices (which must handle state prices
approaching zero) are not in this file. One date, common beliefs, CRRA marginal utility only.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace IncompleteMultiAsset

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

/-- Affordable marketed payoffs with a floor `δ` in every state. -/
def K (d : J → S → ℝ) (ψ : S → ℝ) (w δ : ℝ) : Set (S → ℝ) :=
  {x | x ∈ Mset d ∧ (∀ s, δ ≤ x s) ∧ ∑ s, ψ s * x s ≤ w}

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

theorem cost_line (q θ v : J → ℝ) (t : ℝ) :
    cost q (fun i => θ i + t * v i) = cost q θ + t * cost q v := by
  unfold cost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cost_sub (q θ e : J → ℝ) : cost q (fun j => e j - θ j) = cost q e - cost q θ := by
  unfold cost
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

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

theorem K_le {d : J → S → ℝ} {ψ : S → ℝ} {w δ : ℝ} (hψ : ∀ s, 0 < ψ s) (hδ : 0 < δ)
    {x : S → ℝ} (hx : x ∈ K d ψ w δ) (s : S) : ψ s * x s ≤ w := by
  simp only [K, Set.mem_ofPred_eq] at hx
  have : ψ s * x s ≤ ∑ t, ψ t * x t :=
    Finset.single_le_sum (f := fun t => ψ t * x t)
      (fun t _ => mul_nonneg (hψ t).le (hδ.le.trans (hx.2.1 t))) (Finset.mem_univ s)
  linarith [hx.2.2]

theorem K_compact (d : J → S → ℝ) (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (w δ : ℝ) (hδ : 0 < δ) :
    IsCompact (K d ψ w δ) := by
  have h1 : IsClosed {x : S → ℝ | ∀ s, δ ≤ x s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h2 : IsClosed {x : S → ℝ | ∑ s, ψ s * x s ≤ w} :=
    isClosed_le (by fun_prop) continuous_const
  have hcl : IsClosed (K d ψ w δ) := (isClosed_Mset d).inter (h1.inter h2)
  refine (isCompact_univ_pi fun s => isCompact_Icc (a := δ) (b := w / ψ s)).of_isClosed_subset
    hcl ?_
  intro x hx
  rw [Set.mem_univ_pi]
  intro s
  have hle := K_le hψ hδ hx s
  simp only [K, Set.mem_ofPred_eq] at hx
  refine ⟨hx.2.1 s, ?_⟩
  rw [le_div_iff₀ (hψ s)]
  linarith

theorem V_contOn (π : S → ℝ) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (ψ : S → ℝ) (w δ : ℝ)
    (hδ : 0 < δ) : ContinuousOn (V π u) (K d ψ w δ) := by
  intro x hx
  simp only [K, Set.mem_ofPred_eq] at hx
  have h : ContinuousAt (V π u) x := by
    unfold V
    exact tendsto_finsetSum _ fun s _ => Filter.Tendsto.const_mul (π s)
      (ContinuousAt.comp (x := x) (hu _ (lt_of_lt_of_le hδ (hx.2.1 s))).continuousAt
        ((continuous_apply s : Continuous fun p : S → ℝ => p s).continuousAt))
  exact h.continuousWithinAt

/-- Derivative of expected utility along a segment of payoffs. -/
theorem hasDeriv_line (π : S → ℝ) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (x z : S → ℝ) (hx : ∀ s, 0 < x s) :
    HasDerivAt (fun t => V π u (fun s => x s + t * (z s - x s)))
      (∑ s, π s * x s ^ (-γ) * (z s - x s)) 0 := by
  show HasDerivAt (fun t => ∑ s, π s * u (x s + t * (z s - x s))) _ 0
  apply HasDerivAt.fun_sum
  intro s _
  have hin : HasDerivAt (fun t => x s + t * (z s - x s)) (z s - x s) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (z s - x s)).const_add (x s)).congr_deriv (one_mul _)
  have hpos : 0 < x s + 0 * (z s - x s) := by simpa using hx s
  exact (((hu _ hpos).comp (0 : ℝ) hin).const_mul (π s)).congr_deriv
    (by rw [zero_mul, add_zero]; ring)

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

/-- **The household optimum exists at every arbitrage-free price**, with any number of assets,
any (possibly incomplete) payoffs, and any CRRA coefficient. -/
theorem exists_optimum [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (e : J → ℝ) (he : ∀ s, 0 < pay d e s) :
    ∃ θ : J → ℝ, cost (qp ψ d) θ ≤ cost (qp ψ d) e ∧ (∀ s, 0 < pay d θ s) ∧
      ∀ θ', cost (qp ψ d) θ' ≤ cost (qp ψ d) e → (∀ s, 0 < pay d θ' s) →
        EU π u d θ' ≤ EU π u d θ := by
  set w := ∑ s, ψ s * pay d e s with hw
  have hwc : cost (qp ψ d) e = w := cost_qp ψ d e
  have hw0 : 0 < w := Finset.sum_pos (fun s _ => mul_pos (hψ s) (he s)) Finset.univ_nonempty
  set m := Finset.univ.inf' Finset.univ_nonempty (fun s => pay d e s) with hm
  obtain ⟨slo, -, hslo⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun s => pay d e s)
  have hm0 : 0 < m := by
    rw [hm, hslo]
    exact he slo
  have hmle : ∀ s, m ≤ pay d e s := fun s =>
    Finset.inf'_le (fun s => pay d e s) (Finset.mem_univ s)
  set pmin := Finset.univ.inf' Finset.univ_nonempty π with hpmin
  obtain ⟨sp, -, hsp⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty π
  have hp0 : 0 < pmin := by
    rw [hpmin, hsp]
    exact hπ sp
  have hple : ∀ s, pmin ≤ π s := fun s => Finset.inf'_le π (Finset.mem_univ s)
  set qmin := Finset.univ.inf' Finset.univ_nonempty ψ with hqmin
  obtain ⟨sq, -, hsq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ψ
  have hq0 : 0 < qmin := by
    rw [hqmin, hsq]
    exact hψ sq
  have hqle : ∀ s, qmin ≤ ψ s := fun s => Finset.inf'_le ψ (Finset.mem_univ s)
  set P := ∑ s, π s with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun s _ => (hπ s).le
  have hmr : 0 ≤ m ^ (-γ) := Real.rpow_nonneg hm0.le _
  have hwq : 0 < w / qmin := div_pos hw0 hq0
  set A := P * (m ^ (-γ) * (w / qmin)) with hA
  have hA0 : 0 ≤ A := mul_nonneg hP0 (mul_nonneg hmr hwq.le)
  obtain ⟨δ, hδ0, hδm, hδM⟩ := small_delta (m / 2) (2 * A / (pmin * m)) γ (by linarith)
    (div_nonneg (by linarith) (mul_pos hp0 hm0).le) hγ
  have hx0K : (fun s => pay d e s) ∈ K d ψ w δ := by
    simp only [K, Set.mem_ofPred_eq]
    exact ⟨⟨e, rfl⟩, fun s => by linarith [hmle s], le_rfl⟩
  obtain ⟨x, hxK, hxmax⟩ := (K_compact d ψ hψ w δ hδ0).exists_isMaxOn ⟨_, hx0K⟩
    (V_contOn π γ u hu d ψ w δ hδ0)
  have hxle : ∀ s, ψ s * x s ≤ w := K_le hψ hδ0 hxK
  have hxK' := hxK
  simp only [K, Mset, Set.mem_ofPred_eq, Set.mem_range] at hxK'
  obtain ⟨⟨θ, hθ⟩, hxδ, hxb⟩ := hxK'
  have hpx : ∀ s, pay d θ s = x s := fun s => congrFun hθ s
  have hxpos : ∀ s, 0 < x s := fun s => lt_of_lt_of_le hδ0 (hxδ s)
  have hxub : ∀ s, x s ≤ w / qmin := fun s => by
    rw [le_div_iff₀ hq0]
    have h1 : x s * qmin ≤ x s * ψ s := mul_le_mul_of_nonneg_left (hqle s) (hxpos s).le
    linarith [hxle s]
  -- Step 1: the maximiser stays strictly above the floor.
  have hint : ∀ s, δ < x s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s0, hs0⟩ := hcon
    have hs0e : x s0 = δ := le_antisymm hs0 (hxδ s0)
    have hDle : ∑ s, π s * x s ^ (-γ) * (pay d e s - x s) ≤ 0 := by
      refine deriv_nonpos _ _ (hasDeriv_line π γ u hu x (fun s => pay d e s) hxpos) ?_
      filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
      have hmem : (fun s => x s + t * (pay d e s - x s)) ∈ K d ψ w δ := by
        simp only [K, Mset, Set.mem_ofPred_eq, Set.mem_range]
        refine ⟨⟨fun j => θ j + t * (e j - θ j), ?_⟩, fun s => ?_, ?_⟩
        · funext s
          simp only [pay_line, pay_sub, hpx]
        · have h1 : (1 - t) * δ ≤ (1 - t) * x s :=
            mul_le_mul_of_nonneg_left (hxδ s) (by linarith [ht.2])
          have h2 : t * δ ≤ t * pay d e s :=
            mul_le_mul_of_nonneg_left (by linarith [hmle s]) ht.1.le
          linarith
        · have e1 : ∑ s, ψ s * (x s + t * (pay d e s - x s)) =
              (1 - t) * ∑ s, ψ s * x s + t * ∑ s, ψ s * pay d e s := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
          rw [e1]
          have h1 : (1 - t) * ∑ s, ψ s * x s ≤ (1 - t) * w :=
            mul_le_mul_of_nonneg_left hxb (by linarith [ht.2])
          have h2 : ∑ s, ψ s * pay d e s = w := rfl
          linarith
      have := isMaxOn_iff.1 hxmax _ hmem
      simpa using this
    have hterm : ∀ s, -(π s * (m ^ (-γ) * (w / qmin))) ≤
        π s * x s ^ (-γ) * (pay d e s - x s) := by
      intro s
      have hr : 0 ≤ x s ^ (-γ) := Real.rpow_nonneg (hxpos s).le _
      have hc : 0 ≤ π s * (m ^ (-γ) * (w / qmin)) :=
        mul_nonneg (hπ s).le (mul_nonneg hmr hwq.le)
      rcases le_or_gt (x s) (pay d e s) with h | h
      · have : 0 ≤ π s * x s ^ (-γ) * (pay d e s - x s) :=
          mul_nonneg (mul_nonneg (hπ s).le hr) (by linarith)
        linarith
      · have hxm : m ≤ x s := by linarith [hmle s]
        have hpow : x s ^ (-γ) ≤ m ^ (-γ) := Real.rpow_le_rpow_of_nonpos hm0 hxm (by linarith)
        have h1 : m ^ (-γ) * (pay d e s - x s) ≤ x s ^ (-γ) * (pay d e s - x s) :=
          mul_le_mul_of_nonpos_right hpow (by linarith)
        have h2 : m ^ (-γ) * (-(w / qmin)) ≤ m ^ (-γ) * (pay d e s - x s) :=
          mul_le_mul_of_nonneg_left (by linarith [hxub s, he s]) hmr
        have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hπ s).le
        linarith
    have hb0 : pmin * δ ^ (-γ) * (m / 2) ≤ π s0 * x s0 ^ (-γ) * (pay d e s0 - x s0) := by
      rw [hs0e]
      have hdp : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
      have h1 : m / 2 ≤ pay d e s0 - δ := by linarith [hmle s0]
      have h2 : pmin * δ ^ (-γ) ≤ π s0 * δ ^ (-γ) := mul_le_mul_of_nonneg_right (hple s0) hdp.le
      calc pmin * δ ^ (-γ) * (m / 2) ≤ π s0 * δ ^ (-γ) * (m / 2) :=
            mul_le_mul_of_nonneg_right h2 (by linarith)
        _ ≤ π s0 * δ ^ (-γ) * (pay d e s0 - δ) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (hπ s0).le hdp.le)
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun s => π s * x s ^ (-γ) * (pay d e s - x s)) (Finset.mem_univ s0)).symm
    have hrest : -A ≤ ∑ s ∈ Finset.univ.erase s0, π s * x s ^ (-γ) * (pay d e s - x s) := by
      have h1 : ∑ s ∈ Finset.univ.erase s0, -(π s * (m ^ (-γ) * (w / qmin))) ≤
          ∑ s ∈ Finset.univ.erase s0, π s * x s ^ (-γ) * (pay d e s - x s) :=
        Finset.sum_le_sum fun s _ => hterm s
      have h2 : ∑ s ∈ Finset.univ.erase s0, π s * (m ^ (-γ) * (w / qmin)) ≤
          ∑ s, π s * (m ^ (-γ) * (w / qmin)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun s _ _ => mul_nonneg (hπ s).le (mul_nonneg hmr hwq.le)
      have h3 : ∑ s, π s * (m ^ (-γ) * (w / qmin)) = A := by
        rw [hA, hP, Finset.sum_mul]
      rw [Finset.sum_neg_distrib] at h1
      linarith
    have hbig : A < pmin * δ ^ (-γ) * (m / 2) := by
      have hpm : 0 < pmin * m := mul_pos hp0 hm0
      rw [div_lt_iff₀ hpm] at hδM
      linarith
    linarith
  -- Step 2: an interior maximiser is a global maximiser.
  refine ⟨θ, ?_, fun s => by rw [hpx]; exact hxpos s, fun θ' hb' hpos' => ?_⟩
  · rw [cost_qp, cost_qp]
    simp only [hpx]
    exact hxb
  · have hb'' : ∑ s, ψ s * pay d θ' s ≤ w := by
      rw [← cost_qp, hwc.symm]
      exact hb'
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ s, δ < x s + t * (pay d θ' s - x s) := by
      refine Filter.eventually_all.2 fun s => ?_
      have hc : Continuous fun t : ℝ => x s + t * (pay d θ' s - x s) := by fun_prop
      exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hint s)))
    have hDy : ∑ s, π s * x s ^ (-γ) * (pay d θ' s - x s) ≤ 0 := by
      refine deriv_nonpos _ _ (hasDeriv_line π γ u hu x (fun s => pay d θ' s) hxpos) ?_
      filter_upwards [hev, Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t hts ht
      have hmem : (fun s => x s + t * (pay d θ' s - x s)) ∈ K d ψ w δ := by
        simp only [K, Mset, Set.mem_ofPred_eq, Set.mem_range]
        refine ⟨⟨fun j => θ j + t * (θ' j - θ j), ?_⟩, fun s => (hts s).le, ?_⟩
        · funext s
          simp only [pay_line, pay_sub, hpx]
        · have e1 : ∑ s, ψ s * (x s + t * (pay d θ' s - x s)) =
              (1 - t) * ∑ s, ψ s * x s + t * ∑ s, ψ s * pay d θ' s := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
          rw [e1]
          have h1 : (1 - t) * ∑ s, ψ s * x s ≤ (1 - t) * w :=
            mul_le_mul_of_nonneg_left hxb (by linarith [ht.2])
          have h2 : t * ∑ s, ψ s * pay d θ' s ≤ t * w :=
            mul_le_mul_of_nonneg_left hb'' ht.1.le
          linarith
      have := isMaxOn_iff.1 hxmax _ hmem
      simpa using this
    have hV := V_diff_le π (fun s => (hπ s).le) γ hγ u hu x (fun s => pay d θ' s) hxpos hpos'
    have e1 : EU π u d θ' = V π u (fun s => pay d θ' s) := rfl
    have e2 : EU π u d θ = V π u x := by
      unfold EU V
      simp only [hpx]
    rw [e1, e2]
    linarith

/-- **The optimal payoff is unique**: two optimal portfolios for the same prices and budget pay
the same in every state. -/
theorem optimum_payoff_unique (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (q : J → ℝ)
    (W : ℝ) (θ1 θ2 : J → ℝ) (h1 : cost q θ1 ≤ W) (h2 : cost q θ2 ≤ W)
    (hp1 : ∀ s, 0 < pay d θ1 s) (hp2 : ∀ s, 0 < pay d θ2 s)
    (ho1 : ∀ θ', cost q θ' ≤ W → (∀ s, 0 < pay d θ' s) → EU π u d θ' ≤ EU π u d θ1)
    (ho2 : ∀ θ', cost q θ' ≤ W → (∀ s, 0 < pay d θ' s) → EU π u d θ' ≤ EU π u d θ2) :
    ∀ s, pay d θ1 s = pay d θ2 s := by
  by_contra hne
  push Not at hne
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨θm, hθm⟩ : ∃ θm : J → ℝ, θm = fun j => θ1 j + (1 / 2) * (θ2 j - θ1 j) := ⟨_, rfl⟩
  have hpm : ∀ s, pay d θm s = (pay d θ1 s + pay d θ2 s) / 2 := fun s => by
    rw [hθm, pay_line, pay_sub]
    ring
  have hcm : cost q θm = (cost q θ1 + cost q θ2) / 2 := by
    rw [hθm, cost_line, cost_sub]
    ring
  have hstrict : EU π u d θ1 + EU π u d θ2 < 2 * EU π u d θm := by
    unfold EU
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ _, ?_⟩
    · rw [hpm s]
      rcases eq_or_ne (pay d θ1 s) (pay d θ2 s) with h | h
      · rw [h, add_self_div_two]
        linarith
      · have := mul_le_mul_of_nonneg_left (mid_strict γ hγ u hu (hp1 s) (hp2 s) h).le
          (hπ s).le
        linarith
    · rw [hpm s0]
      have := mul_lt_mul_of_pos_left (mid_strict γ hγ u hu (hp1 s0) (hp2 s0) hs0) (hπ s0)
      linarith
  have hm_pos : ∀ s, 0 < pay d θm s := fun s => by
    rw [hpm]
    linarith [hp1 s, hp2 s]
  have hmc : cost q θm ≤ W := by
    rw [hcm]
    linarith
  have a1 := ho1 θm hmc hm_pos
  have a2 := ho1 θ2 h2 hp2
  have a3 := ho2 θ1 h1 hp1
  linarith

omit [Fintype S] in
/-- With no redundant assets, equal payoffs mean equal portfolios. -/
theorem portfolio_unique (d : J → S → ℝ)
    (hli : ∀ v : J → ℝ, (∀ s, ∑ j, v j * d j s = 0) → v = 0) (θ1 θ2 : J → ℝ)
    (h : ∀ s, pay d θ1 s = pay d θ2 s) : θ1 = θ2 := by
  have hv := hli (fun j => θ1 j - θ2 j) fun s => by
    have := pay_sub d θ2 θ1 s
    rw [h s, sub_self] at this
    exact this
  funext j
  have := congrFun hv j
  simp only [Pi.zero_apply] at this
  linarith

/-- **Existence and uniqueness of the optimal portfolio** at arbitrage-free prices with
non-redundant (possibly incomplete) assets and any CRRA coefficient. -/
theorem exists_unique_optimum [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ)
    (hγ : 0 < γ) (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (hli : ∀ v : J → ℝ, (∀ s, ∑ j, v j * d j s = 0) → v = 0)
    (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (e : J → ℝ) (he : ∀ s, 0 < pay d e s) :
    ∃ θ : J → ℝ, (cost (qp ψ d) θ ≤ cost (qp ψ d) e ∧ (∀ s, 0 < pay d θ s) ∧
      ∀ θ', cost (qp ψ d) θ' ≤ cost (qp ψ d) e → (∀ s, 0 < pay d θ' s) →
        EU π u d θ' ≤ EU π u d θ) ∧
      ∀ θ2 : J → ℝ, cost (qp ψ d) θ2 ≤ cost (qp ψ d) e → (∀ s, 0 < pay d θ2 s) →
        (∀ θ', cost (qp ψ d) θ' ≤ cost (qp ψ d) e → (∀ s, 0 < pay d θ' s) →
          EU π u d θ' ≤ EU π u d θ2) → θ2 = θ := by
  obtain ⟨θ, h1, hp1, ho1⟩ := exists_optimum π hπ γ hγ u hu d ψ hψ e he
  refine ⟨θ, ⟨h1, hp1, ho1⟩, fun θ2 h2 hp2 ho2 => ?_⟩
  exact portfolio_unique d hli θ2 θ (optimum_payoff_unique π hπ γ hγ u hu d (qp ψ d) _ θ2 θ
    h2 h1 hp2 hp1 ho2 ho1)

end IncompleteMultiAsset

end

#print axioms IncompleteMultiAsset.concave_lt
#print axioms IncompleteMultiAsset.mid_strict
#print axioms IncompleteMultiAsset.deriv_nonpos
#print axioms IncompleteMultiAsset.isClosed_Mset
#print axioms IncompleteMultiAsset.K_compact
#print axioms IncompleteMultiAsset.V_diff_le
#print axioms IncompleteMultiAsset.exists_optimum
#print axioms IncompleteMultiAsset.optimum_payoff_unique
#print axioms IncompleteMultiAsset.portfolio_unique
#print axioms IncompleteMultiAsset.exists_unique_optimum
