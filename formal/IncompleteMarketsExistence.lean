import Mathlib

/-!
# Stage 382: incomplete markets with one good per state: continuity of demand and the
# reduction of equilibrium to clearing of payoffs

SCOPE: ONE GOOD PER STATE. Everything here is for a single consumption good in each state, so
asset payoffs are real and do not depend on spot prices. With several goods per state,
equilibrium in incomplete markets with real assets can fail to exist (Hart 1975); nothing in
this file applies to that case.

Setup: one date, finitely many states `s`, finitely many assets `j` with ANY real payoffs
`d j s` (incomplete or redundant allowed). Each household has probabilities `π s > 0`,
marginal utility `c ^ (−γ)` with its own `γ > 0`, and an endowment portfolio `e` whose payoff
is positive in every state (the endowment is spanned by the assets; asset supply is
`Σ_i e_i`). Asset prices are arbitrage-free, `q = qp ψ d` with state prices `ψ s > 0`.
Definitions and the household-optimum results are copied from stage 380
(`IncompleteMultiAsset.lean`, not modified).

Proved here:
* `opt_exists`, `opt_unique`: the optimal marketed payoff (`Opt`) exists and is unique at every
  strictly positive `ψ`.
* `opt_le`, `opt_floor`: UNIFORM bounds. On any price set `{ψ | ∀ s, lo ≤ ψ s, ψ·e ≤ B}` every
  optimal payoff lies in `[δ, B / lo]` in every state, with one `δ > 0` for the whole set
  (explicit Inada constants).
* `dem_continuousAt`: the demand map `ψ ↦ dem ψ` (the optimal payoff) is continuous at every
  strictly positive `ψ` (sequential compactness + the uniform bounds + uniqueness).
* `budget_binds`, `walras`: each household spends its whole budget, so aggregate excess payoff
  demand has value zero at every `ψ > 0`.
* `equilibrium_of_payoff_clearing`: if at some `ψ > 0` the optimal payoffs add up to the
  aggregate endowment payoff, there are portfolios `θ_i` with `Σ_i θ_i = Σ_i e_i` (asset markets
  clear exactly, even with redundant assets), each paying the optimal payoff, each affordable at
  `q = qp ψ d` and each optimal among ALL affordable portfolios with positive consumption.
  This is an equilibrium with no-arbitrage prices.

NOT proved (honest limit): EXISTENCE of a `ψ > 0` at which payoffs clear. The missing step is
the fixed point over state prices. A truncated simplex of `ψ` does not work directly because
demand depends on `ψ` only through its action on the marketed span, so demand need not blow up
as some `ψ s → 0`; the boundary argument has to be made in the space of asset prices (the
no-arbitrage cone), where the needed desirability bound near arbitrage prices is not proved
here. Also limited to: spanned endowments, one date, CRRA marginal utility.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace IncompleteMarketsExistence

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


/-! ## Stage 382: optimal payoffs, uniform bounds, continuity of demand, clearing -/

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

/-- `x` is an optimal marketed payoff at state prices `ψ` with wealth `W`. -/
def Opt (π : S → ℝ) (u : ℝ → ℝ) (d : J → S → ℝ) (ψ : S → ℝ) (W : ℝ) (x : S → ℝ) : Prop :=
  x ∈ Mset d ∧ (∀ s, 0 < x s) ∧ ∑ s, ψ s * x s ≤ W ∧
    ∀ y ∈ Mset d, (∀ s, 0 < y s) → ∑ s, ψ s * y s ≤ W → V π u y ≤ V π u x

/-- The optimal marketed payoff exists at every strictly positive `ψ`. -/
theorem opt_exists [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (e : J → ℝ) (he : ∀ s, 0 < pay d e s) :
    ∃ x, Opt π u d ψ (∑ s, ψ s * pay d e s) x := by
  obtain ⟨θ, hc, hp, ho⟩ := exists_optimum π hπ γ hγ u hu d ψ hψ e he
  rw [cost_qp, cost_qp] at hc
  refine ⟨fun s => pay d θ s, mem_Mset d θ, hp, hc, ?_⟩
  intro y hy hpos hb
  obtain ⟨θ', hθ'⟩ := hy
  subst hθ'
  exact ho θ' (by rw [cost_qp, cost_qp]; exact hb) hpos

/-- The optimal marketed payoff is unique. -/
theorem opt_unique (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (ψ : S → ℝ) (W : ℝ) (x1 x2 : S → ℝ) (h1 : Opt π u d ψ W x1) (h2 : Opt π u d ψ W x2) :
    x1 = x2 := by
  obtain ⟨⟨θ1, rfl⟩, hp1, hb1, ho1⟩ := h1
  obtain ⟨⟨θ2, rfl⟩, hp2, hb2, ho2⟩ := h2
  funext s
  exact optimum_payoff_unique π hπ γ hγ u hu d (qp ψ d) W θ1 θ2
    (by rw [cost_qp]; exact hb1) (by rw [cost_qp]; exact hb2) hp1 hp2
    (fun θ' hc hp => ho1 (fun s => pay d θ' s) (mem_Mset d θ') hp
      (by rw [cost_qp] at hc; exact hc))
    (fun θ' hc hp => ho2 (fun s => pay d θ' s) (mem_Mset d θ') hp
      (by rw [cost_qp] at hc; exact hc)) s

/-- Uniform upper bound: with `ψ ≥ lo > 0` and wealth at most `B`, an optimal payoff is at most
`B / lo` in every state. -/
theorem opt_le {π : S → ℝ} {u : ℝ → ℝ} {d : J → S → ℝ} {ψ : S → ℝ} {W lo B : ℝ}
    (hlo : 0 < lo) (hψ : ∀ s, lo ≤ ψ s) (hW : W ≤ B) {x : S → ℝ} (hx : Opt π u d ψ W x)
    (s : S) : x s ≤ B / lo := by
  obtain ⟨-, hpos, hb, -⟩ := hx
  have h1 : ψ s * x s ≤ ∑ t, ψ t * x t :=
    Finset.single_le_sum (f := fun t => ψ t * x t)
      (fun t _ => mul_nonneg (hlo.le.trans (hψ t)) (hpos t).le) (Finset.mem_univ s)
  have h2 : lo * x s ≤ ψ s * x s := mul_le_mul_of_nonneg_right (hψ s) (hpos s).le
  rw [le_div_iff₀ hlo]
  linarith

/-- **Uniform floor.** One `δ > 0` bounds every optimal payoff from below, in every state,
for all state prices with `ψ ≥ lo > 0` and endowment value at most `B`. -/
theorem opt_floor [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (e : J → ℝ) (he : ∀ s, 0 < pay d e s) (lo B : ℝ) (hlo : 0 < lo) (hB : 0 ≤ B) :
    ∃ δ, 0 < δ ∧ ∀ ψ : S → ℝ, (∀ s, lo ≤ ψ s) → ∑ s, ψ s * pay d e s ≤ B →
      ∀ x, Opt π u d ψ (∑ s, ψ s * pay d e s) x → ∀ s, δ ≤ x s := by
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
  set P := ∑ s, π s with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun s _ => (hπ s).le
  have hmr : 0 ≤ m ^ (-γ) := Real.rpow_nonneg hm0.le _
  have hBl : 0 ≤ B / lo := div_nonneg hB hlo.le
  set A := P * (m ^ (-γ) * (B / lo)) with hA
  have hA0 : 0 ≤ A := mul_nonneg hP0 (mul_nonneg hmr hBl)
  obtain ⟨δ, hδ0, hδm, hδM⟩ := small_delta (m / 2) (2 * A / (pmin * m)) γ (by linarith)
    (div_nonneg (by linarith) (mul_pos hp0 hm0).le) hγ
  refine ⟨δ, hδ0, fun ψ hψ hWB x hx s0 => ?_⟩
  by_contra hlt
  push Not at hlt
  have hxub : ∀ s, x s ≤ B / lo := opt_le hlo hψ hWB hx
  obtain ⟨⟨θ, hθ⟩, hxpos, hxb, hxo⟩ := hx
  have hpx : ∀ s, pay d θ s = x s := fun s => congrFun hθ s
  have hDle : ∑ s, π s * x s ^ (-γ) * (pay d e s - x s) ≤ 0 := by
    refine deriv_nonpos _ _ (hasDeriv_line π γ u hu x (fun s => pay d e s) hxpos) ?_
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    have hmem : (fun s => x s + t * (pay d e s - x s)) ∈ Mset d := by
      have h : (fun s => x s + t * (pay d e s - x s)) =
          fun s => pay d (fun j => θ j + t * (e j - θ j)) s := by
        funext s
        simp only [pay_line, pay_sub, hpx]
      rw [h]
      exact mem_Mset d _
    have hpos : ∀ s, 0 < x s + t * (pay d e s - x s) := fun s => by
      have h1 : 0 ≤ (1 - t) * x s := mul_nonneg (by linarith [ht.2]) (hxpos s).le
      have h2 : 0 < t * pay d e s := mul_pos ht.1 (he s)
      linarith
    have hbud : ∑ s, ψ s * (x s + t * (pay d e s - x s)) ≤ ∑ s, ψ s * pay d e s := by
      have e1 : ∑ s, ψ s * (x s + t * (pay d e s - x s)) =
          (1 - t) * ∑ s, ψ s * x s + t * ∑ s, ψ s * pay d e s := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e1]
      have h1 : (1 - t) * ∑ s, ψ s * x s ≤ (1 - t) * ∑ s, ψ s * pay d e s :=
        mul_le_mul_of_nonneg_left hxb (by linarith [ht.2])
      linarith
    have := hxo _ hmem hpos hbud
    simpa using this
  have hterm : ∀ s, -(π s * (m ^ (-γ) * (B / lo))) ≤
      π s * x s ^ (-γ) * (pay d e s - x s) := by
    intro s
    have hr : 0 ≤ x s ^ (-γ) := Real.rpow_nonneg (hxpos s).le _
    have hc : 0 ≤ π s * (m ^ (-γ) * (B / lo)) :=
      mul_nonneg (hπ s).le (mul_nonneg hmr hBl)
    rcases le_or_gt (x s) (pay d e s) with h | h
    · have : 0 ≤ π s * x s ^ (-γ) * (pay d e s - x s) :=
        mul_nonneg (mul_nonneg (hπ s).le hr) (by linarith)
      linarith
    · have hxm : m ≤ x s := by linarith [hmle s]
      have hpow : x s ^ (-γ) ≤ m ^ (-γ) := Real.rpow_le_rpow_of_nonpos hm0 hxm (by linarith)
      have h1 : m ^ (-γ) * (pay d e s - x s) ≤ x s ^ (-γ) * (pay d e s - x s) :=
        mul_le_mul_of_nonpos_right hpow (by linarith)
      have h2 : m ^ (-γ) * (-(B / lo)) ≤ m ^ (-γ) * (pay d e s - x s) :=
        mul_le_mul_of_nonneg_left (by linarith [hxub s, he s]) hmr
      have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hπ s).le
      linarith
  have hb0 : pmin * δ ^ (-γ) * (m / 2) ≤ π s0 * x s0 ^ (-γ) * (pay d e s0 - x s0) := by
    have hdp : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
    have hxr : δ ^ (-γ) ≤ x s0 ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (hxpos s0) hlt.le (by linarith)
    have h1 : m / 2 ≤ pay d e s0 - x s0 := by linarith [hmle s0]
    have h2 : pmin * δ ^ (-γ) ≤ π s0 * x s0 ^ (-γ) := by
      have a1 : pmin * δ ^ (-γ) ≤ π s0 * δ ^ (-γ) :=
        mul_le_mul_of_nonneg_right (hple s0) hdp.le
      have a2 : π s0 * δ ^ (-γ) ≤ π s0 * x s0 ^ (-γ) :=
        mul_le_mul_of_nonneg_left hxr (hπ s0).le
      linarith
    calc pmin * δ ^ (-γ) * (m / 2) ≤ π s0 * x s0 ^ (-γ) * (m / 2) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ ≤ π s0 * x s0 ^ (-γ) * (pay d e s0 - x s0) :=
          mul_le_mul_of_nonneg_left h1
            (mul_nonneg (hπ s0).le (Real.rpow_nonneg (hxpos s0).le _))
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun s => π s * x s ^ (-γ) * (pay d e s - x s)) (Finset.mem_univ s0)).symm
  have hrest : -A ≤ ∑ s ∈ Finset.univ.erase s0, π s * x s ^ (-γ) * (pay d e s - x s) := by
    have h1 : ∑ s ∈ Finset.univ.erase s0, -(π s * (m ^ (-γ) * (B / lo))) ≤
        ∑ s ∈ Finset.univ.erase s0, π s * x s ^ (-γ) * (pay d e s - x s) :=
      Finset.sum_le_sum fun s _ => hterm s
    have h2 : ∑ s ∈ Finset.univ.erase s0, π s * (m ^ (-γ) * (B / lo)) ≤
        ∑ s, π s * (m ^ (-γ) * (B / lo)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun s _ _ => mul_nonneg (hπ s).le (mul_nonneg hmr hBl)
    have h3 : ∑ s, π s * (m ^ (-γ) * (B / lo)) = A := by
      rw [hA, hP, Finset.sum_mul]
    rw [Finset.sum_neg_distrib] at h1
    linarith
  have hbig : A < pmin * δ ^ (-γ) * (m / 2) := by
    have hpm : 0 < pmin * m := mul_pos hp0 hm0
    rw [div_lt_iff₀ hpm] at hδM
    linarith
  linarith

/-- Expected utility is continuous at every strictly positive payoff. -/
theorem V_contAt (π : S → ℝ) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (x : S → ℝ) (hx : ∀ s, 0 < x s) :
    ContinuousAt (V π u) x := by
  unfold V
  exact tendsto_finsetSum _ fun s _ => Filter.Tendsto.const_mul (π s)
    (ContinuousAt.comp (x := x) (hu _ (hx s)).continuousAt
      ((continuous_apply s : Continuous fun p : S → ℝ => p s).continuousAt))

/-- Demand: the optimal marketed payoff at state prices `ψ` (zero where none exists). -/
def dem (π : S → ℝ) (u : ℝ → ℝ) (d : J → S → ℝ) (e : J → ℝ) (ψ : S → ℝ) : S → ℝ :=
  if h : ∃ x, Opt π u d ψ (∑ s, ψ s * pay d e s) x then h.choose else 0

theorem dem_spec [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (e : J → ℝ) (he : ∀ s, 0 < pay d e s) :
    Opt π u d ψ (∑ s, ψ s * pay d e s) (dem π u d e ψ) := by
  have h := opt_exists π hπ γ hγ u hu d ψ hψ e he
  unfold dem
  rw [dite_eq_left h]
  exact h.choose_spec

/-- **Continuity of demand.** The optimal marketed payoff is a continuous function of the state
prices at every strictly positive `ψ`, with any number of (possibly redundant) assets in
(possibly) incomplete markets and any `γ > 0`. -/
theorem dem_continuousAt [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (e : J → ℝ) (he : ∀ s, 0 < pay d e s) (ψ0 : S → ℝ) (hψ0 : ∀ s, 0 < ψ0 s) :
    ContinuousAt (dem π u d e) ψ0 := by
  set mn := Finset.univ.inf' Finset.univ_nonempty ψ0 with hmn
  obtain ⟨sq, -, hsq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ψ0
  have hmn0 : 0 < mn := by
    rw [hmn, hsq]
    exact hψ0 sq
  have hmnle : ∀ s, mn ≤ ψ0 s := fun s => Finset.inf'_le ψ0 (Finset.mem_univ s)
  obtain ⟨lo, hlo0, hlomn⟩ : ∃ lo : ℝ, 0 < lo ∧ lo < mn := ⟨mn / 2, by linarith, by linarith⟩
  set W0 := ∑ s, ψ0 s * pay d e s
  have hW0pos : 0 < W0 :=
    Finset.sum_pos (fun s _ => mul_pos (hψ0 s) (he s)) Finset.univ_nonempty
  obtain ⟨B, hB0, hWB⟩ : ∃ B : ℝ, 0 ≤ B ∧ W0 < B := ⟨W0 + 1, by linarith, by linarith⟩
  obtain ⟨δ, hδ0, hfl⟩ := opt_floor π hπ γ hγ u hu d e he lo B hlo0 hB0
  have hcW : Continuous fun ψ : S → ℝ => ∑ s, ψ s * pay d e s := by fun_prop
  have hG : ∀ᶠ ψ in 𝓝 ψ0, (∀ s, lo < ψ s) ∧ ∑ s, ψ s * pay d e s < B := by
    refine Filter.Eventually.and (Filter.eventually_all.2 fun s => ?_) ?_
    · exact ((continuous_apply s).tendsto ψ0).eventually (lt_mem_nhds (by linarith [hmnle s]))
    · exact (hcW.tendsto ψ0).eventually (gt_mem_nhds hWB)
  have hmemC : ∀ ψ : S → ℝ, ((∀ s, lo < ψ s) ∧ ∑ s, ψ s * pay d e s < B) →
      dem π u d e ψ ∈ Mset d ∩ Set.pi Set.univ (fun _ => Set.Icc δ (B / lo)) ∧
      Opt π u d ψ (∑ s, ψ s * pay d e s) (dem π u d e ψ) := by
    intro ψ hψ
    have hψp : ∀ s, 0 < ψ s := fun s => hlo0.trans (hψ.1 s)
    have hO := dem_spec π hπ γ hγ u hu d ψ hψp e he
    have hle : ∀ s, lo ≤ ψ s := fun s => (hψ.1 s).le
    exact ⟨⟨hO.1, Set.mem_univ_pi.2 fun s =>
      ⟨hfl ψ hle hψ.2.le _ hO s, opt_le hlo0 hle hψ.2.le hO s⟩⟩, hO⟩
  have hC : IsCompact (Mset d ∩ Set.pi Set.univ (fun _ : S => Set.Icc δ (B / lo))) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_left (isClosed_Mset d)
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro ψs hψs
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hψs.comp hns).eventually hG)
  obtain ⟨xs, hxsC, φ, hφ, hlim⟩ := hC.tendsto_subseq
    (x := fun k => dem π u d e (ψs (ns (k + N))))
    fun k => (hmemC (ψs (ns (k + N))) (hN (k + N) (by omega))).1
  refine ⟨fun k => φ k + N, ?_⟩
  have hφt : Tendsto (fun k => φ k + N) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) N) hφ.tendsto_atTop
  have hp : Tendsto (fun k => ψs (ns (φ k + N))) atTop (𝓝 ψ0) := (hψs.comp hns).comp hφt
  have hGk : ∀ k, (∀ s, lo < ψs (ns (φ k + N)) s) ∧
      ∑ s, ψs (ns (φ k + N)) s * pay d e s < B := fun k => hN _ (by omega)
  have hx : Tendsto (fun k => dem π u d e (ψs (ns (φ k + N)))) atTop (𝓝 xs) := hlim
  have hOk : ∀ k, Opt π u d (ψs (ns (φ k + N))) (∑ s, ψs (ns (φ k + N)) s * pay d e s)
      (dem π u d e (ψs (ns (φ k + N)))) := fun k => (hmemC _ (hGk k)).2
  have hxspos : ∀ s, 0 < xs s := fun s => hδ0.trans_le (Set.mem_univ_pi.1 hxsC.2 s).1
  have hpi := tendsto_pi_nhds.1 hp
  have hxi := tendsto_pi_nhds.1 hx
  have hWlim : Tendsto (fun k => ∑ s, ψs (ns (φ k + N)) s * pay d e s) atTop (𝓝 W0) :=
    tendsto_finsetSum _ fun s _ => (hpi s).mul_const _
  have hOpt : Opt π u d ψ0 W0 xs := by
    refine ⟨hxsC.1, hxspos, ?_, ?_⟩
    · exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ fun s _ => (hpi s).mul (hxi s))
        hWlim fun k => (hOk k).2.2.1
    · intro y hyM hypos hyb
      obtain ⟨θy, hθy⟩ := hyM
      have hclaim : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          V π u (fun s => (1 - t) * y s) ≤ V π u xs := by
        intro t ht
        have hyt : (fun s => (1 - t) * y s) ∈ Mset d := by
          have h : (fun s => (1 - t) * y s) = fun s => pay d (fun j => (1 - t) * θy j) s := by
            funext s
            rw [← hθy]
            show (1 - t) * pay d θy s = pay d (fun j => (1 - t) * θy j) s
            unfold pay
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [h]
          exact mem_Mset d _
        have hytpos : ∀ s, 0 < (1 - t) * y s := fun s =>
          mul_pos (by linarith [ht.2]) (hypos s)
        have hneg : ∑ s, ψ0 s * ((1 - t) * y s) - W0 < 0 := by
          have e1 : ∑ s, ψ0 s * ((1 - t) * y s) = (1 - t) * ∑ s, ψ0 s * y s := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
          rw [e1]
          have h1 : (1 - t) * ∑ s, ψ0 s * y s ≤ (1 - t) * W0 :=
            mul_le_mul_of_nonneg_left hyb (by linarith [ht.2])
          have h2 : 0 < t * W0 := mul_pos ht.1 hW0pos
          linarith
        have hFl : Tendsto (fun k => ∑ s, ψs (ns (φ k + N)) s * ((1 - t) * y s) -
            ∑ s, ψs (ns (φ k + N)) s * pay d e s) atTop
            (𝓝 (∑ s, ψ0 s * ((1 - t) * y s) - W0)) :=
          (tendsto_finsetSum _ fun s _ => (hpi s).mul_const _).sub hWlim
        have hev : ∀ᶠ k in atTop, V π u (fun s => (1 - t) * y s) ≤
            V π u (dem π u d e (ψs (ns (φ k + N)))) := by
          filter_upwards [hFl.eventually (gt_mem_nhds hneg)] with k hk
          exact (hOk k).2.2.2 _ hyt hytpos (sub_neg.1 hk).le
        exact ge_of_tendsto ((V_contAt π γ u hu xs hxspos).tendsto.comp hx) hev
      have h1 : Tendsto (fun t : ℝ => fun s => (1 - t) * y s) (𝓝 0) (𝓝 y) :=
        (continuous_pi fun s => by fun_prop : Continuous fun t : ℝ => fun s => (1 - t) * y s
          ).tendsto' 0 y (by funext s; simp)
      have hg := ((V_contAt π γ u hu y hypos).tendsto.comp h1).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      refine le_of_tendsto hg ?_
      filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
      exact hclaim t ht
  have hEq : xs = dem π u d e ψ0 :=
    opt_unique π hπ γ hγ u hu d ψ0 W0 xs _ hOpt (dem_spec π hπ γ hγ u hu d ψ0 hψ0 e he)
  rw [← hEq]
  exact hx

/-- **The budget binds**: an optimal payoff spends the whole endowment value. -/
theorem budget_binds [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ)
    (u : ℝ → ℝ) (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) (e : J → ℝ) (he : ∀ s, 0 < pay d e s)
    (x : S → ℝ) (hx : Opt π u d ψ (∑ s, ψ s * pay d e s) x) :
    ∑ s, ψ s * x s = ∑ s, ψ s * pay d e s := by
  obtain ⟨⟨θ, hθ⟩, hxpos, hxb, hxo⟩ := hx
  have hpx : ∀ s, pay d θ s = x s := fun s => congrFun hθ s
  refine le_antisymm hxb (not_lt.1 fun hlt => ?_)
  set W := ∑ s, ψ s * pay d e s with hW
  have hW0 : 0 < W := Finset.sum_pos (fun s _ => mul_pos (hψ s) (he s)) Finset.univ_nonempty
  set t := (W - ∑ s, ψ s * x s) / W with ht
  have ht0 : 0 < t := div_pos (by linarith) hW0
  have hyM : (fun s => x s + t * pay d e s) ∈ Mset d := by
    have h : (fun s => x s + t * pay d e s) = fun s => pay d (fun j => θ j + t * e j) s := by
      funext s
      rw [pay_line, hpx]
    rw [h]
    exact mem_Mset d _
  have hypos : ∀ s, 0 < x s + t * pay d e s := fun s => by
    have := mul_pos ht0 (he s)
    linarith [hxpos s]
  have hyb : ∑ s, ψ s * (x s + t * pay d e s) ≤ W := by
    have e1 : ∑ s, ψ s * (x s + t * pay d e s) = ∑ s, ψ s * x s + t * W := by
      rw [hW, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e1, ht, div_mul_cancel₀ _ hW0.ne']
    linarith
  have hle := hxo _ hyM hypos hyb
  have hlt' : V π u x < V π u (fun s => x s + t * pay d e s) := by
    unfold V
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun s _ => ?_
    have h1 := concave_le γ hγ u hu (hypos s) (hxpos s)
    have h2 : 0 < (x s + t * pay d e s) ^ (-γ) * (t * pay d e s) :=
      mul_pos (Real.rpow_pos_of_pos (hypos s) _) (mul_pos ht0 (he s))
    have h3 : u (x s) < u (x s + t * pay d e s) := by nlinarith
    exact mul_lt_mul_of_pos_left h3 (hπ s)
  linarith

/-- **Walras' law** for payoff demand: aggregate excess payoff demand has value zero at every
strictly positive `ψ`. -/
theorem walras {I : Type*} [Fintype I] [Nonempty S] (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s)
    (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ)
    (e : I → J → ℝ) (he : ∀ i s, 0 < pay d (e i) s) (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s) :
    ∑ s, ψ s * (∑ i, dem (π i) (u i) d (e i) ψ s - ∑ i, pay d (e i) s) = 0 := by
  have hb : ∀ i, ∑ s, ψ s * dem (π i) (u i) d (e i) ψ s = ∑ s, ψ s * pay d (e i) s :=
    fun i => budget_binds (π i) (hπ i) (γ i) (hγ i) (u i) (hu i) d ψ hψ (e i) (he i) _
      (dem_spec (π i) (hπ i) (γ i) (hγ i) (u i) (hu i) d ψ hψ (e i) (he i))
  have hc : ∀ f : I → S → ℝ, ∑ s, ψ s * ∑ i, f i s = ∑ i, ∑ s, ψ s * f i s := fun f => by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have e1 : ∑ s, ψ s * (∑ i, dem (π i) (u i) d (e i) ψ s - ∑ i, pay d (e i) s) =
      ∑ s, ψ s * ∑ i, dem (π i) (u i) d (e i) ψ s - ∑ s, ψ s * ∑ i, pay d (e i) s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, hc (fun i s => dem (π i) (u i) d (e i) ψ s), hc (fun i s => pay d (e i) s)]
  simp only [hb, sub_self]

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

/-- **Equilibrium at clearing prices.** At any strictly positive `ψ` where the households'
demands add up to the aggregate endowment payoff, asset prices `q = qp ψ d` (arbitrage-free)
and suitable portfolios form an equilibrium: asset markets clear exactly (`Σ_i θ_i = Σ_i e_i`),
consumption is positive, and every household is optimal. Existence of such `ψ` is NOT proved
here. -/
theorem equilibrium_of_zero_excess {I : Type*} [Fintype I] [Nonempty S] (i0 : I)
    (π : I → S → ℝ) (hπ : ∀ i s, 0 < π i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i)
    (u : I → ℝ → ℝ) (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) (d : J → S → ℝ)
    (e : I → J → ℝ) (he : ∀ i s, 0 < pay d (e i) s) (ψ : S → ℝ) (hψ : ∀ s, 0 < ψ s)
    (hclear : ∀ s, ∑ i, dem (π i) (u i) d (e i) ψ s = ∑ i, pay d (e i) s) :
    ∃ θ : I → J → ℝ, ∑ i, θ i = ∑ i, e i ∧ ∀ i, (∀ s, 0 < pay d (θ i) s) ∧
      cost (qp ψ d) (θ i) ≤ cost (qp ψ d) (e i) ∧
      ∀ θ' : J → ℝ, cost (qp ψ d) θ' ≤ cost (qp ψ d) (e i) → (∀ s, 0 < pay d θ' s) →
        EU (π i) (u i) d θ' ≤ EU (π i) (u i) d (θ i) := by
  have hO := fun i => dem_spec (π i) (hπ i) (γ i) (hγ i) (u i) (hu i) d ψ hψ (e i) (he i)
  obtain ⟨θ, hs, hi⟩ := equilibrium_of_payoff_clearing i0 π u d e ψ _ hO hclear
  refine ⟨θ, hs, fun i => ⟨fun s => ?_, (hi i).2.1, (hi i).2.2⟩⟩
  rw [(hi i).1 s]
  exact (hO i).2.1 s

end IncompleteMarketsExistence

end

#print axioms IncompleteMarketsExistence.exists_optimum
#print axioms IncompleteMarketsExistence.optimum_payoff_unique
#print axioms IncompleteMarketsExistence.opt_exists
#print axioms IncompleteMarketsExistence.opt_unique
#print axioms IncompleteMarketsExistence.opt_le
#print axioms IncompleteMarketsExistence.opt_floor
#print axioms IncompleteMarketsExistence.V_contAt
#print axioms IncompleteMarketsExistence.dem_spec
#print axioms IncompleteMarketsExistence.dem_continuousAt
#print axioms IncompleteMarketsExistence.budget_binds
#print axioms IncompleteMarketsExistence.walras
#print axioms IncompleteMarketsExistence.equilibrium_of_payoff_clearing
#print axioms IncompleteMarketsExistence.equilibrium_of_zero_excess
