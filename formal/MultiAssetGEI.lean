import Mathlib

/-!
# Stage 371: many assets, one date: optimal portfolios, state prices, and an equilibrium

Stage 366 proved that the one-date economy with an equity and a bond has an equilibrium when
households differ in CRRA risk aversion. This file goes beyond two assets.

Setup: finitely many states `s` with probabilities `π s`, finitely many assets `j` with payoffs
`d j s` (any sign; no completeness assumed), asset prices `q j`. A portfolio `θ` pays
`pay d θ s = Σ_j θ j d j s` and costs `cost q θ = Σ_j q j θ j`. Households have marginal utility
`c ^ (−γ)` with `γ > 0` (log and every power utility). `mu θ j = Σ_s π s (pay θ s) ^ (−γ) d j s`
is the marginal value of asset `j` at portfolio `θ`.

The individual problem, for any number of assets:

* `euler_sufficient`: if a portfolio with positive consumption has marginal values proportional
  to prices (`mu θ j = λ q j`, `λ ≥ 0`), it is optimal among all portfolios that cost no more and
  give positive consumption (concavity through the mean value theorem, `concave_le`).
* `unique_optimum`: with positive probabilities and no redundant assets (no nonzero portfolio
  pays zero in every state), such an optimum is the only one.
* `euler_necessary`: conversely, at any optimal portfolio, marginal values are proportional to
  prices (`mu θ j · q k = mu θ k · q j` for every pair; the derivative along each zero-cost
  trade vanishes).
* `state_prices`: hence, if some asset with positive price pays nonnegative amounts and a
  positive amount in some state, an optimal portfolio exists only at prices that are given by
  strictly positive state prices, `q j = Σ_s ψ s d j s` (the prices admit no arbitrage).

Equilibrium:

* **`exists_equilibrium_common`**: with any number of assets, any payoffs, and any number of
  households who share one CRRA coefficient but hold different endowment portfolios (each
  giving positive consumption in every state), an equilibrium exists. Prices are the marginal
  values at the aggregate endowment, `q j = Σ_s π s Y s ^ (−γ) d j s`; each household sells its
  endowment and buys the share `a i` (its wealth over total wealth) of the market portfolio, which
  is optimal for it, and asset markets clear asset by asset. Households trade whenever their
  endowment portfolio is not a multiple of the aggregate one.

Limits: one date and common beliefs. The equilibrium theorem needs a common CRRA coefficient;
existence of equilibrium with many assets and heterogeneous risk aversion (stage 366 covers two
assets) is not proved here. For that one would also need existence of each household's optimum
at arbitrary no-arbitrage prices and continuity of demand in a multi-dimensional price, followed
by a fixed point argument; none of these is in this file. Uniqueness of the equilibrium and
multi-date economies are not covered.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace MultiAssetGEI

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

variable {S J : Type*} [Fintype S] [Fintype J]

/-- State-`s` payoff of portfolio `θ`. -/
def pay (d : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * d j s

/-- Cost of portfolio `θ` at prices `q`. -/
def cost (q θ : J → ℝ) : ℝ := ∑ j, q j * θ j

/-- Expected utility of portfolio `θ`. -/
def EU (π : S → ℝ) (u : ℝ → ℝ) (d : J → S → ℝ) (θ : J → ℝ) : ℝ := ∑ s, π s * u (pay d θ s)

/-- Marginal value of asset `j` at portfolio `θ`. -/
def mu (π : S → ℝ) (γ : ℝ) (d : J → S → ℝ) (θ : J → ℝ) (j : J) : ℝ :=
  ∑ s, π s * pay d θ s ^ (-γ) * d j s

omit [Fintype S] in
theorem pay_eq (d : J → S → ℝ) (x : J → ℝ) (s : S) : pay d x s = ∑ j, x j * d j s := rfl

omit [Fintype S] in
theorem pay_line (d : J → S → ℝ) (θ v : J → ℝ) (t : ℝ) (s : S) :
    pay d (fun i => θ i + t * v i) s = pay d θ s + t * pay d v s := by
  unfold pay
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cost_line (q θ v : J → ℝ) (t : ℝ) :
    cost q (fun i => θ i + t * v i) = cost q θ + t * cost q v := by
  unfold cost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
theorem pay_smul (d : J → S → ℝ) (a : ℝ) (x : J → ℝ) (s : S) :
    pay d (fun j => a * x j) s = a * pay d x s := by
  unfold pay
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cost_smul (q : J → ℝ) (a : ℝ) (x : J → ℝ) :
    cost q (fun j => a * x j) = a * cost q x := by
  unfold cost
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cost_smul_left (q : J → ℝ) (a : ℝ) (x : J → ℝ) :
    cost (fun j => a * q j) x = a * cost q x := by
  unfold cost
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
theorem pay_sum {I : Type*} [Fintype I] (d : J → S → ℝ) (e : I → J → ℝ) (s : S) :
    pay d (fun j => ∑ i, e i j) s = ∑ i, pay d (e i) s := by
  unfold pay
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem cost_sum {I : Type*} [Fintype I] (q : J → ℝ) (e : I → J → ℝ) :
    cost q (fun j => ∑ i, e i j) = ∑ i, cost q (e i) := by
  unfold cost
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- The cost of `x` at the marginal-value prices of `θ` is the marginal-utility-weighted
payoff of `x`. -/
theorem cost_mu (π : S → ℝ) (γ : ℝ) (d : J → S → ℝ) (θ x : J → ℝ) :
    cost (mu π γ d θ) x = ∑ s, π s * pay d θ s ^ (-γ) * pay d x s := by
  unfold cost mu
  simp_rw [pay_eq d x, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

/-- The utility gain from moving to `θ'` is at most its value at the marginal-value prices
of `θ`. -/
theorem eu_diff_le (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (θ θ' : J → ℝ)
    (hF : ∀ s, 0 < pay d θ s) (hF' : ∀ s, 0 < pay d θ' s) :
    EU π u d θ' - EU π u d θ ≤ cost (mu π γ d θ) θ' - cost (mu π γ d θ) θ := by
  rw [cost_mu, cost_mu, ← Finset.sum_sub_distrib]
  unfold EU
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := concave_le γ hγ u hu (hF s) (hF' s)
  have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
  linarith

/-- Strict version: if the payoffs differ in some state. -/
theorem eu_diff_lt (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (θ θ' : J → ℝ)
    (hF : ∀ s, 0 < pay d θ s) (hF' : ∀ s, 0 < pay d θ' s) (s0 : S)
    (hs0 : pay d θ s0 ≠ pay d θ' s0) :
    EU π u d θ' - EU π u d θ < cost (mu π γ d θ) θ' - cost (mu π γ d θ) θ := by
  rw [cost_mu, cost_mu, ← Finset.sum_sub_distrib]
  unfold EU
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ _, ?_⟩
  · have h1 := concave_le γ hγ u hu (hF s) (hF' s)
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s).le
    linarith
  · have h1 := concave_lt γ hγ u hu (hF s0) (hF' s0) hs0
    have h2 := mul_lt_mul_of_pos_left h1 (hπ s0)
    linarith

/-- **First-order conditions are sufficient**, with any number of assets. -/
theorem euler_sufficient (π : S → ℝ) (hπ : ∀ s, 0 ≤ π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (q θ θ' : J → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hF : ∀ s, 0 < pay d θ s) (hF' : ∀ s, 0 < pay d θ' s)
    (hE : ∀ j, mu π γ d θ j = lam * q j) (hb : cost q θ' ≤ cost q θ) :
    EU π u d θ' ≤ EU π u d θ := by
  have h := eu_diff_le π hπ γ hγ u hu d θ θ' hF hF'
  have e : mu π γ d θ = fun j => lam * q j := funext hE
  rw [e, cost_smul_left, cost_smul_left] at h
  have : lam * (cost q θ' - cost q θ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  linarith

/-- **The optimum is unique** when no portfolio other than zero pays zero in every state. -/
theorem unique_optimum (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ)
    (hli : ∀ v : J → ℝ, (∀ s, ∑ j, v j * d j s = 0) → v = 0) (q θ θ' : J → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hF : ∀ s, 0 < pay d θ s) (hF' : ∀ s, 0 < pay d θ' s)
    (hE : ∀ j, mu π γ d θ j = lam * q j) (hb : cost q θ' ≤ cost q θ)
    (hopt : EU π u d θ ≤ EU π u d θ') : θ' = θ := by
  by_cases hall : ∀ s, pay d θ s = pay d θ' s
  · have hv := hli (fun j => θ' j - θ j) fun s => by
      have := (hall s).symm
      unfold pay at this
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by ring
    funext j
    have := congrFun hv j
    simp only [Pi.zero_apply] at this
    linarith
  · push Not at hall
    obtain ⟨s0, hs0⟩ := hall
    have h := eu_diff_lt π hπ γ hγ u hu d θ θ' hF hF' s0 hs0
    have e : mu π γ d θ = fun j => lam * q j := funext hE
    rw [e, cost_smul_left, cost_smul_left] at h
    have : lam * (cost q θ' - cost q θ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
    linarith

/-- **First-order conditions are necessary**: at an optimal portfolio, marginal values are
proportional to prices. -/
theorem euler_necessary (π : S → ℝ) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (q θ : J → ℝ) (k : J)
    (hF : ∀ s, 0 < pay d θ s)
    (hopt : ∀ θ', cost q θ' = cost q θ → (∀ s, 0 < pay d θ' s) → EU π u d θ' ≤ EU π u d θ) :
    ∀ j, mu π γ d θ j * q k = mu π γ d θ k * q j := by
  intro j
  set v : J → ℝ := fun i => (if i = j then q k else 0) - (if i = k then q j else 0) with hv
  have hcv : cost q v = 0 := by
    simp only [cost, hv, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Fintype.sum_ite_eq']
    ring
  have hpv : ∀ s, pay d v s = q k * d j s - q j * d k s := by
    intro s
    simp only [pay, hv, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
      Fintype.sum_ite_eq']
  set f : ℝ → ℝ := fun t => EU π u d (fun i => θ i + t * v i) with hf
  have hderiv : HasDerivAt f (∑ s, π s * pay d θ s ^ (-γ) * pay d v s) 0 := by
    have e : f = fun t => ∑ s, π s * u (pay d θ s + t * pay d v s) := by
      funext t
      simp only [hf, EU, pay_line]
    rw [e]
    apply HasDerivAt.fun_sum
    intro s _
    have hin : HasDerivAt (fun t => pay d θ s + t * pay d v s) (pay d v s) 0 :=
      (((hasDerivAt_id' (0 : ℝ)).mul_const (pay d v s)).const_add (pay d θ s)).congr_deriv
        (one_mul _)
    have hpos : 0 < pay d θ s + 0 * pay d v s := by simpa using hF s
    exact (((hu _ hpos).comp (0 : ℝ) hin).const_mul (π s)).congr_deriv
      (by rw [zero_mul, add_zero]; ring)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < pay d θ s + t * pay d v s := by
    refine Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun t : ℝ => pay d θ s + t * pay d v s :=
      continuous_const.add (continuous_id.mul continuous_const)
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hF s))
  have hmax : IsLocalMax f 0 := by
    unfold IsLocalMax IsMaxFilter
    filter_upwards [hev] with t ht
    have hb : cost q (fun i => θ i + t * v i) = cost q θ := by
      rw [cost_line, hcv, mul_zero, add_zero]
    have := hopt _ hb fun s => by rw [pay_line]; exact ht s
    simpa [hf] using this
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hx : ∑ s, π s * pay d θ s ^ (-γ) * pay d v s =
      q k * mu π γ d θ j - q j * mu π γ d θ k := by
    unfold mu
    simp_rw [hpv]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hx] at h0
  linarith

/-- **Optimal portfolios exist only at arbitrage-free prices**: the prices are then given by
strictly positive state prices. -/
theorem state_prices (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (q θ : J → ℝ) (k : J)
    (hqk : 0 < q k) (hdk : ∀ s, 0 ≤ d k s) (s1 : S) (hds : 0 < d k s1)
    (hF : ∀ s, 0 < pay d θ s)
    (hopt : ∀ θ', cost q θ' = cost q θ → (∀ s, 0 < pay d θ' s) → EU π u d θ' ≤ EU π u d θ) :
    ∃ ψ : S → ℝ, (∀ s, 0 < ψ s) ∧ ∀ j, q j = ∑ s, ψ s * d j s := by
  have hmuk : 0 < mu π γ d θ k :=
    Finset.sum_pos' (fun s _ => mul_nonneg (mul_nonneg (hπ s).le
      (Real.rpow_nonneg (hF s).le _)) (hdk s))
      ⟨s1, Finset.mem_univ _, mul_pos (mul_pos (hπ s1) (Real.rpow_pos_of_pos (hF s1) _)) hds⟩
  have hn := euler_necessary π γ u hu d q θ k hF hopt
  refine ⟨fun s => π s * pay d θ s ^ (-γ) * q k / mu π γ d θ k,
    fun s => div_pos (mul_pos (mul_pos (hπ s) (Real.rpow_pos_of_pos (hF s) _)) hqk) hmuk,
    fun j => ?_⟩
  have hj := hn j
  set M := mu π γ d θ k with hM
  have hsum : ∑ s, π s * pay d θ s ^ (-γ) * q k / M * d j s = mu π γ d θ j * q k / M := by
    unfold mu
    rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum, hj]
  field_simp

/-! ## Equilibrium with many assets and a common risk aversion -/

/-- **Existence of equilibrium with any number of assets** when households share one CRRA
coefficient but hold different endowment portfolios. `q` are asset prices, `θ i` household
`i`'s portfolio, `a i` its share of the market portfolio. -/
theorem exists_equilibrium_common {I : Type*} [Fintype I] [Nonempty I] [Nonempty S] (π : S → ℝ)
    (hπ : ∀ s, 0 < π s) (γ : ℝ) (hγ : 0 < γ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (d : J → S → ℝ) (e : I → J → ℝ)
    (he : ∀ i s, 0 < pay d (e i) s) :
    ∃ (q : J → ℝ) (θ : I → J → ℝ) (a : I → ℝ),
      (∀ i, cost q (θ i) = cost q (e i)) ∧ (∀ i s, 0 < pay d (θ i) s) ∧
      (∀ i θ', cost q θ' ≤ cost q (e i) → (∀ s, 0 < pay d θ' s) →
        EU π u d θ' ≤ EU π u d (θ i)) ∧
      (∀ j, ∑ i, θ i j = ∑ i, e i j) ∧
      (∀ i, 0 < a i) ∧ (∀ i s, pay d (θ i) s = a i * ∑ k, pay d (e k) s) := by
  set ebar : J → ℝ := fun j => ∑ i, e i j with hebar
  have hY : ∀ s, pay d ebar s = ∑ i, pay d (e i) s := fun s => pay_sum d e s
  have hYpos : ∀ s, 0 < pay d ebar s := fun s => by
    rw [hY]
    exact Finset.sum_pos (fun i _ => he i s) Finset.univ_nonempty
  set q : J → ℝ := mu π γ d ebar with hq
  set W : I → ℝ := fun i => cost q (e i) with hW
  have hWpos : ∀ i, 0 < W i := fun i => by
    simp only [hW, hq, cost_mu]
    exact Finset.sum_pos (fun s _ => mul_pos (mul_pos (hπ s)
      (Real.rpow_pos_of_pos (hYpos s) _)) (he i s)) Finset.univ_nonempty
  have hWt : cost q ebar = ∑ i, W i := cost_sum q e
  have hWtpos : 0 < cost q ebar := by
    rw [hWt]
    exact Finset.sum_pos (fun i _ => hWpos i) Finset.univ_nonempty
  set a : I → ℝ := fun i => W i / cost q ebar with ha
  have hapos : ∀ i, 0 < a i := fun i => div_pos (hWpos i) hWtpos
  set θ : I → J → ℝ := fun i j => a i * ebar j with hθ
  have hpay : ∀ i s, pay d (θ i) s = a i * pay d ebar s := fun i s => pay_smul d (a i) ebar s
  have hcost : ∀ i, cost q (θ i) = cost q (e i) := fun i => by
    have h1 : cost q (θ i) = a i * cost q ebar := cost_smul q (a i) ebar
    rw [h1]
    exact div_mul_cancel₀ _ hWtpos.ne'
  have hmu : ∀ i j, mu π γ d (θ i) j = a i ^ (-γ) * q j := by
    intro i j
    rw [hq]
    simp only [mu, hpay, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Real.mul_rpow (hapos i).le (hYpos s).le]
    ring
  refine ⟨q, θ, a, hcost, fun i s => ?_, ?_, ?_, hapos, fun i s => by rw [hpay, hY]⟩
  · rw [hpay]
    exact mul_pos (hapos i) (hYpos s)
  · intro i θ' hb hF'
    exact euler_sufficient π (fun s => (hπ s).le) γ hγ u hu d q (θ i) θ' (a i ^ (-γ))
      (Real.rpow_nonneg (hapos i).le _)
      (fun s => by rw [hpay]; exact mul_pos (hapos i) (hYpos s)) hF' (hmu i)
      (by rw [hcost i]; exact hb)
  · intro j
    have hsa : ∑ i, a i = 1 := by
      simp only [ha]
      rw [← Finset.sum_div, ← hWt]
      exact div_self hWtpos.ne'
    show ∑ i, a i * ebar j = ebar j
    rw [← Finset.sum_mul, hsa, one_mul]

end MultiAssetGEI

end

#print axioms MultiAssetGEI.concave_lt
#print axioms MultiAssetGEI.cost_mu
#print axioms MultiAssetGEI.euler_sufficient
#print axioms MultiAssetGEI.unique_optimum
#print axioms MultiAssetGEI.euler_necessary
#print axioms MultiAssetGEI.state_prices
#print axioms MultiAssetGEI.exists_equilibrium_common
