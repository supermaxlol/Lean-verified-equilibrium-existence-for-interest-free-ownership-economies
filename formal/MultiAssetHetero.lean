import FixedPointTheorems.brouwer
import Mathlib

/-!
# Stage 375: equilibrium with many assets and heterogeneous CRRA (complete markets)

Stage 366 proved existence with two assets (equity and a bond) and heterogeneous CRRA; stage 371
proved existence with any number of assets but a common CRRA coefficient. This file proves
existence with any number of assets and heterogeneous CRRA coefficients **when the assets span
every state-contingent payoff** (complete markets), by the Negishi method.

Setup: households `i` with endowment `e i s > 0` in each state, CRRA marginal utility
`c ^ (−γ i)` (`γ i > 0`), common probabilities `π s > 0`; aggregate output `agg e s`.

* `root_exists`, `F_lt`: for welfare weights `l ≥ 0`, not all zero, and output `y > 0`, the
  multiplier `m > 0` with `Σ i (l i / m) ^ (1 / γ i) = y` exists and is unique.
* `mu_continuous`: that multiplier depends continuously on the weights on the simplex.
* `walras`: the transfers `T i` (value of the weighted Pareto allocation `alloc` minus the value
  of the endowment, at state prices `ψ s = π s · m s`) sum to zero.
* `exists_weights`: Brouwer on the simplex gives weights at which every transfer is zero, and
  every weight is positive.
* **`exists_ad_equilibrium`**: an Arrow–Debreu equilibrium in state-contingent claims: positive
  state prices and positive consumption, each household's consumption affordable and optimal
  among all affordable positive consumption plans, and every state market clears.
* **`exists_equilibrium_complete`**: with `J` assets whose payoffs `d j s` span every payoff and
  are non-redundant, and endowment portfolios paying a positive amount in every state, there are
  arbitrage-free asset prices `q j = Σ s ψ s d j s` and portfolios such that each portfolio
  costs the endowment portfolio, gives positive consumption, is optimal among all affordable
  portfolios with positive consumption, and every asset market clears.

Limits: one date, common beliefs, CRRA marginal utility. The asset result needs COMPLETE markets
(the spanning hypothesis); with incomplete markets the Negishi allocation need not be
attainable and the many-asset heterogeneous-CRRA existence remains open (stage 366 covers two
assets, stage 371 a common coefficient). Existence of each household's optimum at arbitrary
arbitrage-free prices and continuity of portfolio demand in prices are not proved here.
Uniqueness of the equilibrium is not proved.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace MultiAssetHetero

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

variable {I : Type*} [Fintype I]

/-- The simplex of welfare weights. -/
def Simp (I : Type*) [Fintype I] : Set (I → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem convex_Simp : Convex ℝ (Simp I) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun h => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 h)) (mul_nonneg hb (hy.1 h))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    linarith

theorem compact_Simp : IsCompact (Simp I) := by
  have hsub : Simp I ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
    intro x hx h _
    refine ⟨hx.1 h, ?_⟩
    rw [← hx.2]
    exact Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ h)
  have hcl : IsClosed (Simp I) := by
    have e : Simp I = (⋂ h, {x : I → ℝ | 0 ≤ x h}) ∩ {x | ∑ h, x h = 1} := by
      ext x
      simp [Simp]
    rw [e]
    exact (isClosed_iInter fun h => isClosed_le continuous_const (continuous_apply h)).inter
      (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

theorem exists_pos_of_Simp {l : I → ℝ} (hl : l ∈ Simp I) : ∃ k, 0 < l k := by
  by_contra hne
  push Not at hne
  have h0 : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hne i) (hl.1 i)
  rw [hl.2] at h0
  norm_num at h0

/-! ## The Pareto multiplier -/

/-- Aggregate demand of the weighted Pareto allocation at multiplier `m`. -/
def F (γ l : I → ℝ) (m : ℝ) : ℝ := ∑ i, (l i / m) ^ (γ i)⁻¹

omit [Fintype I] in
theorem term_le (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : ∀ i, 0 ≤ l i) {m m' : ℝ}
    (hm : 0 < m) (hle : m ≤ m') (i : I) : (l i / m') ^ (γ i)⁻¹ ≤ (l i / m) ^ (γ i)⁻¹ := by
  have hm' : 0 < m' := by linarith
  have h : l i / m' ≤ l i / m := by
    rw [div_le_div_iff₀ hm' hm]
    nlinarith [hl i]
  exact Real.rpow_le_rpow (div_nonneg (hl i) hm'.le) h (inv_nonneg.2 (hγ i).le)

theorem F_le (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : ∀ i, 0 ≤ l i) {m m' : ℝ}
    (hm : 0 < m) (hle : m ≤ m') : F γ l m' ≤ F γ l m :=
  Finset.sum_le_sum fun i _ => term_le γ l hγ hl hm hle i

/-- **The aggregate is strictly decreasing in the multiplier.** -/
theorem F_lt (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : ∀ i, 0 ≤ l i) (k : I) (hk : 0 < l k)
    {m m' : ℝ} (hm : 0 < m) (hlt : m < m') : F γ l m' < F γ l m := by
  have hm' : 0 < m' := by linarith
  refine Finset.sum_lt_sum (fun i _ => term_le γ l hγ hl hm hlt.le i) ⟨k, Finset.mem_univ _, ?_⟩
  have h : l k / m' < l k / m := by
    rw [div_lt_div_iff₀ hm' hm]
    nlinarith
  exact Real.rpow_lt_rpow (div_nonneg (hl k) hm'.le) h (inv_pos.2 (hγ k))

theorem F_continuous_l (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (m : ℝ) :
    Continuous fun l : I → ℝ => F γ l m :=
  continuous_finsetSum _ fun i _ =>
    (show Continuous fun l : I → ℝ => l i / m from
      (continuous_apply i : Continuous fun l : I → ℝ => l i).div_const m).rpow_const fun _ => Or.inr (inv_nonneg.2 (hγ i).le)

theorem F_continuousOn_m (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) :
    ContinuousOn (fun m => F γ l m) (Ioi 0) :=
  continuousOn_finsetSum _ fun i _ =>
    (continuousOn_const.div continuousOn_id fun _ hx => (ne_of_gt hx)).rpow_const
      fun _ _ => Or.inr (inv_nonneg.2 (hγ i).le)

/-- **The multiplier exists.** -/
theorem root_exists (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : ∀ i, 0 ≤ l i) (k : I)
    (hk : 0 < l k) (y : ℝ) (hy : 0 < y) : ∃ m, 0 < m ∧ F γ l m = y := by
  -- large multipliers: the aggregate tends to zero
  have htop : Tendsto (fun m => F γ l m) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset I) fun i _ =>
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (l i)).rpow_const
        (p := (γ i)⁻¹) (Or.inr (inv_nonneg.2 (hγ i).le))
    have e : ∀ i, (l i * (0 : ℝ)) ^ (γ i)⁻¹ = 0 := fun i => by
      rw [mul_zero, Real.zero_rpow (inv_ne_zero (hγ i).ne')]
    simp only [e, Finset.sum_const_zero] at h
    refine h.congr fun m => ?_
    unfold F
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  obtain ⟨m1, hm1y, hm1⟩ := ((htop.eventually (gt_mem_nhds hy)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  -- small multipliers: household `k`'s term alone exceeds `y`
  have hzero : Tendsto (fun m => (l k / m) ^ (γ k)⁻¹) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun m : ℝ => l k * m⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop hk
    exact ((tendsto_rpow_atTop (inv_pos.2 (hγ k))).comp h1).congr fun m => by
      simp [Function.comp, div_eq_mul_inv]
  obtain ⟨m0, hm0y, hm0⟩ := ((hzero.eventually (eventually_gt_atTop y)).and
    self_mem_nhdsWithin).exists
  have hm0' : 0 < m0 := hm0
  have hF0 : y < F γ l m0 := by
    refine lt_of_lt_of_le hm0y ?_
    exact Finset.single_le_sum (f := fun i => (l i / m0) ^ (γ i)⁻¹)
      (fun i _ => Real.rpow_nonneg (div_nonneg (hl i) hm0'.le) _) (Finset.mem_univ k)
  have hle : m0 ≤ m1 := by
    by_contra h
    push Not at h
    have := F_le γ l hγ hl hm1 h.le
    linarith
  have hcont : ContinuousOn (fun m => F γ l m) (Icc m0 m1) :=
    (F_continuousOn_m γ l hγ).mono fun x hx => lt_of_lt_of_le hm0' hx.1
  obtain ⟨m, hm, hFm⟩ := intermediate_value_Icc' hle hcont ⟨hm1y.le, hF0.le⟩
  exact ⟨m, lt_of_lt_of_le hm0' hm.1, hFm⟩

/-- The multiplier as a function of the weights. -/
def mu (γ l : I → ℝ) (y : ℝ) : ℝ :=
  if h : ∃ m, 0 < m ∧ F γ l m = y then Classical.choose h else 1

theorem mu_spec (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : l ∈ Simp I) (y : ℝ) (hy : 0 < y) :
    0 < mu γ l y ∧ F γ l (mu γ l y) = y := by
  obtain ⟨k, hk⟩ := exists_pos_of_Simp hl
  have h := root_exists γ l hγ hl.1 k hk y hy
  unfold mu
  split_ifs
  exact Classical.choose_spec h

theorem mu_gt (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : l ∈ Simp I) (y : ℝ) (hy : 0 < y)
    {p : ℝ} (_hp : 0 < p) (hF : y < F γ l p) : p < mu γ l y := by
  obtain ⟨hm, hFm⟩ := mu_spec γ l hγ hl y hy
  by_contra h
  push Not at h
  have := F_le γ l hγ hl.1 hm h
  linarith

theorem mu_lt (γ l : I → ℝ) (hγ : ∀ i, 0 < γ i) (hl : l ∈ Simp I) (y : ℝ) (hy : 0 < y)
    {p : ℝ} (hp : 0 < p) (hF : F γ l p < y) : mu γ l y < p := by
  obtain ⟨hm, hFm⟩ := mu_spec γ l hγ hl y hy
  by_contra h
  push Not at h
  have := F_le γ l hγ hl.1 hp h
  linarith

/-- **The multiplier is continuous in the weights** on the simplex. -/
theorem mu_continuous (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (y : ℝ) (hy : 0 < y) :
    Continuous fun q : Simp I => mu γ q.1 y := by
  rw [continuous_iff_continuousAt]
  intro q0
  obtain ⟨hm0, hF0⟩ := mu_spec γ q0.1 hγ q0.2 y hy
  obtain ⟨k, hk⟩ := exists_pos_of_Simp q0.2
  have cF : ∀ p, Continuous fun q : Simp I => F γ q.1 p := fun p =>
    (F_continuous_l γ hγ p).comp continuous_subtype_val
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set p := max a (mu γ q0.1 y / 2) with hp
    have hp0 : 0 < p := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hpm : p < mu γ q0.1 y := max_lt ha (by linarith)
    have hFp : y < F γ q0.1 p := by
      have := F_lt γ q0.1 hγ q0.2.1 k hk hp0 hpm
      linarith
    filter_upwards [(cF p).continuousAt.eventually (lt_mem_nhds hFp)] with q hq
    exact lt_of_le_of_lt (le_max_left _ _) (mu_gt γ q.1 hγ q.2 y hy hp0 hq)
  · set p := (mu γ q0.1 y + b) / 2 with hp
    have hp0 : 0 < p := by linarith
    have hpm : mu γ q0.1 y < p := by linarith
    have hFp : F γ q0.1 p < y := by
      have := F_lt γ q0.1 hγ q0.2.1 k hk hm0 hpm
      linarith
    filter_upwards [(cF p).continuousAt.eventually (gt_mem_nhds hFp)] with q hq
    exact lt_trans (mu_lt γ q.1 hγ q.2 y hy hp0 hq) (by linarith)

/-! ## Allocation, transfers and the Negishi fixed point -/

variable {S : Type*} [Fintype S]

/-- Aggregate endowment. -/
def agg (e : I → S → ℝ) (s : S) : ℝ := ∑ i, e i s

/-- The weighted Pareto allocation. -/
def alloc (γ : I → ℝ) (e : I → S → ℝ) (l : I → ℝ) (i : I) (s : S) : ℝ :=
  (l i / mu γ l (agg e s)) ^ (γ i)⁻¹

/-- Supporting state prices. -/
def psi (π : S → ℝ) (γ : I → ℝ) (e : I → S → ℝ) (l : I → ℝ) (s : S) : ℝ :=
  π s * mu γ l (agg e s)

/-- Transfer needed by household `i`: value of its allocation minus value of its endowment. -/
def T (π : S → ℝ) (γ : I → ℝ) (e : I → S → ℝ) (l : I → ℝ) (i : I) : ℝ :=
  ∑ s, psi π γ e l s * (alloc γ e l i s - e i s)

def mx (π : S → ℝ) (γ : I → ℝ) (e : I → S → ℝ) (l : I → ℝ) (i : I) : ℝ :=
  max 0 (-T π γ e l i)

/-- The Negishi map on the simplex: raise the weight of households in deficit. -/
def Φ (π : S → ℝ) (γ : I → ℝ) (e : I → S → ℝ) (l : I → ℝ) (i : I) : ℝ :=
  (l i + mx π γ e l i) / (1 + ∑ k, mx π γ e l k)

omit [Fintype S] in
theorem agg_pos [Nonempty I] (e : I → S → ℝ) (he : ∀ i s, 0 < e i s) (s : S) : 0 < agg e s :=
  Finset.sum_pos (fun i _ => he i s) Finset.univ_nonempty

omit [Fintype S] in
theorem alloc_sum [Nonempty I] (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (e : I → S → ℝ)
    (he : ∀ i s, 0 < e i s) (l : I → ℝ) (hl : l ∈ Simp I) (s : S) :
    ∑ i, alloc γ e l i s = agg e s :=
  (mu_spec γ l hγ hl _ (agg_pos e he s)).2

/-- **Walras' law for transfers.** -/
theorem walras [Nonempty I] (π : S → ℝ) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (e : I → S → ℝ)
    (he : ∀ i s, 0 < e i s) (l : I → ℝ) (hl : l ∈ Simp I) : ∑ i, T π γ e l i = 0 := by
  unfold T
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, alloc_sum γ hγ e he l hl s]
  unfold agg
  rw [sub_self, mul_zero]

theorem T_neg_of_zero [Nonempty I] [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (γ : I → ℝ)
    (hγ : ∀ i, 0 < γ i) (e : I → S → ℝ) (he : ∀ i s, 0 < e i s) (l : I → ℝ) (hl : l ∈ Simp I)
    (i : I) (hi : l i = 0) : T π γ e l i < 0 := by
  have h : ∀ s ∈ Finset.univ, psi π γ e l s * (alloc γ e l i s - e i s) < (fun _ => (0 : ℝ)) s := by
    intro s _
    have ha : alloc γ e l i s = 0 := by
      unfold alloc
      rw [hi, zero_div, Real.zero_rpow (inv_ne_zero (hγ i).ne')]
    rw [ha]
    exact mul_neg_of_pos_of_neg
      (mul_pos (hπ s) (mu_spec γ l hγ hl _ (agg_pos e he s)).1) (by linarith [he i s])
  have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty h
  simpa [T] using this

/-- **Negishi weights**: there are positive weights on the simplex at which no household needs a
transfer. -/
theorem exists_weights [Nonempty I] [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s)
    (γ : I → ℝ) (hγ : ∀ i, 0 < γ i) (e : I → S → ℝ) (he : ∀ i s, 0 < e i s) :
    ∃ l ∈ Simp I, (∀ i, 0 < l i) ∧ ∀ i, T π γ e l i = 0 := by
  have hmx0 : ∀ l i, 0 ≤ mx π γ e l i := fun l i => le_max_left _ _
  have hM0 : ∀ l, 0 ≤ ∑ k, mx π γ e l k := fun l => Finset.sum_nonneg fun k _ => hmx0 l k
  have hmaps : ∀ l ∈ Simp I, Φ π γ e l ∈ Simp I := fun l hl =>
    ⟨fun i => div_nonneg (add_nonneg (hl.1 i) (hmx0 l i)) (by linarith [hM0 l]), by
      unfold Φ
      rw [← Finset.sum_div, Finset.sum_add_distrib, hl.2, div_self (by linarith [hM0 l])]⟩
  have cmu : ∀ s, Continuous fun q : Simp I => mu γ q.1 (agg e s) := fun s =>
    mu_continuous γ hγ _ (agg_pos e he s)
  have cq : ∀ i, Continuous fun q : Simp I => q.1 i := fun i =>
    (continuous_apply i).comp continuous_subtype_val
  have calloc : ∀ i s, Continuous fun q : Simp I => alloc γ e q.1 i s := fun i s =>
    ((cq i).div (cmu s) fun q => (mu_spec γ q.1 hγ q.2 _ (agg_pos e he s)).1.ne').rpow_const
      fun _ => Or.inr (inv_nonneg.2 (hγ i).le)
  have cT : ∀ i, Continuous fun q : Simp I => T π γ e q.1 i := fun i =>
    continuous_finsetSum _ fun s _ =>
      (continuous_const.mul (cmu s)).mul ((calloc i s).sub continuous_const)
  have cmx : ∀ i, Continuous fun q : Simp I => mx π γ e q.1 i := fun i =>
    continuous_const.max (cT i).neg
  have cΦ : Continuous fun q : Simp I => Φ π γ e q.1 := by
    refine continuous_pi fun i => ?_
    exact ((cq i).add (cmx i)).div (continuous_const.add (continuous_finsetSum _ fun k _ => cmx k))
      fun q => by linarith [hM0 q.1]
  let f : C(Simp I, Simp I) := ⟨fun q => ⟨Φ π γ e q.1, hmaps q.1 q.2⟩, cΦ.subtype_mk _⟩
  have hne : (Simp I).Nonempty := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨fun i => if i = i0 then 1 else 0, fun i => by
      show (0:ℝ) ≤ if i = i0 then 1 else 0
      split_ifs <;> norm_num, ?_⟩
    simp
  obtain ⟨q, hq⟩ := brouwer_fixed_point (Simp I) convex_Simp compact_Simp hne f
  have hfix : Φ π γ e q.1 = q.1 := congrArg Subtype.val hq
  set l := q.1 with hldef
  have hl : l ∈ Simp I := q.2
  set M := ∑ k, mx π γ e l k with hM
  have hmxM : ∀ i, mx π γ e l i = l i * M := fun i => by
    have h := congrFun hfix i
    unfold Φ at h
    rw [div_eq_iff (by linarith [hM0 l])] at h
    linarith
  have hW := walras π γ hγ e he l hl
  have hMz : M = 0 := by
    by_contra hM1
    have hMp : 0 < M := lt_of_le_of_ne (hM0 l) (Ne.symm hM1)
    have hneg : ∀ i ∈ Finset.univ, T π γ e l i < (fun _ => (0 : ℝ)) i := by
      intro i _
      rcases (hl.1 i).lt_or_eq with hli | hli
      · have hpos : 0 < mx π γ e l i := by rw [hmxM i]; exact mul_pos hli hMp
        unfold mx at hpos
        by_contra hT
        push Not at hT
        rw [max_eq_left (by linarith)] at hpos
        exact lt_irrefl _ hpos
      · exact T_neg_of_zero π hπ γ hγ e he l hl i hli.symm
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hneg
    simp only [Finset.sum_const_zero] at this
    linarith
  have hTnn : ∀ i, 0 ≤ T π γ e l i := fun i => by
    have h1 : mx π γ e l i = 0 := by rw [hmxM i, hMz, mul_zero]
    have h2 : -T π γ e l i ≤ mx π γ e l i := le_max_right _ _
    linarith
  have hT0 : ∀ i, T π γ e l i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hTnn i).1 hW i (Finset.mem_univ i)
  refine ⟨l, hl, fun i => ?_, hT0⟩
  rcases (hl.1 i).lt_or_eq with hli | hli
  · exact hli
  · have := T_neg_of_zero π hπ γ hγ e he l hl i hli.symm
    rw [hT0 i] at this
    exact absurd this (lt_irrefl _)

theorem mu_pow (γ x : ℝ) (hγ : 0 < γ) (hx : 0 < x) : (x ^ γ⁻¹) ^ (-γ) = x⁻¹ := by
  rw [← Real.rpow_mul hx.le, mul_neg, inv_mul_cancel₀ hγ.ne', Real.rpow_neg_one]

/-- **Arrow–Debreu equilibrium in state-contingent claims with heterogeneous CRRA.** -/
theorem exists_ad_equilibrium [Nonempty I] [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s)
    (e : I → S → ℝ) (he : ∀ i s, 0 < e i s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i)
    (u : I → ℝ → ℝ) (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) :
    ∃ (ψ : S → ℝ) (c : I → S → ℝ), (∀ s, 0 < ψ s) ∧ (∀ i s, 0 < c i s) ∧
      (∀ i, ∑ s, ψ s * c i s = ∑ s, ψ s * e i s) ∧ (∀ s, ∑ i, c i s = ∑ i, e i s) ∧
      (∀ i (c' : S → ℝ), (∀ s, 0 < c' s) → ∑ s, ψ s * c' s ≤ ∑ s, ψ s * e i s →
        ∑ s, π s * u i (c' s) ≤ ∑ s, π s * u i (c i s)) := by
  obtain ⟨l, hl, hlpos, hT0⟩ := exists_weights π hπ γ hγ e he
  have hmu : ∀ s, 0 < mu γ l (agg e s) := fun s => (mu_spec γ l hγ hl _ (agg_pos e he s)).1
  have hc : ∀ i s, 0 < alloc γ e l i s := fun i s =>
    Real.rpow_pos_of_pos (div_pos (hlpos i) (hmu s)) _
  have hbud : ∀ i, ∑ s, psi π γ e l s * alloc γ e l i s = ∑ s, psi π γ e l s * e i s := by
    intro i
    have h := hT0 i
    unfold T at h
    simp only [mul_sub, Finset.sum_sub_distrib] at h
    linarith
  refine ⟨psi π γ e l, alloc γ e l, fun s => mul_pos (hπ s) (hmu s), hc, hbud,
    fun s => alloc_sum γ hγ e he l hl s, ?_⟩
  intro i c' hc' hb
  have hmarg : ∀ s, alloc γ e l i s ^ (-γ i) = mu γ l (agg e s) / l i := fun s => by
    unfold alloc
    rw [mu_pow (γ i) _ (hγ i) (div_pos (hlpos i) (hmu s)), inv_div]
  have key : ∀ s, π s * u i (c' s) - π s * u i (alloc γ e l i s) ≤
      (l i)⁻¹ * (psi π γ e l s * c' s - psi π γ e l s * alloc γ e l i s) := by
    intro s
    have h := concave_le (γ i) (hγ i) (u i) (hu i) (hc i s) (hc' s)
    rw [hmarg s] at h
    have h2 := mul_le_mul_of_nonneg_left h (hπ s).le
    unfold psi
    calc π s * u i (c' s) - π s * u i (alloc γ e l i s)
        = π s * (u i (c' s) - u i (alloc γ e l i s)) := by ring
      _ ≤ π s * (mu γ l (agg e s) / l i * (c' s - alloc γ e l i s)) := h2
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => key s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hbud i] at hsum
  have : (l i)⁻¹ * (∑ s, psi π γ e l s * c' s - ∑ s, psi π γ e l s * e i s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hlpos i).le) (by linarith)
  linarith

/-! ## Assets -/

variable {J : Type*} [Fintype J]

/-- State-`s` payoff of portfolio `θ`. -/
def pay (d : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * d j s

/-- Cost of portfolio `θ` at prices `q`. -/
def cost (q θ : J → ℝ) : ℝ := ∑ j, q j * θ j

theorem cost_eq (d : J → S → ℝ) (ψ : S → ℝ) (θ : J → ℝ) :
    cost (fun j => ∑ s, ψ s * d j s) θ = ∑ s, ψ s * pay d θ s := by
  unfold cost pay
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Equilibrium with many assets and heterogeneous CRRA, complete markets.** Asset prices are
arbitrage-free (`q j = Σ s ψ s d j s` with `ψ > 0`). -/
theorem exists_equilibrium_complete [Nonempty I] [Nonempty S] (π : S → ℝ) (hπ : ∀ s, 0 < π s)
    (d : J → S → ℝ) (hspan : ∀ c : S → ℝ, ∃ θ : J → ℝ, ∀ s, pay d θ s = c s)
    (hnr : ∀ θ : J → ℝ, (∀ s, pay d θ s = 0) → θ = 0)
    (θ0 : I → J → ℝ) (hθ0 : ∀ i s, 0 < pay d (θ0 i) s) (γ : I → ℝ) (hγ : ∀ i, 0 < γ i)
    (u : I → ℝ → ℝ) (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) :
    ∃ (ψ : S → ℝ) (q : J → ℝ) (θ : I → J → ℝ), (∀ s, 0 < ψ s) ∧
      (∀ j, q j = ∑ s, ψ s * d j s) ∧ (∀ i, cost q (θ i) = cost q (θ0 i)) ∧
      (∀ i s, 0 < pay d (θ i) s) ∧
      (∀ i θ', cost q θ' ≤ cost q (θ0 i) → (∀ s, 0 < pay d θ' s) →
        ∑ s, π s * u i (pay d θ' s) ≤ ∑ s, π s * u i (pay d (θ i) s)) ∧
      ∀ j, ∑ i, θ i j = ∑ i, θ0 i j := by
  obtain ⟨ψ, c, hψ, hc, hbud, hclear, hopt⟩ := exists_ad_equilibrium π hπ
    (fun i s => pay d (θ0 i) s) hθ0 γ hγ u hu
  choose θ hθ using fun i => hspan (c i)
  set q : J → ℝ := fun j => ∑ s, ψ s * d j s with hq
  have hcost : ∀ x, cost q x = ∑ s, ψ s * pay d x s := fun x => cost_eq d ψ x
  refine ⟨ψ, q, θ, hψ, fun j => rfl, fun i => ?_, fun i s => by rw [hθ i s]; exact hc i s,
    fun i θ' hb hpos => ?_, ?_⟩
  · rw [hcost, hcost]
    simp only [hθ i]
    exact hbud i
  · have h := hopt i (fun s => pay d θ' s) hpos (by rw [← hcost, ← hcost]; exact hb)
    simp only [hθ i]
    exact h
  · have hz : (fun j => ∑ i, θ i j - ∑ i, θ0 i j) = 0 := by
      apply hnr
      intro s
      unfold pay
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm (f := fun j i => θ i j * d j s),
        Finset.sum_comm (f := fun j i => θ0 i j * d j s)]
      have h1 : ∀ i, ∑ j, θ i j * d j s = c i s := fun i => hθ i s
      simp only [h1]
      rw [hclear s]
      simp [pay]
    intro j
    have := congrFun hz j
    simp only [Pi.zero_apply] at this
    linarith

end MultiAssetHetero

end

#print axioms MultiAssetHetero.F_lt
#print axioms MultiAssetHetero.root_exists
#print axioms MultiAssetHetero.mu_continuous
#print axioms MultiAssetHetero.walras
#print axioms MultiAssetHetero.exists_weights
#print axioms MultiAssetHetero.exists_ad_equilibrium
#print axioms MultiAssetHetero.exists_equilibrium_complete
