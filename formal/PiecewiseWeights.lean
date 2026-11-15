import Mathlib

/-!
Stage 334 (extends stage 330): Debreu's consumer with price-dependent weights.

Debreu's consumer with weight `w q > 0` trades `x q = w q · (e_k − q_k q)` at unit price `q`.

* `debreu_variable_weight` — if the weight is relatively Lipschitz with a small constant,
  `|w p − w q| ≤ κ · w q · ‖p − q‖` with `4κ ≤ ε` on `P` (coordinates `≥ ε`), the consumer is rationalised on
  the whole continuum `P` by a continuous, concave, strictly monotone utility (each `x p` is a
  maximiser, not shown unique).
* `debreu_piecewise` — in particular for weights that are constant on pieces of `P` that are
  `η`-separated, `‖p − q‖ ≥ η` across pieces, with `|c_i − c_j| ≤ κ c_j η`.
* `revealed_sign_invariant`, `debreu_warp` — revealed preference between Debreu trades does not
  depend on the weights, and WARP holds for every positive weight function.
* `limit_optimal`, `no_unique_of_jump`, `debreu_jump` — the obstruction: if prices `q_n ∈ P`
  with constant weight `c'` converge to `p ∈ P` with `w p ≠ c'` (and `e_k − p_k p ≠ 0`), then
  no continuous utility rationalises `x` on `P` with a unique maximiser at `p`. So pieces with
  different weights that touch rule out unique demand, and the separation in
  `debreu_piecewise` cannot be dropped for unique demand.

Scope: the relative Lipschitz constant must be small (`κ ≤ ε/4`); Debreu's weights
`α_k(p)` are in general not of this kind, and the continuous Mantel/Debreu decomposition on
`S_ε` is not done here.

Stage 330 description follows.

Stage 330: Afriat's construction on a continuum of prices.

Let `P` be any (possibly infinite) set of prices with coordinates in `[ε, 1]`, and `x q` the
trade chosen at `q`.  If there are numbers `V q` (utility levels) and `λ q ∈ [ε, Λ]` (marginal
utilities of income) satisfying the continuum Afriat inequalities

  `V p ≤ V q + λ q · (q·x p − q·x q)`        for all `p, q ∈ P`,

then `U y = inf_{q ∈ P} (V q + λ q · (q·y − q·x q))` is finite, Lipschitz (hence continuous),
concave and strictly monotone on all of `ℝ^S`, `U (x p) = V p`, and `x p` maximizes `U` on the
budget `{y | p·y ≤ p·x p}` (`continuum_afriat`).

Check of non-vacuity: Debreu's consumer `x q = c (e_k − q_k q)` with a constant weight `c > 0`
satisfies the inequalities with `V q = −q_k`, `λ q = 1/c` on any set of unit prices
(`debreu_constant_weight`), so it is rationalised by a continuous, concave, strictly monotone
utility on a whole continuum of prices.

This reduces the continuous Mantel/Debreu problem on `S_ε` to finding `V, λ` for the Debreu
consumers with price-dependent weights; that step is not done here.
-/

noncomputable section

open Finset Filter Topology

namespace PiecewiseWeights

variable {S : Type*} [Fintype S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- The affine function attached to price `q`. -/
def g (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (q y : S → ℝ) : ℝ :=
  V q + lam q * (dot q y - dot q (x q))

/-- The continuum Afriat utility. -/
def U (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (y : S → ℝ) : ℝ :=
  ⨅ q : P, g V lam x q y

/-- The hypotheses: bounds on prices and on `λ`, and the continuum Afriat inequalities. -/
def Afriat (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ) : Prop :=
  (∀ q ∈ P, ε ≤ lam q ∧ lam q ≤ Λ) ∧ (∀ q ∈ P, ∀ s, ε ≤ q s ∧ q s ≤ 1) ∧
    (∀ p ∈ P, ∀ q ∈ P, V p ≤ g V lam x q (x p))

theorem g_sub (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (q y z : S → ℝ) :
    g V lam x q z - g V lam x q y = lam q * dot q (fun s => z s - y s) := by
  simp only [g, dot, mul_sub, Finset.sum_sub_distrib]
  ring

theorem lip_term (q d : S → ℝ) (l Λ : ℝ) (hq : ∀ s, 0 ≤ q s ∧ q s ≤ 1) (hl : 0 ≤ l)
    (hlΛ : l ≤ Λ) : |l * dot q d| ≤ Λ * ∑ s, |d s| := by
  have h1 : |dot q d| ≤ ∑ s, |d s| := by
    unfold dot
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul, abs_of_nonneg (hq s).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hq s).2
  rw [abs_mul, abs_of_nonneg hl]
  exact mul_le_mul hlΛ h1 (abs_nonneg _) (hl.trans hlΛ)

/-- Each affine piece changes by at most `Λ · ‖z − y‖₁`. -/
theorem g_lip (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (q : S → ℝ) (hq : q ∈ P) (y z : S → ℝ) :
    |g V lam x q z - g V lam x q y| ≤ Λ * ∑ s, |z s - y s| := by
  rw [g_sub]
  have hb : |lam q * dot q (fun s => z s - y s)| ≤ Λ * ∑ s, |z s - y s| :=
    lip_term q _ (lam q) Λ (fun s => ⟨hε.le.trans (h.2.1 q hq s).1, (h.2.1 q hq s).2⟩)
      (hε.le.trans (h.1 q hq).1) (h.1 q hq).2
  exact hb

/-- A uniform lower bound for the affine pieces at `y`. -/
theorem g_lower (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (p0 : S → ℝ) (hp0 : p0 ∈ P) (y : S → ℝ)
    (q : S → ℝ) (hq : q ∈ P) :
    V p0 - Λ * ∑ s, |y s - x p0 s| ≤ g V lam x q y := by
  have h1 := (abs_le.1 (g_lip P V lam x ε Λ hε h q hq (x p0) y)).1
  have h2 := h.2.2 p0 hp0 q hq
  linarith

theorem bdd (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) (y : S → ℝ) :
    BddBelow (Set.range fun q : P => g V lam x q y) := by
  obtain ⟨p0, hp0⟩ := hne
  exact ⟨V p0 - Λ * ∑ s, |y s - x p0 s|, by
    rintro _ ⟨q, rfl⟩
    exact g_lower P V lam x ε Λ hε h p0 hp0 y q q.2⟩

theorem U_le (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (y q : S → ℝ) (hq : q ∈ P) :
    U P V lam x y ≤ g V lam x q y :=
  ciInf_le (bdd P V lam x ε Λ hε h ⟨q, hq⟩ y) ⟨q, hq⟩

theorem le_U (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ)
    (hne : P.Nonempty) (y : S → ℝ) (c : ℝ) (hc : ∀ q ∈ P, c ≤ g V lam x q y) :
    c ≤ U P V lam x y := by
  have : Nonempty P := hne.to_subtype
  exact le_ciInf fun q => hc q q.2

/-- **Lipschitz.** -/
theorem U_lip (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) (y z : S → ℝ) :
    |U P V lam x z - U P V lam x y| ≤ Λ * ∑ s, |z s - y s| := by
  have hsym : ∑ s, |y s - z s| = ∑ s, |z s - y s| :=
    Finset.sum_congr rfl fun s _ => abs_sub_comm _ _
  have h1 : U P V lam x z - Λ * ∑ s, |z s - y s| ≤ U P V lam x y := by
    refine le_U P V lam x hne y _ fun q hq => ?_
    have a1 := U_le P V lam x ε Λ hε h z q hq
    have a2 := (abs_le.1 (g_lip P V lam x ε Λ hε h q hq y z)).2
    linarith
  have h2 : U P V lam x y - Λ * ∑ s, |z s - y s| ≤ U P V lam x z := by
    refine le_U P V lam x hne z _ fun q hq => ?_
    have a1 := U_le P V lam x ε Λ hε h y q hq
    have a2 := (abs_le.1 (g_lip P V lam x ε Λ hε h q hq z y)).2
    rw [hsym] at a2
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Continuous.** -/
theorem U_continuous (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) :
    Continuous (U P V lam x) := by
  obtain ⟨q0, hq0⟩ := hne
  have hΛ : 0 ≤ Λ := hε.le.trans ((h.1 q0 hq0).1.trans (h.1 q0 hq0).2)
  rw [Metric.continuous_iff]
  intro y r hr
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Λ * (Fintype.card S + 1) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hδ : 0 < r / K := div_pos hr hK0
  refine ⟨r / K, hδ, fun z hz => ?_⟩
  have hs : ∀ s, |z s - y s| ≤ r / K := fun s => by
    have := (dist_pi_lt_iff hδ).1 hz s
    rw [Real.dist_eq] at this
    exact this.le
  have hsum : ∑ s, |z s - y s| ≤ Fintype.card S * (r / K) := by
    have := Finset.sum_le_sum fun s (_ : s ∈ (univ : Finset S)) => hs s
    simpa using this
  have hl := U_lip P V lam x ε Λ hε h ⟨q0, hq0⟩ y z
  have hratio : Λ * Fintype.card S < K := by
    have e : Λ * (↑(Fintype.card S) + 1) = Λ * Fintype.card S + Λ := by ring
    rw [hK, e]
    linarith
  rw [Real.dist_eq]
  calc |U P V lam x z - U P V lam x y| ≤ Λ * ∑ s, |z s - y s| := hl
    _ ≤ Λ * (Fintype.card S * (r / K)) := mul_le_mul_of_nonneg_left hsum hΛ
    _ = r * (Λ * Fintype.card S) / K := by ring
    _ < r := by
      rw [div_lt_iff₀ hK0]
      exact mul_lt_mul_of_pos_left hratio hr

/-- **Concave.** -/
theorem U_concave (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) :
    ConcaveOn ℝ Set.univ (U P V lam x) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_U P V lam x hne _ _ fun q hq => ?_
  have h1 := mul_le_mul_of_nonneg_left (U_le P V lam x ε Λ hε h y q hq) ha
  have h2 := mul_le_mul_of_nonneg_left (U_le P V lam x ε Λ hε h z q hq) hb
  have e : g V lam x q (a • y + b • z) = a * g V lam x q y + b * g V lam x q z := by
    simp only [g, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ s, q s * (a * y s + b * z s) = a * ∑ s, q s * y s + b * ∑ s, q s * z s := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e1]
    linear_combination (-(V q) + lam q * ∑ s, q s * x q s) * hab
  rw [e]
  linarith

/-- **Strictly monotone.** -/
theorem U_strictMono (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) : U P V lam x y < U P V lam x z := by
  obtain ⟨s0, hs0⟩ := hlt
  have hd : 0 < ε * ε * (z s0 - y s0) := by have := sub_pos.2 hs0; positivity
  have key : U P V lam x y + ε * ε * (z s0 - y s0) ≤ U P V lam x z := by
    refine le_U P V lam x hne z _ fun q hq => ?_
    have a1 := U_le P V lam x ε Λ hε h y q hq
    have a2 := g_sub V lam x q y z
    have hq1 : ∀ s, ε ≤ q s := fun s => (h.2.1 q hq s).1
    have hdot : ε * (z s0 - y s0) ≤ dot q (fun s => z s - y s) := by
      unfold dot
      have t1 : q s0 * (z s0 - y s0) ≤ ∑ s, q s * (z s - y s) :=
        Finset.single_le_sum (f := fun s => q s * (z s - y s))
          (fun s _ => mul_nonneg (hε.le.trans (hq1 s)) (sub_nonneg.2 (hyz s))) (mem_univ s0)
      have t2 := mul_le_mul_of_nonneg_right (hq1 s0) (sub_nonneg.2 (hyz s0))
      linarith
    have hl := (h.1 q hq).1
    have hpos : 0 ≤ ε * (z s0 - y s0) := by have := sub_pos.2 hs0; positivity
    have t3 : ε * (ε * (z s0 - y s0)) ≤ lam q * dot q (fun s => z s - y s) :=
      mul_le_mul hl hdot hpos (hε.le.trans hl)
    nlinarith
  linarith

/-- The chosen trade gets utility `V p`. -/
theorem U_at (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (p : S → ℝ) (hp : p ∈ P) :
    U P V lam x (x p) = V p := by
  apply le_antisymm
  · have := U_le P V lam x ε Λ hε h (x p) p hp
    simp only [g, sub_self, mul_zero, add_zero] at this
    exact this
  · exact le_U P V lam x ⟨p, hp⟩ _ _ fun q hq => h.2.2 p hp q hq

/-- **Afriat on a continuum.**  The infimum of the affine pieces is a continuous, concave,
strictly monotone utility, and each chosen trade is optimal on its budget. -/
theorem continuum_afriat (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ)
    (ε Λ : ℝ) (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) :
    Continuous (U P V lam x) ∧ ConcaveOn ℝ Set.univ (U P V lam x) ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → U P V lam x y < U P V lam x z) ∧
      (∀ p ∈ P, U P V lam x (x p) = V p) ∧
      (∀ p ∈ P, ∀ y, dot p y ≤ dot p (x p) → U P V lam x y ≤ U P V lam x (x p)) := by
  refine ⟨U_continuous P V lam x ε Λ hε h hne, U_concave P V lam x ε Λ hε h hne,
    U_strictMono P V lam x ε Λ hε h hne, fun p hp => U_at P V lam x ε Λ hε h p hp,
    fun p hp y hy => ?_⟩
  rw [U_at P V lam x ε Λ hε h p hp]
  have h1 := U_le P V lam x ε Λ hε h y p hp
  have h2 : lam p * (dot p y - dot p (x p)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hε.le.trans (h.1 p hp).1) (by linarith)
  unfold g at h1
  linarith

/-! ### Non-vacuity: Debreu's consumer with a constant weight -/

theorem dot_le_one (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) :
    dot q p ≤ 1 := by
  have h : 0 ≤ ∑ s, (q s - p s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  have e : ∑ s, (q s - p s) ^ 2 = ∑ s, q s ^ 2 + ∑ s, p s ^ 2 - 2 * dot q p := by
    unfold dot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

variable [DecidableEq S]

/-- Debreu's direction `e_k − p_k p`. -/
def dirk (k : S) (p : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - p k * p s

theorem dot_dirk (k : S) (p q : S → ℝ) : dot q (dirk k p) = q k - p k * dot q p := by
  unfold dot dirk
  have e : ∀ s, q s * ((if s = k then 1 else 0) - p k * p s) =
      (if s = k then q s else 0) - p k * (q s * p s) := by
    intro s
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- **Debreu's consumer with a constant weight is rationalised on a continuum.**  On any
non-empty set `P` of unit prices with coordinates at least `ε > 0`, the trades
`x q = c (e_k − q_k q)` (`c > 0`) are optimal for a continuous, concave, strictly monotone
utility. -/
theorem debreu_constant_weight (P : Set (S → ℝ)) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hne : P.Nonempty) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => c * dirk k p s) = 0 ∧
        ∀ y, dot p y ≤ 0 → u y ≤ u (fun s => c * dirk k p s) := by
  set x : (S → ℝ) → S → ℝ := fun q s => c * dirk k q s with hx
  have hdx : ∀ p q, dot q (x p) = c * (q k - p k * dot q p) := by
    intro p q
    rw [← dot_dirk]
    simp only [hx, dot]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hdot1 : ∀ q ∈ P, dot q q = 1 := by
    intro q hq
    rw [← hP q hq]
    unfold dot
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbud : ∀ q ∈ P, dot q (x q) = 0 := by
    intro q hq
    rw [hdx, hdot1 q hq]
    ring
  have hle1 : ∀ q ∈ P, ∀ s, q s ≤ 1 := by
    intro q hq s
    have h1 : q s ^ 2 ≤ ∑ t, q t ^ 2 :=
      Finset.single_le_sum (f := fun t => q t ^ 2) (fun t _ => sq_nonneg _) (mem_univ s)
    rw [hP q hq] at h1
    nlinarith [hpos q hq s]
  set ε' : ℝ := min ε (1 / c) with hε'
  have hε'0 : 0 < ε' := lt_min hε (one_div_pos.2 hc)
  have hA : Afriat P (fun q => -q k) (fun _ => 1 / c) x ε' (1 / c) := by
    refine ⟨fun _ _ => ⟨min_le_right _ _, le_rfl⟩,
      fun q hq s => ⟨(min_le_left _ _).trans (hpos q hq s), hle1 q hq s⟩,
      fun p hp q hq => ?_⟩
    show -p k ≤ -q k + 1 / c * (dot q (x p) - dot q (x q))
    rw [hbud q hq, hdx]
    have h1 := dot_le_one p q (hP p hp) (hP q hq)
    have h2 : 0 ≤ p k := hε.le.trans (hpos p hp k)
    have e : 1 / c * (c * (q k - p k * dot q p) - 0) = q k - p k * dot q p := by
      rw [sub_zero]
      field_simp
    rw [e]
    nlinarith
  obtain ⟨hc1, hc2, hc3, -, hc5⟩ :=
    continuum_afriat P (fun q => -q k) (fun _ => 1 / c) x ε' (1 / c) hε'0 hA hne
  refine ⟨_, hc1, hc2, hc3, fun p hp => ⟨hbud p hp, fun y hy => ?_⟩⟩
  exact hc5 p hp y (by rw [hbud p hp]; exact hy)


/-! ### Price-dependent weights -/

/-- **Slowly varying weights.** -/
theorem debreu_variable_weight (P : Set (S → ℝ)) (ε κ cmin cmax : ℝ) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε)
    (hcmin : 0 < cmin) (w : (S → ℝ) → ℝ) (k : S) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hne : P.Nonempty) (hw : ∀ q ∈ P, cmin ≤ w q ∧ w q ≤ cmax)
    (hvar : ∀ p ∈ P, ∀ q ∈ P, (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * ∑ s, (p s - q s) ^ 2) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => w p * dirk k p s) = 0 ∧
        ∀ y, dot p y ≤ 0 → u y ≤ u (fun s => w p * dirk k p s) := by
  set x : (S → ℝ) → S → ℝ := fun q s => w q * dirk k q s with hx
  have hdx : ∀ p q, dot q (x p) = w p * (q k - p k * dot q p) := by
    intro p q
    rw [← dot_dirk]
    simp only [hx, dot]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hdot1 : ∀ q ∈ P, dot q q = 1 := by
    intro q hq
    rw [← hP q hq]
    unfold dot
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbud : ∀ q ∈ P, dot q (x q) = 0 := by
    intro q hq
    rw [hdx, hdot1 q hq]
    ring
  have hle1 : ∀ q ∈ P, ∀ s, q s ≤ 1 := by
    intro q hq s
    have h1 : q s ^ 2 ≤ ∑ t, q t ^ 2 :=
      Finset.single_le_sum (f := fun t => q t ^ 2) (fun t _ => sq_nonneg _) (mem_univ s)
    rw [hP q hq] at h1
    nlinarith [hpos q hq s]
  obtain ⟨q0, hq0⟩ := hne
  have hcmax : 0 < cmax := hcmin.trans_le ((hw q0 hq0).1.trans (hw q0 hq0).2)
  set ε' : ℝ := min ε (1 / cmax) with hε'
  have hε'0 : 0 < ε' := lt_min hε (one_div_pos.2 hcmax)
  have hA : Afriat P (fun q => -q k) (fun q => 1 / w q) x ε' (1 / cmin) := by
    refine ⟨fun q hq => ⟨(min_le_right _ _).trans
        (one_div_le_one_div_of_le (hcmin.trans_le (hw q hq).1) (hw q hq).2),
        one_div_le_one_div_of_le hcmin (hw q hq).1⟩,
      fun q hq s => ⟨(min_le_left _ _).trans (hpos q hq s), hle1 q hq s⟩,
      fun p hp q hq => ?_⟩
    show -p k ≤ -q k + 1 / w q * (dot q (x p) - dot q (x q))
    rw [hbud q hq, hdx]
    have hwq : 0 < w q := hcmin.trans_le (hw q hq).1
    set d : ℝ := ∑ s, (p s - q s) ^ 2 with hd
    have hd0 : 0 ≤ d := Finset.sum_nonneg fun s _ => sq_nonneg _
    have hdq : d = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
      rw [hd]
      unfold dot
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hP p hp, hP q hq] at hdq
    have hqp0 : 0 ≤ dot q p :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (hε.le.trans (hpos q hq s)) (hε.le.trans (hpos p hp s))
    have hpk0 : ε ≤ p k := hpos p hp k
    have hpk1 := hle1 p hp k
    set A : ℝ := q k - p k * dot q p with hAdef
    have hpd : p k * dot q p = p k - p k * d / 2 := by
      have : dot q p = 1 - d / 2 := by linarith
      rw [this]
      ring
    have e : 1 / w q * (w p * A - 0) = w p / w q * A := by ring
    rw [e]
    set r : ℝ := w p / w q with hr
    have hA' : A = (q k - p k) + p k * d / 2 := by rw [hAdef, hpd]; ring
    have hr2 : (r - 1) ^ 2 ≤ κ ^ 2 * d := by
      have e2 : r - 1 = (w p - w q) / w q := by
        rw [hr, div_sub_one hwq.ne']
      rw [e2, div_pow, div_le_iff₀ (by positivity)]
      calc (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * d := hvar p hp q hq
        _ = κ ^ 2 * d * w q ^ 2 := by ring
    have hkd : (q k - p k) ^ 2 ≤ d := by
      have h := Finset.single_le_sum (f := fun s => (p s - q s) ^ 2)
        (fun s _ => sq_nonneg _) (mem_univ k)
      calc (q k - p k) ^ 2 = (p k - q k) ^ 2 := by ring
        _ ≤ d := h
    have hd2 : d ≤ 2 := by linarith
    have hsq : ((r - 1) * (q k - p k)) ^ 2 ≤ (κ * d) ^ 2 := by
      calc ((r - 1) * (q k - p k)) ^ 2 = (r - 1) ^ 2 * (q k - p k) ^ 2 := by ring
        _ ≤ (κ ^ 2 * d) * d := mul_le_mul hr2 hkd (sq_nonneg _) (by positivity)
        _ = (κ * d) ^ 2 := by ring
    have h1 := abs_le_of_sq_le_sq' hsq (mul_nonneg hκ hd0)
    have hX : |r - 1| ≤ 2 * κ := by
      refine abs_le_of_sq_le_sq ?_ (by linarith)
      have : κ ^ 2 * d ≤ κ ^ 2 * 4 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg κ)
      nlinarith
    have hpd0 : 0 ≤ p k * d / 2 := by
      have := mul_nonneg (hε.le.trans hpk0) hd0
      linarith
    have h3 : -(|r - 1| * d / 2) ≤ (r - 1) * (p k * d / 2) := by
      have h := neg_abs_le ((r - 1) * (p k * d / 2))
      rw [abs_mul, abs_of_nonneg hpd0] at h
      have : |r - 1| * (p k * d / 2) ≤ |r - 1| * d / 2 := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpk1 hd0)
          (abs_nonneg (r - 1))
        linarith
      linarith
    have h4 : |r - 1| * d / 2 ≤ κ * d := by
      have := mul_le_mul_of_nonneg_right hX hd0
      linarith
    have h5 : 4 * κ * d ≤ ε * d := mul_le_mul_of_nonneg_right hκε hd0
    have hra : r * A = A + (r - 1) * (q k - p k) + (r - 1) * (p k * d / 2) := by
      rw [hA']
      ring
    have hpe : ε * d ≤ p k * d := mul_le_mul_of_nonneg_right hpk0 hd0
    rw [hra, hA']
    linarith [h1.1]
  obtain ⟨hc1, hc2, hc3, -, hc5⟩ :=
    continuum_afriat P (fun q => -q k) (fun q => 1 / w q) x ε' (1 / cmin) hε'0 hA ⟨q0, hq0⟩
  refine ⟨_, hc1, hc2, hc3, fun p hp => ⟨hbud p hp, fun y hy => ?_⟩⟩
  exact hc5 p hp y (by rw [hbud p hp]; exact hy)

/-- **Piecewise-constant weights on separated pieces.** -/
theorem debreu_piecewise {ι : Type*} (P : Set (S → ℝ)) (ε κ η cmin cmax : ℝ) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε) (hη : 0 ≤ η) (hcmin : 0 < cmin) (piece : (S → ℝ) → ι) (cw : ι → ℝ) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hne : P.Nonempty)
    (hcw : ∀ i, cmin ≤ cw i ∧ cw i ≤ cmax)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, piece p ≠ piece q → η ^ 2 ≤ ∑ s, (p s - q s) ^ 2)
    (hclose : ∀ i j, |cw i - cw j| ≤ κ * cw j * η) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => cw (piece p) * dirk k p s) = 0 ∧
        ∀ y, dot p y ≤ 0 → u y ≤ u (fun s => cw (piece p) * dirk k p s) := by
  refine debreu_variable_weight P ε κ cmin cmax hε hκ hκε hcmin (fun q => cw (piece q)) k hP
    hpos hne (fun q _ => hcw (piece q)) fun p hp q hq => ?_
  show (cw (piece p) - cw (piece q)) ^ 2 ≤ (κ * cw (piece q)) ^ 2 * ∑ s, (p s - q s) ^ 2
  have hd0 : 0 ≤ ∑ s, (p s - q s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  by_cases h : piece p = piece q
  · rw [h, sub_self]
    have := mul_nonneg (sq_nonneg (κ * cw (piece q))) hd0
    simpa using this
  · have hb : 0 ≤ κ * cw (piece q) * η :=
      mul_nonneg (mul_nonneg hκ (hcmin.le.trans (hcw (piece q)).1)) hη
    have h1 : (cw (piece p) - cw (piece q)) ^ 2 ≤ (κ * cw (piece q) * η) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hclose _ _) 2
    calc (cw (piece p) - cw (piece q)) ^ 2 ≤ (κ * cw (piece q) * η) ^ 2 := h1
      _ = (κ * cw (piece q)) ^ 2 * η ^ 2 := by ring
      _ ≤ (κ * cw (piece q)) ^ 2 * ∑ s, (p s - q s) ^ 2 :=
        mul_le_mul_of_nonneg_left (hsep p hp q hq h) (sq_nonneg _)


/-! ### Revealed preference does not see the weights -/

/-- The sign of `q · x p` does not depend on the (positive) weight. -/
theorem revealed_sign_invariant (w : ℝ) (hw : 0 < w) (k : S) (p q : S → ℝ) :
    (dot q (fun s => w * dirk k p s) ≤ 0 ↔ dot q (dirk k p) ≤ 0) ∧
      (dot q (fun s => w * dirk k p s) < 0 ↔ dot q (dirk k p) < 0) := by
  have e : dot q (fun s => w * dirk k p s) = w * dot q (dirk k p) := by
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc
    push Not at hc
    linarith [mul_pos hw hc]
  · nlinarith
  · by_contra hc
    push Not at hc
    linarith [mul_nonneg hw.le hc]
  · nlinarith

/-- **WARP for Debreu's consumer, whatever the weights.**  If each of `x p`, `x q` is
affordable at the other's price, then `p = q`. -/
theorem debreu_warp (k : S) (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1)
    (hpp : ∀ s, 0 < p s) (hqq : ∀ s, 0 < q s)
    (h1 : dot q (dirk k p) ≤ 0) (h2 : dot p (dirk k q) ≤ 0) : p = q := by
  rw [dot_dirk] at h1 h2
  have hsym : dot p q = dot q p := by
    unfold dot
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  rw [hsym] at h2
  have hc1 := dot_le_one p q hp hq
  have hc0 : 0 ≤ dot q p := Finset.sum_nonneg fun s _ => mul_nonneg (hqq s).le (hpp s).le
  have hpk := hpp k
  have hqk := hqq k
  have hk1 : p k ≤ q k := by nlinarith
  have hk2 : q k ≤ p k := by nlinarith
  have hc : dot q p = 1 := by nlinarith
  have hd : ∑ s, (p s - q s) ^ 2 = 0 := by
    have e : ∑ s, (p s - q s) ^ 2 = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
      unfold dot
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, hp, hq, hc]
    norm_num
  funext s
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => sq_nonneg (p s - q s))).1 hd s
    (mem_univ s)
  have : p s - q s = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h
  linarith

/-! ### The obstruction to unique demand where weights jump -/

omit [DecidableEq S] in
theorem dot_continuous : Continuous (fun pr : (S → ℝ) × (S → ℝ) => dot pr.1 pr.2) := by
  unfold dot
  exact continuous_finsetSum _ fun s _ =>
    ((continuous_apply s).comp continuous_fst).mul ((continuous_apply s).comp continuous_snd)

omit [DecidableEq S] in
/-- **Limits of optimal trades are optimal.** -/
theorem limit_optimal [Nonempty S] (u : (S → ℝ) → ℝ) (hu : Continuous u) (P : Set (S → ℝ))
    (x : (S → ℝ) → S → ℝ) (hb : ∀ q ∈ P, dot q (x q) = 0)
    (hopt : ∀ q ∈ P, ∀ y, dot q y ≤ 0 → u y ≤ u (x q))
    (q : ℕ → S → ℝ) (hq : ∀ n, q n ∈ P) (p z : S → ℝ) (hp : ∀ s, 0 < p s)
    (hqp : Tendsto q atTop (𝓝 p)) (hxz : Tendsto (fun n => x (q n)) atTop (𝓝 z)) :
    dot p z = 0 ∧ ∀ y, dot p y ≤ 0 → u y ≤ u z := by
  have hdz : Tendsto (fun n => dot (q n) (x (q n))) atTop (𝓝 (dot p z)) :=
    (dot_continuous.tendsto (p, z)).comp (hqp.prodMk_nhds hxz)
  have e : (fun n => dot (q n) (x (q n))) = fun _ => (0 : ℝ) := funext fun n => hb _ (hq n)
  rw [e] at hdz
  have h0 : dot p z = 0 := tendsto_nhds_unique hdz tendsto_const_nhds
  have hux : Tendsto (fun n => u (x (q n))) atTop (𝓝 (u z)) := (hu.tendsto z).comp hxz
  have hstrict : ∀ y, dot p y < 0 → u y ≤ u z := by
    intro y hy
    have hdy : Tendsto (fun n => dot (q n) y) atTop (𝓝 (dot p y)) :=
      (dot_continuous.tendsto (p, y)).comp (hqp.prodMk_nhds tendsto_const_nhds)
    have hev : ∀ᶠ n in atTop, dot (q n) y < 0 := hdy.eventually (eventually_lt_nhds hy)
    exact ge_of_tendsto hux (hev.mono fun n hn => hopt _ (hq n) y hn.le)
  refine ⟨h0, fun y hy => ?_⟩
  have hsp : 0 < ∑ s, p s := Finset.sum_pos (fun s _ => hp s) Finset.univ_nonempty
  have hshift : ∀ t : ℝ, dot p (fun s => y s - t) = dot p y - t * ∑ s, p s := by
    intro t
    unfold dot
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hcont : Tendsto (fun t : ℝ => u (fun s => y s - t)) (𝓝[>] 0) (𝓝 (u y)) := by
    have hc : Continuous fun t : ℝ => u (fun s => y s - t) :=
      hu.comp (continuous_pi fun s => continuous_const.sub continuous_id)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), u (fun s => y s - t) ≤ u z :=
    eventually_nhdsWithin_of_forall fun t ht => hstrict _ (by
      rw [hshift]
      have : 0 < t * ∑ s, p s := mul_pos ht hsp
      linarith)
  exact le_of_tendsto hcont hev

omit [DecidableEq S] in
/-- **No unique demand at a jump.** -/
theorem no_unique_of_jump [Nonempty S] (u : (S → ℝ) → ℝ) (hu : Continuous u)
    (P : Set (S → ℝ)) (x : (S → ℝ) → S → ℝ) (hb : ∀ q ∈ P, dot q (x q) = 0)
    (q : ℕ → S → ℝ) (hq : ∀ n, q n ∈ P) (p z : S → ℝ) (hpP : p ∈ P) (hp : ∀ s, 0 < p s)
    (hqp : Tendsto q atTop (𝓝 p)) (hxz : Tendsto (fun n => x (q n)) atTop (𝓝 z))
    (hz : z ≠ x p) :
    ¬ ((∀ q ∈ P, ∀ y, dot q y ≤ 0 → u y ≤ u (x q)) ∧
      ∀ y, dot p y ≤ 0 → y ≠ x p → u y < u (x p)) := by
  rintro ⟨hopt, huniq⟩
  obtain ⟨h0, hle⟩ := limit_optimal u hu P x hb hopt q hq p z hp hqp hxz
  have h1 := huniq z (by rw [h0]) hz
  have h2 := hle (x p) (by rw [hb p hpP])
  linarith

/-- **Debreu's consumer: touching pieces with different weights rule out unique demand.** -/
theorem debreu_jump [Nonempty S] (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (q : ℕ → S → ℝ) (hq : ∀ n, q n ∈ P) (p : S → ℝ)
    (hpP : p ∈ P) (hp : ∀ s, 0 < p s) (c' : ℝ) (hqp : Tendsto q atTop (𝓝 p))
    (hwq : ∀ n, w (q n) = c') (hc' : c' ≠ w p) (hd : dirk k p ≠ 0) :
    ¬ ∃ u : (S → ℝ) → ℝ, Continuous u ∧
      (∀ q ∈ P, ∀ y, dot q y ≤ 0 → u y ≤ u (fun s => w q * dirk k q s)) ∧
      ∀ y, dot p y ≤ 0 → y ≠ (fun s => w p * dirk k p s) →
        u y < u (fun s => w p * dirk k p s) := by
  rintro ⟨u, hu, hopt, huniq⟩
  have hb : ∀ q ∈ P, dot q (fun s => w q * dirk k q s) = 0 := by
    intro q' hq'
    have e : dot q' (fun s => w q' * dirk k q' s) = w q' * dot q' (dirk k q') := by
      unfold dot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h1 : dot q' q' = 1 := by
      rw [← hP q' hq']
      unfold dot
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, dot_dirk, h1]
    ring
  have hdc : Continuous fun r : S → ℝ => fun s => c' * dirk k r s := by
    refine continuous_pi fun s => continuous_const.mul ?_
    unfold dirk
    exact continuous_const.sub ((continuous_apply k).mul (continuous_apply s))
  have hxz : Tendsto (fun n => (fun s => w (q n) * dirk k (q n) s)) atTop
      (𝓝 (fun s => c' * dirk k p s)) := by
    have e : (fun n => (fun s => w (q n) * dirk k (q n) s)) =
        fun n => (fun s => c' * dirk k (q n) s) := by
      funext n s
      rw [hwq n]
    rw [e]
    exact (hdc.tendsto p).comp hqp
  have hz : (fun s => c' * dirk k p s) ≠ (fun s => w p * dirk k p s) := by
    intro h
    obtain ⟨s0, hs0⟩ : ∃ s, dirk k p s ≠ 0 := by
      by_contra hcon
      exact hd (funext fun s => not_not.1 fun hne => hcon ⟨s, hne⟩)
    exact hc' (mul_right_cancel₀ hs0 (congrFun h s0))
  exact no_unique_of_jump u hu P (fun q s => w q * dirk k q s) hb q hq p _ hpP hp hqp hxz hz
    ⟨hopt, huniq⟩

end PiecewiseWeights

end

#print axioms PiecewiseWeights.g_sub
#print axioms PiecewiseWeights.lip_term
#print axioms PiecewiseWeights.g_lip
#print axioms PiecewiseWeights.g_lower
#print axioms PiecewiseWeights.bdd
#print axioms PiecewiseWeights.U_le
#print axioms PiecewiseWeights.le_U
#print axioms PiecewiseWeights.U_lip
#print axioms PiecewiseWeights.U_continuous
#print axioms PiecewiseWeights.U_concave
#print axioms PiecewiseWeights.U_strictMono
#print axioms PiecewiseWeights.U_at
#print axioms PiecewiseWeights.continuum_afriat
#print axioms PiecewiseWeights.dot_le_one
#print axioms PiecewiseWeights.dot_dirk
#print axioms PiecewiseWeights.debreu_constant_weight
#print axioms PiecewiseWeights.debreu_variable_weight
#print axioms PiecewiseWeights.debreu_piecewise
#print axioms PiecewiseWeights.dot_continuous
#print axioms PiecewiseWeights.limit_optimal
#print axioms PiecewiseWeights.no_unique_of_jump
#print axioms PiecewiseWeights.debreu_jump
#print axioms PiecewiseWeights.revealed_sign_invariant
#print axioms PiecewiseWeights.debreu_warp
