import Mathlib

/-!
Stage 335 (extends stage 334): unique demand for Debreu's consumer with slowly varying weights.

Debreu's consumer with weight `w q > 0` trades `dx w k q = w q · (e_k − q_k q)` at unit price `q`.
Stage 334 rationalised these trades on a continuum `P` when the weight is relatively Lipschitz
with a small constant (`|w p − w q| ≤ κ · w q · ‖p − q‖`, `4κ ≤ ε`), but did not show uniqueness.

* `key_upper` — the affine Afriat piece at `q` lies at most `‖p − q‖²` above `−p_k` at the trade
  `dx w k p`.
* `debreu_variable_unique` — if, in addition, `P` is *rich* around each of its points (it
  contains the short great-circle arcs `arc p z t` leaving `p` in every direction `z` tangent to
  the budget plane), then the same continuous, concave, strictly monotone utility has `dx w k p`
  as its **unique** maximiser on the budget `{y | p·y ≤ 0}` for every `p ∈ P`.
* `rich_open` — non-vacuity of the richness condition: the open set of unit prices with all
  coordinates `> ε` is rich.

Scope: the uniqueness needs both the small relative Lipschitz constant (`4κ ≤ ε`) of stage 334
and the richness of `P`, i.e. uniqueness is shown at relatively interior prices. Boundary prices of
a closed `P` are not covered. Debreu's weights `α_k(p)` are in general not of this small-constant
kind, and the continuous Mantel/Debreu decomposition on `S_ε` is not done here.

Stage 330/334 description follows.

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
(stage 330, `debreu_constant_weight`), so it is rationalised by a continuous, concave, strictly monotone
utility on a whole continuum of prices.

This reduces the continuous Mantel/Debreu problem on `S_ε` to finding `V, λ` for the Debreu
consumers with price-dependent weights; that step is not done here.
-/


noncomputable section

open Finset Filter Topology

namespace BoundaryUnique

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


/-! ### Stage 335: unique demand for slowly varying weights -/

/-- Debreu's trade with weight `w`: `dx w k q = w q · (e_k − q_k q)`. -/
def dx (w : (S → ℝ) → ℝ) (k : S) (q : S → ℝ) (s : S) : ℝ := w q * dirk k q s

theorem dot_dx (w : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) :
    dot q (dx w k p) = w p * (q k - p k * dot q p) := by
  rw [← dot_dirk]
  simp only [dx, dot]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
theorem dist_eq (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) :
    ∑ s, (p s - q s) ^ 2 = 2 - 2 * dot q p := by
  have e : ∑ s, (p s - q s) ^ 2 = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
    unfold dot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, hp, hq]
  ring

omit [DecidableEq S] in
theorem le_one_of_unit (q : S → ℝ) (hq : ∑ s, q s ^ 2 = 1) (s : S) (h0 : 0 ≤ q s) :
    q s ≤ 1 := by
  have h1 : q s ^ 2 ≤ ∑ t, q t ^ 2 :=
    Finset.single_le_sum (f := fun t => q t ^ 2) (fun t _ => sq_nonneg _) (mem_univ s)
  rw [hq] at h1
  nlinarith

/-- **The Afriat inequalities for slowly varying weights** (the core of stage 334). -/
theorem variable_afriat (P : Set (S → ℝ)) (ε κ cmin cmax : ℝ) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε)
    (hcmin : 0 < cmin) (w : (S → ℝ) → ℝ) (k : S) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hw : ∀ q ∈ P, cmin ≤ w q ∧ w q ≤ cmax)
    (hvar : ∀ p ∈ P, ∀ q ∈ P, (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * ∑ s, (p s - q s) ^ 2) :
    Afriat P (fun q => -q k) (fun q => 1 / w q) (dx w k) (min ε (1 / cmax)) (1 / cmin) := by
  have hdot1 : ∀ q ∈ P, dot q q = 1 := by
    intro q hq
    rw [← hP q hq]
    unfold dot
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbud : ∀ q ∈ P, dot q (dx w k q) = 0 := by
    intro q hq
    rw [dot_dx, hdot1 q hq]
    ring
  have hle1 : ∀ q ∈ P, ∀ s, q s ≤ 1 := fun q hq s =>
    le_one_of_unit q (hP q hq) s (hε.le.trans (hpos q hq s))
  refine ⟨fun q hq => ⟨(min_le_right _ _).trans
      (one_div_le_one_div_of_le (hcmin.trans_le (hw q hq).1) (hw q hq).2),
      one_div_le_one_div_of_le hcmin (hw q hq).1⟩,
    fun q hq s => ⟨(min_le_left _ _).trans (hpos q hq s), hle1 q hq s⟩,
    fun p hp q hq => ?_⟩
  show -p k ≤ -q k + 1 / w q * (dot q (dx w k p) - dot q (dx w k q))
  rw [hbud q hq, dot_dx]
  have hwq : 0 < w q := hcmin.trans_le (hw q hq).1
  set d : ℝ := ∑ s, (p s - q s) ^ 2 with hd
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hdq : d = 2 - 2 * dot q p := dist_eq p q (hP p hp) (hP q hq)
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

omit [DecidableEq S] in
/-- **Upper bound on an Afriat piece.**  At the trade with weight ratio `wp / wq`, the piece of
`q` lies at most `‖p − q‖²` above `−p_k`. -/
theorem key_upper (ε κ : ℝ) (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε) (k : S) (p q : S → ℝ)
    (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) (hpk : ε ≤ p k) (hpk1 : p k ≤ 1)
    (hqp0 : 0 ≤ dot q p) (wp wq : ℝ) (hwq : 0 < wq)
    (hvar : (wp - wq) ^ 2 ≤ (κ * wq) ^ 2 * ∑ s, (p s - q s) ^ 2) :
    -q k + wp / wq * (q k - p k * dot q p) ≤ -p k + ∑ s, (p s - q s) ^ 2 := by
  have hdq := dist_eq p q hp hq
  set d : ℝ := ∑ s, (p s - q s) ^ 2 with hd
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun s _ => sq_nonneg _
  have hd2 : d ≤ 2 := by linarith
  set A : ℝ := q k - p k * dot q p with hAdef
  have hpd : p k * dot q p = p k - p k * d / 2 := by
    have : dot q p = 1 - d / 2 := by linarith
    rw [this]
    ring
  have hA' : A = (q k - p k) + p k * d / 2 := by rw [hAdef, hpd]; ring
  set r : ℝ := wp / wq with hr
  have hr2 : (r - 1) ^ 2 ≤ κ ^ 2 * d := by
    have e2 : r - 1 = (wp - wq) / wq := by
      rw [hr, div_sub_one hwq.ne']
    rw [e2, div_pow, div_le_iff₀ (by positivity)]
    calc (wp - wq) ^ 2 ≤ (κ * wq) ^ 2 * d := hvar
      _ = κ ^ 2 * d * wq ^ 2 := by ring
  have hkd : (q k - p k) ^ 2 ≤ d := by
    have h := Finset.single_le_sum (f := fun s => (p s - q s) ^ 2)
      (fun s _ => sq_nonneg _) (mem_univ k)
    calc (q k - p k) ^ 2 = (p k - q k) ^ 2 := by ring
      _ ≤ d := h
  have hε0 : 0 ≤ ε := by linarith
  have hpk0 : 0 ≤ p k := hε0.trans hpk
  have hpk2 : p k ^ 2 ≤ 1 := by nlinarith
  have hdd : d ^ 2 ≤ 2 * d := by nlinarith
  have hB : (p k * d / 2) ^ 2 ≤ d / 2 := by
    have e3 : (p k * d / 2) ^ 2 = p k ^ 2 * d ^ 2 / 4 := by ring
    have := mul_le_mul_of_nonneg_right hpk2 (sq_nonneg d)
    rw [e3]
    linarith
  have hA2 : A ^ 2 ≤ 3 * d := by
    rw [hA']
    nlinarith [sq_nonneg ((q k - p k) - p k * d / 2)]
  have hprod : ((r - 1) * A) ^ 2 ≤ (2 * κ * d) ^ 2 := by
    calc ((r - 1) * A) ^ 2 = (r - 1) ^ 2 * A ^ 2 := by ring
      _ ≤ (κ ^ 2 * d) * (3 * d) := mul_le_mul hr2 hA2 (sq_nonneg _) (by positivity)
      _ ≤ (2 * κ * d) ^ 2 := by nlinarith [sq_nonneg (κ * d)]
  have h1 := abs_le_of_sq_le_sq' hprod (by positivity)
  have hε1 : ε ≤ 1 := hpk.trans hpk1
  have h4 : 4 * κ * d ≤ 1 * d := mul_le_mul_of_nonneg_right (by linarith) hd0
  have hpkd : p k * d ≤ 1 * d := mul_le_mul_of_nonneg_right hpk1 hd0
  have hra : r * A = A + (r - 1) * A := by ring
  rw [hra]
  linarith [h1.2]

/-- Squared Euclidean norm. -/
def nsq (z : S → ℝ) : ℝ := ∑ s, z s ^ 2

omit [DecidableEq S] in
theorem nsq_nonneg (z : S → ℝ) : 0 ≤ nsq z := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The great-circle arc leaving the unit price `p` in the tangent direction `−z`. -/
def arc (p z : S → ℝ) (t : ℝ) (s : S) : ℝ :=
  ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z)

omit [DecidableEq S] in
theorem arc_den (z : S → ℝ) (t : ℝ) : 0 < 1 + t ^ 2 * nsq z := by
  have := mul_nonneg (sq_nonneg t) (nsq_nonneg z)
  linarith

omit [DecidableEq S] in
theorem arc_dot_p (p z : S → ℝ) (t : ℝ) (hp : ∑ s, p s ^ 2 = 1) (hz : dot p z = 0) :
    dot (arc p z t) p = (1 - t ^ 2 * nsq z) / (1 + t ^ 2 * nsq z) := by
  have hz' : ∑ s, p s * z s = 0 := hz
  have e : ∀ s, ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z) * p s =
      ((1 - t ^ 2 * nsq z) * p s ^ 2 - 2 * t * (p s * z s)) / (1 + t ^ 2 * nsq z) :=
    fun s => by ring
  unfold dot arc
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hz']
  ring

omit [DecidableEq S] in
theorem arc_dot_z (p z : S → ℝ) (t : ℝ) (hz : dot p z = 0) :
    dot (arc p z t) z = -(2 * t * nsq z) / (1 + t ^ 2 * nsq z) := by
  have hz' : ∑ s, p s * z s = 0 := hz
  have e : ∀ s, ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z) * z s =
      ((1 - t ^ 2 * nsq z) * (p s * z s) - 2 * t * z s ^ 2) / (1 + t ^ 2 * nsq z) :=
    fun s => by ring
  unfold dot arc
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hz',
    show ∑ s, z s ^ 2 = nsq z from rfl]
  ring

omit [DecidableEq S] in
theorem arc_unit (p z : S → ℝ) (t : ℝ) (hp : ∑ s, p s ^ 2 = 1) (hz : dot p z = 0) :
    ∑ s, arc p z t s ^ 2 = 1 := by
  have hz' : ∑ s, p s * z s = 0 := hz
  have e : ∀ s, (((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z)) ^ 2 =
      ((1 - t ^ 2 * nsq z) ^ 2 * p s ^ 2 - 4 * t * (1 - t ^ 2 * nsq z) * (p s * z s) +
        4 * t ^ 2 * z s ^ 2) / (1 + t ^ 2 * nsq z) ^ 2 :=
    fun s => by rw [div_pow]; congr 1; ring
  unfold arc
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hp, hz', show ∑ s, z s ^ 2 = nsq z from rfl,
    div_eq_one_iff_eq (pow_pos (arc_den z t) 2).ne']
  ring

omit [DecidableEq S] in
/-- **Non-vacuity of richness.**  The open set of unit prices with all coordinates `> ε`
contains the short arcs leaving each of its points in every tangent direction. -/
theorem rich_open (ε : ℝ) (p : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hpe : ∀ s, ε < p s)
    (z : S → ℝ) (hz : dot p z = 0) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      arc p z t ∈ {q : S → ℝ | ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε < q s} := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, ε < arc p z t s := by
    rw [eventually_all]
    intro s
    have hc : Continuous fun t : ℝ => arc p z t s := by
      show Continuous fun t : ℝ =>
        ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z)
      exact Continuous.div (by fun_prop) (by fun_prop) fun t => (arc_den z t).ne'
    have h0 : arc p z 0 s = p s := by simp [arc]
    have ht := hc.tendsto 0
    rw [h0] at ht
    exact ht.eventually (eventually_gt_nhds (hpe s))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun t ht htd => ⟨arc_unit p z t hp hz, hball ?_⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht]
  exact htd

/-- **Unique demand for slowly varying weights.**  Under the hypotheses of stage 334, and if `P`
is rich (it contains the short arcs `arc p z t` leaving each `p ∈ P` in every direction `z`
with `p·z = 0`), Debreu's trade `dx w k p` is the *unique* maximiser of one continuous, concave,
strictly monotone utility on the budget `{y | p·y ≤ 0}`, for every `p ∈ P`. -/
theorem debreu_variable_unique (P : Set (S → ℝ)) (ε κ cmin cmax : ℝ) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε)
    (hcmin : 0 < cmin) (w : (S → ℝ) → ℝ) (k : S) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hne : P.Nonempty) (hw : ∀ q ∈ P, cmin ≤ w q ∧ w q ≤ cmax)
    (hvar : ∀ p ∈ P, ∀ q ∈ P, (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * ∑ s, (p s - q s) ^ 2)
    (hrich : ∀ p ∈ P, ∀ z : S → ℝ, dot p z = 0 →
      ∃ t0 > 0, ∀ t, 0 < t → t < t0 → arc p z t ∈ P) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (dx w k p) = 0 ∧ (∀ y, dot p y ≤ 0 → u y ≤ u (dx w k p)) ∧
        ∀ y, dot p y ≤ 0 → y ≠ dx w k p → u y < u (dx w k p) := by
  have hdot1 : ∀ q ∈ P, dot q q = 1 := by
    intro q hq
    rw [← hP q hq]
    unfold dot
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbud : ∀ q ∈ P, dot q (dx w k q) = 0 := by
    intro q hq
    rw [dot_dx, hdot1 q hq]
    ring
  obtain ⟨q0, hq0⟩ := hne
  have hcmax : 0 < cmax := hcmin.trans_le ((hw q0 hq0).1.trans (hw q0 hq0).2)
  have hε'0 : 0 < min ε (1 / cmax) := lt_min hε (one_div_pos.2 hcmax)
  have hA := variable_afriat P ε κ cmin cmax hε hκ hκε hcmin w k hP hpos hw hvar
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    continuum_afriat P (fun q => -q k) (fun q => 1 / w q) (dx w k) _ (1 / cmin) hε'0 hA
      ⟨q0, hq0⟩
  refine ⟨U P (fun q => -q k) (fun q => 1 / w q) (dx w k), hc1, hc2, hc3, fun p hp =>
    ⟨hbud p hp, fun y hy => hc5 p hp y (by rw [hbud p hp]; exact hy), fun y hy hyne => ?_⟩⟩
  have hup : U P (fun q => -q k) (fun q => 1 / w q) (dx w k) (dx w k p) = -p k := hc4 p hp
  rcases hy.lt_or_eq with hlt | heq
  · -- below the budget line: shift up onto it, then use strict monotonicity
    have hsum : 0 < ∑ s, p s :=
      lt_of_lt_of_le (hε.trans_le (hpos p hp k))
        (Finset.single_le_sum (f := fun s => p s) (fun s _ => hε.le.trans (hpos p hp s))
          (mem_univ k))
    set c : ℝ := -dot p y / ∑ s, p s with hcdef
    have hc : 0 < c := div_pos (by linarith) hsum
    set y' : S → ℝ := fun s => y s + c with hy'def
    have hy' : dot p y' = 0 := by
      have e1 : dot p y' = dot p y + (∑ s, p s) * c := by
        simp only [dot, hy'def, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      have e2 : (∑ s, p s) * c = -dot p y := by
        rw [hcdef, mul_div_assoc']
        exact mul_div_cancel_left₀ _ hsum.ne'
      rw [e1, e2]
      ring
    have h1 := hc3 y y' (fun s => by simp only [hy'def]; linarith) ⟨k, by simp only [hy'def]; linarith⟩
    have h2 := hc5 p hp y' (by rw [hy', hbud p hp])
    exact h1.trans_le h2
  · -- on the budget line: a nearby price separates `y` strictly
    set z : S → ℝ := fun s => y s - dx w k p s with hzdef
    have hz : dot p z = 0 := by
      have e1 : dot p z = dot p y - dot p (dx w k p) := by
        simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
      rw [e1, heq, hbud p hp]
      ring
    have hN : 0 < nsq z := by
      obtain ⟨s, hs⟩ : ∃ s, y s ≠ dx w k p s := by
        by_contra h
        push Not at h
        exact hyne (funext h)
      have hzs : z s ≠ 0 := by simp only [hzdef]; exact sub_ne_zero.2 hs
      have h1 : 0 < z s ^ 2 := by positivity
      exact lt_of_lt_of_le h1
        (Finset.single_le_sum (f := fun s => z s ^ 2) (fun _ _ => sq_nonneg _) (mem_univ s))
    obtain ⟨t0, ht0, hrt⟩ := hrich p hp z hz
    set t : ℝ := min (t0 / 2) (1 / (4 * cmax)) with htdef
    have ht : 0 < t := lt_min (by linarith) (by positivity)
    have htt0 : t < t0 := (min_le_left _ _).trans_lt (by linarith)
    have htc : t ≤ 1 / (4 * cmax) := min_le_right _ _
    have hq := hrt t ht htt0
    set q : S → ℝ := arc p z t with hqdef
    have hpu := hP p hp
    have hqu := hP q hq
    have hqp := arc_dot_p p z t hpu hz
    have hqz := arc_dot_z p z t hz
    rw [← hqdef] at hqp hqz
    have hd := dist_eq p q hpu hqu
    have hqp0 : 0 ≤ dot q p :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (hε.le.trans (hpos q hq s)) (hε.le.trans (hpos p hp s))
    have hwq := hw q hq
    have hwq0 : 0 < w q := hcmin.trans_le hwq.1
    have hpk1 : p k ≤ 1 := le_one_of_unit p hpu k (hε.le.trans (hpos p hp k))
    have hkey := key_upper ε κ hκ hκε k p q hpu hqu (hpos p hp k) hpk1 hqp0 (w p) (w q) hwq0
      (hvar p hp q hq)
    have hU := U_le P (fun q => -q k) (fun q => 1 / w q) (dx w k) _ (1 / cmin) hε'0 hA y q hq
    simp only [g] at hU
    rw [hbud q hq] at hU
    have hyz : dot q y = dot q (dx w k p) + dot q z := by
      simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hyz, dot_dx] at hU
    have e : 1 / w q * (w p * (q k - p k * dot q p) + dot q z - 0) =
        w p / w q * (q k - p k * dot q p) + dot q z / w q := by ring
    rw [e] at hU
    have h1a := arc_den z t
    have h1a' : 1 + t ^ 2 * nsq z ≠ 0 := h1a.ne'
    have hwq' : w q ≠ 0 := hwq0.ne'
    have htw : 2 * t * w q < 1 := by
      have h1 : t * (4 * cmax) ≤ 1 := (le_div_iff₀ (by positivity)).1 htc
      have h2 : t * w q ≤ t * cmax := mul_le_mul_of_nonneg_left hwq.2 ht.le
      linarith
    have hneg : ∑ s, (p s - q s) ^ 2 + dot q z / w q < 0 := by
      rw [hd, hqp, hqz]
      have e2 : 2 - 2 * ((1 - t ^ 2 * nsq z) / (1 + t ^ 2 * nsq z)) +
          -(2 * t * nsq z) / (1 + t ^ 2 * nsq z) / w q =
          2 * t * nsq z * (2 * t * w q - 1) / ((1 + t ^ 2 * nsq z) * w q) := by
        field_simp
        ring
      rw [e2]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos (mul_pos two_pos ht) hN) (by linarith))
        (mul_pos h1a hwq0)
    rw [hup]
    linarith


/-! ### Stage 341: uniqueness at boundary prices via one-sided arcs

The proof of `debreu_variable_unique` uses only one arc: the one in the direction
`y − dx p`.  Any tangent direction `z'` with `z'·(y − dx p) > 0` whose short arc stays in `P`
does the same job.  On the closed cap `{q unit, q ≥ ε}` such arcs exist at every price of the
relative interior, and at a boundary price `p` for every `z'` that points strictly inward on the
active coordinates (`z' s < 0` where `p s = ε`).  The directions left uncovered at a boundary
price are those `y − dx p` with `z'·(y − dx p) ≤ 0` for every inward `z'`, a closed cone spanned
by the tangent projections of the active `e_s`.  Uniqueness in those directions is not settled
here. -/

omit [DecidableEq S] in
theorem arc_dot_gen (p z' z : S → ℝ) (t : ℝ) :
    dot (arc p z' t) z =
      ((1 - t ^ 2 * nsq z') * dot p z - 2 * t * dot z' z) / (1 + t ^ 2 * nsq z') := by
  have e : ∀ s, ((1 - t ^ 2 * nsq z') * p s - 2 * t * z' s) / (1 + t ^ 2 * nsq z') * z s =
      ((1 - t ^ 2 * nsq z') * (p s * z s) - 2 * t * (z' s * z s)) / (1 + t ^ 2 * nsq z') :=
    fun s => by ring
  unfold dot arc
  simp only [e]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Directional uniqueness.**  No richness assumption on `P`.  A trade `y ≠ dx p` on the
budget is strictly worse as soon as it is strictly inside the budget, or some tangent direction
`z'` with `z'·(y − dx p) > 0` has its short arc inside `P`. -/
theorem debreu_directional_unique (P : Set (S → ℝ)) (ε κ cmin cmax : ℝ) (hε : 0 < ε)
    (hκ : 0 ≤ κ) (hκε : 4 * κ ≤ ε)
    (hcmin : 0 < cmin) (w : (S → ℝ) → ℝ) (k : S) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hne : P.Nonempty) (hw : ∀ q ∈ P, cmin ≤ w q ∧ w q ≤ cmax)
    (hvar : ∀ p ∈ P, ∀ q ∈ P, (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * ∑ s, (p s - q s) ^ 2) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (dx w k p) = 0 ∧ (∀ y, dot p y ≤ 0 → u y ≤ u (dx w k p)) ∧
        ∀ y, dot p y ≤ 0 → y ≠ dx w k p →
          (dot p y < 0 ∨ ∃ z' : S → ℝ, dot p z' = 0 ∧ 0 < dot z' (fun s => y s - dx w k p s) ∧
            ∃ t0 > 0, ∀ t, 0 < t → t < t0 → arc p z' t ∈ P) →
          u y < u (dx w k p) := by
  have hdot1 : ∀ q ∈ P, dot q q = 1 := by
    intro q hq
    rw [← hP q hq]
    unfold dot
    exact Finset.sum_congr rfl fun s _ => by ring
  have hbud : ∀ q ∈ P, dot q (dx w k q) = 0 := by
    intro q hq
    rw [dot_dx, hdot1 q hq]
    ring
  obtain ⟨q0, hq0⟩ := hne
  have hcmax : 0 < cmax := hcmin.trans_le ((hw q0 hq0).1.trans (hw q0 hq0).2)
  have hε'0 : 0 < min ε (1 / cmax) := lt_min hε (one_div_pos.2 hcmax)
  have hA := variable_afriat P ε κ cmin cmax hε hκ hκε hcmin w k hP hpos hw hvar
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    continuum_afriat P (fun q => -q k) (fun q => 1 / w q) (dx w k) _ (1 / cmin) hε'0 hA
      ⟨q0, hq0⟩
  refine ⟨U P (fun q => -q k) (fun q => 1 / w q) (dx w k), hc1, hc2, hc3, fun p hp =>
    ⟨hbud p hp, fun y hy => hc5 p hp y (by rw [hbud p hp]; exact hy),
      fun y hy _ hdir => ?_⟩⟩
  have hup : U P (fun q => -q k) (fun q => 1 / w q) (dx w k) (dx w k p) = -p k := hc4 p hp
  rcases hy.lt_or_eq with hlt | heq
  · have hsum : 0 < ∑ s, p s :=
      lt_of_lt_of_le (hε.trans_le (hpos p hp k))
        (Finset.single_le_sum (f := fun s => p s) (fun s _ => hε.le.trans (hpos p hp s))
          (mem_univ k))
    set c : ℝ := -dot p y / ∑ s, p s with hcdef
    have hc : 0 < c := div_pos (by linarith) hsum
    set y' : S → ℝ := fun s => y s + c with hy'def
    have hy' : dot p y' = 0 := by
      have e1 : dot p y' = dot p y + (∑ s, p s) * c := by
        simp only [dot, hy'def, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      have e2 : (∑ s, p s) * c = -dot p y := by
        rw [hcdef, mul_div_assoc']
        exact mul_div_cancel_left₀ _ hsum.ne'
      rw [e1, e2]
      ring
    have h1 := hc3 y y' (fun s => by simp only [hy'def]; linarith) ⟨k, by simp only [hy'def]; linarith⟩
    have h2 := hc5 p hp y' (by rw [hy', hbud p hp])
    exact h1.trans_le h2
  · rcases hdir with hlt' | ⟨z', hz', hD, t0, ht0, hrt⟩
    · linarith
    set z : S → ℝ := fun s => y s - dx w k p s with hzdef
    have hz : dot p z = 0 := by
      have e1 : dot p z = dot p y - dot p (dx w k p) := by
        simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
      rw [e1, heq, hbud p hp]
      ring
    have hN0 : 0 ≤ nsq z' := nsq_nonneg z'
    have hden : 0 < 4 * nsq z' * cmax + 1 := by positivity
    set t : ℝ := min (t0 / 2) (dot z' z / (4 * nsq z' * cmax + 1)) with htdef
    have ht : 0 < t := lt_min (by linarith) (div_pos hD hden)
    have htt0 : t < t0 := (min_le_left _ _).trans_lt (by linarith)
    have htc : t * (4 * nsq z' * cmax + 1) ≤ dot z' z := (le_div_iff₀ hden).1 (min_le_right _ _)
    have hq := hrt t ht htt0
    set q : S → ℝ := arc p z' t with hqdef
    have hpu := hP p hp
    have hqu := hP q hq
    have hqp := arc_dot_p p z' t hpu hz'
    have hqz := arc_dot_gen p z' z t
    rw [← hqdef] at hqp hqz
    rw [hz] at hqz
    have hd := dist_eq p q hpu hqu
    have hqp0 : 0 ≤ dot q p :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (hε.le.trans (hpos q hq s)) (hε.le.trans (hpos p hp s))
    have hwq := hw q hq
    have hwq0 : 0 < w q := hcmin.trans_le hwq.1
    have hpk1 : p k ≤ 1 := le_one_of_unit p hpu k (hε.le.trans (hpos p hp k))
    have hkey := key_upper ε κ hκ hκε k p q hpu hqu (hpos p hp k) hpk1 hqp0 (w p) (w q) hwq0
      (hvar p hp q hq)
    have hU := U_le P (fun q => -q k) (fun q => 1 / w q) (dx w k) _ (1 / cmin) hε'0 hA y q hq
    simp only [g] at hU
    rw [hbud q hq] at hU
    have hyz : dot q y = dot q (dx w k p) + dot q z := by
      simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hyz, dot_dx] at hU
    have e : 1 / w q * (w p * (q k - p k * dot q p) + dot q z - 0) =
        w p / w q * (q k - p k * dot q p) + dot q z / w q := by ring
    rw [e] at hU
    have h1a := arc_den z' t
    have h1a' : 1 + t ^ 2 * nsq z' ≠ 0 := h1a.ne'
    have hwq' : w q ≠ 0 := hwq0.ne'
    have htw : 2 * (t * nsq z' * w q) < dot z' z := by
      have h2 : t * nsq z' * w q ≤ t * nsq z' * cmax :=
        mul_le_mul_of_nonneg_left hwq.2 (mul_nonneg ht.le hN0)
      have h3 : 0 ≤ t * nsq z' * cmax := mul_nonneg (mul_nonneg ht.le hN0) hcmax.le
      have e3 : t * (4 * nsq z' * cmax + 1) = 4 * (t * nsq z' * cmax) + t := by ring
      rw [e3] at htc
      linarith
    have hneg : ∑ s, (p s - q s) ^ 2 + dot q z / w q < 0 := by
      rw [hd, hqp, hqz]
      have e2 : 2 - 2 * ((1 - t ^ 2 * nsq z') / (1 + t ^ 2 * nsq z')) +
          ((1 - t ^ 2 * nsq z') * 0 - 2 * t * dot z' z) / (1 + t ^ 2 * nsq z') / w q =
          2 * t * (2 * (t * nsq z' * w q) - dot z' z) / ((1 + t ^ 2 * nsq z') * w q) := by
        field_simp
        ring
      rw [e2]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos two_pos ht) (by linarith))
        (mul_pos h1a hwq0)
    rw [hup]
    linarith

omit [DecidableEq S] in
/-- **One-sided arcs in the closed cap.**  At a price of the closed cap, the short arc in a
tangent direction `z` stays in the cap whenever `z` is strictly inward on the active
coordinates. -/
theorem inward_arc (ε : ℝ) (hε : 0 < ε) (p : S → ℝ) (hp : ∑ s, p s ^ 2 = 1)
    (hpe : ∀ s, ε ≤ p s) (z : S → ℝ) (hz : dot p z = 0) (hin : ∀ s, p s = ε → z s < 0) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      arc p z t ∈ {q : S → ℝ | ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε ≤ q s} := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, 0 < t → ε ≤ arc p z t s := by
    rw [eventually_all]
    intro s
    rcases (hpe s).lt_or_eq with hlt | heq
    · have hc : Continuous fun t : ℝ => arc p z t s := by
        show Continuous fun t : ℝ =>
          ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z)
        exact Continuous.div (by fun_prop) (by fun_prop) fun t => (arc_den z t).ne'
      have h0 : arc p z 0 s = p s := by simp [arc]
      have ht := hc.tendsto 0
      rw [h0] at ht
      exact (ht.eventually (eventually_gt_nhds hlt)).mono fun t h _ => h.le
    · have hzs := hin s heq.symm
      have hN := nsq_nonneg z
      have hc0 : 0 < nsq z * ε + 1 := by positivity
      have hcpos : 0 < -z s / (nsq z * ε + 1) := div_pos (by linarith) hc0
      filter_upwards [eventually_lt_nhds hcpos] with t htc ht
      have h1 : t * (nsq z * ε + 1) < -z s := (lt_div_iff₀ hc0).1 htc
      have h1' : t * nsq z * ε + t < -z s := by
        have e : t * (nsq z * ε + 1) = t * nsq z * ε + t := by ring
        linarith
      have h3 : t * nsq z * ε ≤ -z s := by linarith
      have h2 : t * (t * nsq z * ε) ≤ t * (-z s) := mul_le_mul_of_nonneg_left h3 ht.le
      unfold arc
      rw [le_div_iff₀ (arc_den z t), ← heq]
      nlinarith [h2]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun t ht htd => ⟨arc_unit p z t hp hz, fun s => hball ?_ s ht⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht]
  exact htd

omit [DecidableEq S] in
/-- **The arc method is sharp on the cap.**  At an active coordinate (`p s = ε`), an arc in a
nonzero direction with `z s ≥ 0` leaves the cap immediately. -/
theorem arc_exits (ε : ℝ) (hε : 0 < ε) (p z : S → ℝ) (s : S) (hps : p s = ε)
    (hzs : 0 ≤ z s) (hN : 0 < nsq z) (t : ℝ) (ht : 0 < t) : arc p z t s < ε := by
  unfold arc
  rw [div_lt_iff₀ (arc_den z t), hps]
  have : 0 < t ^ 2 * nsq z * ε := by positivity
  nlinarith [mul_nonneg ht.le hzs]

/-- The closed cap `S_ε` of unit prices with all coordinates `≥ ε`. -/
def Pc (ε : ℝ) : Set (S → ℝ) := {q | ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε ≤ q s}

/-- **Unique demand on the closed cap.**  Under the stage-334 hypotheses on the *closed* cap,
Debreu's trade is the unique maximiser at every relatively interior price, and at a boundary
price against every budget trade `y` for which some strictly inward tangent `z'` has
`z'·(y − dx p) > 0`. -/
theorem debreu_closed_cap_unique (ε κ cmin cmax : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (hκε : 4 * κ ≤ ε) (hcmin : 0 < cmin) (w : (S → ℝ) → ℝ) (k : S)
    (hne : (Pc ε : Set (S → ℝ)).Nonempty) (hw : ∀ q ∈ Pc ε, cmin ≤ w q ∧ w q ≤ cmax)
    (hvar : ∀ p ∈ Pc ε, ∀ q ∈ Pc ε, (w p - w q) ^ 2 ≤ (κ * w q) ^ 2 * ∑ s, (p s - q s) ^ 2) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ Pc ε, dot p (dx w k p) = 0 ∧ (∀ y, dot p y ≤ 0 → u y ≤ u (dx w k p)) ∧
        (∀ y, dot p y ≤ 0 → y ≠ dx w k p → (∀ s, ε < p s) → u y < u (dx w k p)) ∧
        (∀ y, dot p y ≤ 0 → y ≠ dx w k p →
          (∃ z' : S → ℝ, dot p z' = 0 ∧ (∀ s, p s = ε → z' s < 0) ∧
            0 < dot z' (fun s => y s - dx w k p s)) → u y < u (dx w k p)) := by
  obtain ⟨u, h1, h2, h3, h4⟩ := debreu_directional_unique (Pc ε) ε κ cmin cmax hε hκ hκε hcmin
    w k (fun q hq => hq.1) (fun q hq => hq.2) hne hw hvar
  refine ⟨u, h1, h2, h3, fun p hp => ⟨(h4 p hp).1, (h4 p hp).2.1, fun y hy hyne hint => ?_,
    fun y hy hyne ⟨z', hz', hin, hD⟩ => (h4 p hp).2.2 y hy hyne
      (Or.inr ⟨z', hz', hD, inward_arc ε hε p hp.1 hp.2 z' hz' hin⟩)⟩⟩
  rcases hy.lt_or_eq with hlt | heq
  · exact (h4 p hp).2.2 y hy hyne (Or.inl hlt)
  · have htan : dot p (fun s => y s - dx w k p s) = 0 := by
      have hb := (h4 p hp).1
      simp only [dot, mul_sub, Finset.sum_sub_distrib]
      unfold dot at hb heq
      linarith
    have hpos' : 0 < dot (fun s => y s - dx w k p s) (fun s => y s - dx w k p s) := by
      obtain ⟨s, hs⟩ : ∃ s, y s ≠ dx w k p s := by
        by_contra h
        push Not at h
        exact hyne (funext h)
      have h1 : 0 < (y s - dx w k p s) * (y s - dx w k p s) :=
        mul_self_pos.2 (sub_ne_zero.2 hs)
      exact lt_of_lt_of_le h1
        (Finset.single_le_sum (f := fun s => (y s - dx w k p s) * (y s - dx w k p s))
          (fun _ _ => mul_self_nonneg _) (mem_univ s))
    exact (h4 p hp).2.2 y hy hyne (Or.inr ⟨_, htan, hpos',
      inward_arc ε hε p hp.1 hp.2 _ htan fun s hs => absurd hs (hint s).ne'⟩)


end BoundaryUnique

end

#print axioms BoundaryUnique.g_sub
#print axioms BoundaryUnique.lip_term
#print axioms BoundaryUnique.g_lip
#print axioms BoundaryUnique.g_lower
#print axioms BoundaryUnique.bdd
#print axioms BoundaryUnique.U_le
#print axioms BoundaryUnique.le_U
#print axioms BoundaryUnique.U_lip
#print axioms BoundaryUnique.U_continuous
#print axioms BoundaryUnique.U_concave
#print axioms BoundaryUnique.U_strictMono
#print axioms BoundaryUnique.U_at
#print axioms BoundaryUnique.continuum_afriat
#print axioms BoundaryUnique.dot_le_one
#print axioms BoundaryUnique.dot_dirk
#print axioms BoundaryUnique.dot_dx
#print axioms BoundaryUnique.dist_eq
#print axioms BoundaryUnique.le_one_of_unit
#print axioms BoundaryUnique.variable_afriat
#print axioms BoundaryUnique.key_upper
#print axioms BoundaryUnique.nsq_nonneg
#print axioms BoundaryUnique.arc_den
#print axioms BoundaryUnique.arc_dot_p
#print axioms BoundaryUnique.arc_dot_z
#print axioms BoundaryUnique.arc_unit
#print axioms BoundaryUnique.rich_open
#print axioms BoundaryUnique.debreu_variable_unique

#print axioms BoundaryUnique.arc_dot_gen
#print axioms BoundaryUnique.debreu_directional_unique
#print axioms BoundaryUnique.inward_arc
#print axioms BoundaryUnique.arc_exits
#print axioms BoundaryUnique.debreu_closed_cap_unique
