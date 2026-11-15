import Mathlib

/-!
Stage 331 (extends stage 330): unique demand on a continuum of prices.

Debreu's constant-weight consumer `x q = c (e_k − q_k q)` on any set `P` of unit prices with
coordinates at least `ε > 0` is rationalised by a continuous, concave, strictly monotone utility
for which `x p` is the **unique** maximiser on the budget `{y | p·y ≤ 0}` for every `p ∈ P`
(`debreu_constant_weight_unique`).

The utility is `U + δ W`, where `U` is the continuum Afriat utility of stage 330 and `W` is the
infimum, over tangent points `a` in the box `|a_s| ≤ 2c`, of the tangent planes of the strictly
concave quadratic `wq y = y_k − ‖y‖²/(2c)`. `W` agrees with `wq` on the box (which contains every
`x p`), is concave, globally Lipschitz, and loses at most `2 ∑(z − y)` when `y ≤ z` increases to
`z`; `U` gains at least `ε'² ∑(z − y)`, so `δ = ε'²/4` keeps strict monotonicity.
Uniqueness: for `y ≠ x p` on the budget, a tangent point on the segment from `x p` to `y` gives
`W y < wq (x p) = W (x p)`, while `U y ≤ U (x p)`.

Scope: the weight `c` and the good `k` are fixed (one consumer). Price-dependent weights, and
the full continuous Mantel/Debreu decomposition on `S_ε`, are not done here.

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

open Finset

namespace ContinuumUnique

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

/-- Continuity from an `ℓ¹` Lipschitz bound. -/
theorem cont_of_lip (f : (S → ℝ) → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hl : ∀ y z : S → ℝ, |f z - f y| ≤ Λ * ∑ s, |z s - y s|) : Continuous f := by
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
  have hratio : Λ * Fintype.card S < K := by
    have e : Λ * (↑(Fintype.card S) + 1) = Λ * Fintype.card S + Λ := by ring
    rw [hK, e]
    linarith
  rw [Real.dist_eq]
  calc |f z - f y| ≤ Λ * ∑ s, |z s - y s| := hl y z
    _ ≤ Λ * (Fintype.card S * (r / K)) := mul_le_mul_of_nonneg_left hsum hΛ
    _ = r * (Λ * Fintype.card S) / K := by ring
    _ < r := by
      rw [div_lt_iff₀ hK0]
      exact mul_lt_mul_of_pos_left hratio hr

/-- **Quantitative monotonicity of `U`.** -/
theorem U_mono_sum (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ) (ε Λ : ℝ)
    (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hne : P.Nonempty) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) : U P V lam x y + ε * ε * ∑ s, (z s - y s) ≤ U P V lam x z := by
  have hD : 0 ≤ ∑ s, (z s - y s) := Finset.sum_nonneg fun s _ => sub_nonneg.2 (hyz s)
  refine le_U P V lam x hne z _ fun q hq => ?_
  have a1 := U_le P V lam x ε Λ hε h y q hq
  have a2 := g_sub V lam x q y z
  have hq1 : ∀ s, ε ≤ q s := fun s => (h.2.1 q hq s).1
  have hdot : ε * ∑ s, (z s - y s) ≤ dot q (fun s => z s - y s) := by
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hq1 s) (sub_nonneg.2 (hyz s))
  have hl := (h.1 q hq).1
  have t3 : ε * (ε * ∑ s, (z s - y s)) ≤ lam q * dot q (fun s => z s - y s) :=
    mul_le_mul hl hdot (mul_nonneg hε.le hD) (hε.le.trans hl)
  have e : ε * ε * ∑ s, (z s - y s) = ε * (ε * ∑ s, (z s - y s)) := by ring
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


/-! ### The tangent-plane penalty `W` -/

/-- Squared Euclidean norm. -/
def nsq (y : S → ℝ) : ℝ := ∑ s, y s ^ 2

/-- The strictly concave quadratic `y_k − ‖y‖² / (2c)`. -/
def wq (c : ℝ) (k : S) (y : S → ℝ) : ℝ := y k - nsq y / (2 * c)

/-- Gradient of `wq` at `a`. -/
def coef (c : ℝ) (k : S) (a : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - a s / c

/-- Tangent plane of `wq` at `a`. -/
def T (c : ℝ) (k : S) (a y : S → ℝ) : ℝ := wq c k a + ∑ s, coef c k a s * (y s - a s)

/-- The box of tangent points. -/
def box (R : ℝ) : Set (S → ℝ) := {a | ∀ s, |a s| ≤ R}

/-- The penalty: infimum of the tangent planes at points of the box. -/
def W (c R : ℝ) (k : S) (y : S → ℝ) : ℝ := ⨅ a : (box R : Set (S → ℝ)), T c k a.1 y

theorem T_eq (c : ℝ) (k : S) (a y : S → ℝ) :
    T c k a y = wq c k y + nsq (fun s => y s - a s) / (2 * c) := by
  have e1 : ∑ s, coef c k a s * (y s - a s) = (y k - a k) - (∑ s, a s * (y s - a s)) / c := by
    have e : ∀ s, coef c k a s * (y s - a s) =
        (if s = k then y s - a s else 0) - a s * (y s - a s) / c := by
      intro s
      unfold coef
      split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Finset.sum_div]
  have hs : nsq (fun s => y s - a s) =
      ∑ s, y s ^ 2 - 2 * ∑ s, a s * (y s - a s) - ∑ s, a s ^ 2 := by
    unfold nsq
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  unfold T wq
  rw [e1, hs]
  unfold nsq
  ring

theorem T_sub (c : ℝ) (k : S) (a y z : S → ℝ) :
    T c k a z - T c k a y = ∑ s, coef c k a s * (z s - y s) := by
  unfold T
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem wq_le_T (c : ℝ) (hc : 0 < c) (k : S) (a y : S → ℝ) : wq c k y ≤ T c k a y := by
  rw [T_eq]
  have : 0 ≤ nsq (fun s => y s - a s) / (2 * c) :=
    div_nonneg (Finset.sum_nonneg fun s _ => sq_nonneg _) (by linarith)
  linarith

theorem T_self (c : ℝ) (k : S) (a : S → ℝ) : T c k a a = wq c k a := by
  unfold T
  simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem W_bdd (c R : ℝ) (hc : 0 < c) (k : S) (y : S → ℝ) :
    BddBelow (Set.range fun a : (box R : Set (S → ℝ)) => T c k a.1 y) :=
  ⟨wq c k y, by
    rintro _ ⟨a, rfl⟩
    exact wq_le_T c hc k a y⟩

theorem W_le (c R : ℝ) (hc : 0 < c) (k : S) (y a : S → ℝ) (ha : a ∈ box R) :
    W c R k y ≤ T c k a y :=
  ciInf_le (W_bdd c R hc k y) ⟨a, ha⟩

omit [Fintype S] [DecidableEq S] in
theorem zero_mem_box (R : ℝ) (hR : 0 ≤ R) : (0 : S → ℝ) ∈ box R := by
  show ∀ s, |(0 : S → ℝ) s| ≤ R
  intro s
  simp only [Pi.zero_apply, abs_zero]
  exact hR

theorem le_W (c R : ℝ) (hR : 0 ≤ R) (k : S) (y : S → ℝ) (b : ℝ)
    (hb : ∀ a ∈ box R, b ≤ T c k a y) : b ≤ W c R k y := by
  have : Nonempty (box R : Set (S → ℝ)) := ⟨⟨0, zero_mem_box R hR⟩⟩
  exact le_ciInf fun a => hb a a.2

theorem W_at (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (k : S) (a : S → ℝ) (ha : a ∈ box R) :
    W c R k a = wq c k a := by
  apply le_antisymm
  · have := W_le c R hc k a a ha
    rwa [T_self] at this
  · exact le_W c R hR k a _ fun b _ => wq_le_T c hc k b a

omit [Fintype S] in
theorem coef_lower (c R : ℝ) (hc : 0 < c) (k : S) (a : S → ℝ) (ha : a ∈ box R) (s : S) :
    -(R / c) ≤ coef c k a s := by
  have h1 : a s ≤ R := (abs_le.1 (ha s)).2
  have h2 : a s / c ≤ R / c := div_le_div_of_nonneg_right h1 hc.le
  unfold coef
  split_ifs <;> linarith

omit [Fintype S] in
theorem coef_abs (c R : ℝ) (hc : 0 < c) (k : S) (a : S → ℝ) (ha : a ∈ box R) (s : S) :
    |coef c k a s| ≤ 1 + R / c := by
  have h1 := abs_le.1 (ha s)
  have h2 : a s / c ≤ R / c := div_le_div_of_nonneg_right h1.2 hc.le
  have h3 : -R / c ≤ a s / c := div_le_div_of_nonneg_right h1.1 hc.le
  have h4 : -R / c = -(R / c) := neg_div c R
  unfold coef
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

theorem T_lip (c R : ℝ) (hc : 0 < c) (k : S) (a : S → ℝ) (ha : a ∈ box R) (y z : S → ℝ) :
    |T c k a z - T c k a y| ≤ (1 + R / c) * ∑ s, |z s - y s| := by
  rw [T_sub, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (coef_abs c R hc k a ha s) (abs_nonneg _)

theorem W_lip (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (k : S) (y z : S → ℝ) :
    |W c R k z - W c R k y| ≤ (1 + R / c) * ∑ s, |z s - y s| := by
  have hsym : ∑ s, |y s - z s| = ∑ s, |z s - y s| :=
    Finset.sum_congr rfl fun s _ => abs_sub_comm _ _
  have h1 : W c R k z - (1 + R / c) * ∑ s, |z s - y s| ≤ W c R k y := by
    refine le_W c R hR k y _ fun a ha => ?_
    have a1 := W_le c R hc k z a ha
    have a2 := (abs_le.1 (T_lip c R hc k a ha y z)).2
    linarith
  have h2 : W c R k y - (1 + R / c) * ∑ s, |z s - y s| ≤ W c R k z := by
    refine le_W c R hR k z _ fun a ha => ?_
    have a1 := W_le c R hc k y a ha
    have a2 := (abs_le.1 (T_lip c R hc k a ha z y)).2
    rw [hsym] at a2
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem W_continuous (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (k : S) : Continuous (W c R k) :=
  cont_of_lip _ (1 + R / c) (by have := div_nonneg hR hc.le; linarith) (W_lip c R hc hR k)

theorem W_concave (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (k : S) :
    ConcaveOn ℝ Set.univ (W c R k) := by
  refine ⟨convex_univ, fun y _ z _ α β hα hβ hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_W c R hR k _ _ fun a ha => ?_
  have h1 := mul_le_mul_of_nonneg_left (W_le c R hc k y a ha) hα
  have h2 := mul_le_mul_of_nonneg_left (W_le c R hc k z a ha) hβ
  have e : T c k a (α • y + β • z) = α * T c k a y + β * T c k a z := by
    have e1 : ∑ s, coef c k a s * ((α * y s + β * z s) - a s) =
        α * ∑ s, coef c k a s * (y s - a s) + β * ∑ s, coef c k a s * (z s - a s) +
          (α + β - 1) * ∑ s, coef c k a s * a s := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    linear_combination (∑ s, coef c k a s * a s - wq c k a) * hab
  rw [e]
  linarith

/-- `W` loses at most `(R/c) ∑ (z − y)` when `y ≤ z`. -/
theorem W_mono (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (k : S) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) : W c R k y - R / c * ∑ s, (z s - y s) ≤ W c R k z := by
  refine le_W c R hR k z _ fun a ha => ?_
  have a1 := W_le c R hc k y a ha
  have a2 := T_sub c k a y z
  have a3 : ∑ s, -(R / c) * (z s - y s) ≤ ∑ s, coef c k a s * (z s - y s) :=
    Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_right (coef_lower c R hc k a ha s) (sub_nonneg.2 (hyz s))
  have a4 : ∑ s, -(R / c) * (z s - y s) = -(R / c * ∑ s, (z s - y s)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

/-- **Debreu's constant-weight consumer has unique demand on a continuum.**  On any non-empty set
`P` of unit prices with coordinates at least `ε > 0`, there is a continuous, concave, strictly
monotone utility for which, at every `p ∈ P`, the trade `c (e_k − p_k p)` costs nothing and is
the unique maximiser on the budget `{y | p·y ≤ 0}`. -/
theorem debreu_constant_weight_unique (P : Set (S → ℝ)) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (k : S) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s)
    (hne : P.Nonempty) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => c * dirk k p s) = 0 ∧
        ∀ y, dot p y ≤ 0 → y ≠ (fun s => c * dirk k p s) → u y < u (fun s => c * dirk k p s) := by
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
  obtain ⟨hc1, hc2, -, -, hc5⟩ :=
    continuum_afriat P (fun q => -q k) (fun _ => 1 / c) x ε' (1 / c) hε'0 hA hne
  set Uf := U P (fun q => -q k) (fun _ => 1 / c) x with hUf
  set δ : ℝ := ε' * ε' / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hR : (0 : ℝ) ≤ 2 * c := by linarith
  have hRc : 2 * c / c = 2 := by rw [mul_div_assoc, div_self hc.ne', mul_one]
  refine ⟨fun y => Uf y + δ * W c (2 * c) k y,
    hc1.add (continuous_const.mul (W_continuous c (2 * c) hc hR k)), ?_, ?_, ?_⟩
  · -- concave
    have hWc := W_concave c (2 * c) hc hR k
    refine ⟨convex_univ, fun y _ z _ α β hα hβ hab => ?_⟩
    have h1 := hc2.2 (Set.mem_univ y) (Set.mem_univ z) hα hβ hab
    have h2 := hWc.2 (Set.mem_univ y) (Set.mem_univ z) hα hβ hab
    simp only [smul_eq_mul] at h1 h2 ⊢
    have h3 := mul_le_mul_of_nonneg_left h2 hδ0.le
    nlinarith
  · -- strictly monotone
    intro y z hyz hlt
    obtain ⟨s0, hs0⟩ := hlt
    have hD : 0 < ∑ s, (z s - y s) :=
      Finset.sum_pos' (fun s _ => sub_nonneg.2 (hyz s)) ⟨s0, mem_univ _, sub_pos.2 hs0⟩
    have hU := U_mono_sum P (fun q => -q k) (fun _ => 1 / c) x ε' (1 / c) hε'0 hA hne y z hyz
    have hW := W_mono c (2 * c) hc hR k y z hyz
    rw [hRc] at hW
    have hW' := mul_le_mul_of_nonneg_left hW hδ0.le
    have hp : 0 < ε' * ε' * ∑ s, (z s - y s) := by positivity
    show Uf y + δ * W c (2 * c) k y < Uf z + δ * W c (2 * c) k z
    rw [hδ] at hW' ⊢
    nlinarith
  · intro p hp
    refine ⟨hbud p hp, fun y hy hne' => ?_⟩
    have hp0 : ∀ s, 0 < p s := fun s => hε.trans_le (hpos p hp s)
    -- U part
    have hU : Uf y ≤ Uf (x p) := hc5 p hp y (by rw [hbud p hp]; exact hy)
    -- x p lies in the box
    have hdirk : ∀ s, |dirk k p s| ≤ 1 := by
      intro s
      have h1 := hle1 p hp k
      have h2 := hle1 p hp s
      have h3 : 0 ≤ p k * p s := mul_nonneg (hp0 k).le (hp0 s).le
      have h4 : p k * p s ≤ 1 := by nlinarith [hp0 k, hp0 s]
      unfold dirk
      rw [abs_le]
      split_ifs <;> constructor <;> linarith
    have hxs : ∀ s, |x p s| ≤ c := by
      intro s
      simp only [hx]
      rw [abs_mul, abs_of_pos hc]
      exact mul_le_of_le_one_right hc.le (hdirk s)
    have hxbox : x p ∈ box (2 * c) := by
      show ∀ s, |x p s| ≤ 2 * c
      intro s
      have := hxs s
      linarith
    have hWx : W c (2 * c) k (x p) = wq c k (x p) := W_at c (2 * c) hc hR k (x p) hxbox
    -- gradient of wq at x p
    have hcoef : ∀ s, coef c k (x p) s = p k * p s := by
      intro s
      simp only [coef, hx, dirk]
      rw [mul_div_cancel_left₀ _ hc.ne']
      ring
    have hsum : ∑ s, coef c k (x p) s * (y s - x p s) = p k * dot p y := by
      have e : ∑ s, coef c k (x p) s * (y s - x p s) = p k * (dot p y - dot p (x p)) := by
        simp only [hcoef, dot, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e, hbud p hp, sub_zero]
    set N := nsq (fun s => y s - x p s) with hN
    have hN0 : 0 < N := by
      obtain ⟨s1, hs1⟩ : ∃ s, y s ≠ x p s := by
        by_contra hcon
        exact hne' (funext fun s => not_not.1 fun h => hcon ⟨s, h⟩)
      exact Finset.sum_pos' (fun s _ => sq_nonneg _)
        ⟨s1, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hs1)))⟩
    have hwy : wq c k y = wq c k (x p) + p k * dot p y - N / (2 * c) := by
      have e1 := T_eq c k (x p) y
      have e2 : T c k (x p) y = wq c k (x p) + ∑ s, coef c k (x p) s * (y s - x p s) := rfl
      rw [e2, hsum] at e1
      linarith
    -- tangent point on the segment
    set D := ∑ s, |y s - x p s| with hDdef
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun s _ => abs_nonneg _
    have hcD : 0 < c + D := by linarith
    set t := c / (c + D) with ht
    have ht0 : 0 < t := div_pos hc hcD
    have ht1 : t ≤ 1 := (div_le_one hcD).2 (by linarith)
    have htD : t * D ≤ c := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hcD]
      nlinarith
    set a : S → ℝ := fun s => x p s + t * (y s - x p s) with ha
    have habox : a ∈ box (2 * c) := by
      show ∀ s, |a s| ≤ 2 * c
      intro s
      have e2 : |y s - x p s| ≤ D :=
        Finset.single_le_sum (f := fun s' => |y s' - x p s'|) (fun _ _ => abs_nonneg _) (mem_univ s)
      have e4 : |t * (y s - x p s)| ≤ t * D := by
        rw [abs_mul, abs_of_pos ht0]
        exact mul_le_mul_of_nonneg_left e2 ht0.le
      have e5 := abs_add_le (x p s) (t * (y s - x p s))
      have e1 := hxs s
      show |x p s + t * (y s - x p s)| ≤ 2 * c
      linarith
    have hya : nsq (fun s => y s - a s) = (1 - t) ^ 2 * N := by
      rw [hN]
      unfold nsq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by simp only [ha]; ring
    have hTa : T c k a y = wq c k (x p) + p k * dot p y - N / (2 * c) + (1 - t) ^ 2 * (N / (2 * c)) := by
      rw [T_eq, hya, hwy, mul_div_assoc]
    have hQ : 0 < N / (2 * c) := div_pos hN0 (by linarith)
    have h1t : (1 - t) ^ 2 < 1 := by nlinarith
    have hlt := mul_lt_mul_of_pos_right h1t hQ
    have hpk : p k * dot p y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hp0 k).le hy
    have hWy : W c (2 * c) k y ≤ T c k a y := W_le c (2 * c) hc k y a habox
    have hWlt : W c (2 * c) k y < W c (2 * c) k (x p) := by
      rw [hWx]
      linarith
    show Uf y + δ * W c (2 * c) k y < Uf (x p) + δ * W c (2 * c) k (x p)
    have := mul_lt_mul_of_pos_left hWlt hδ0
    linarith

end ContinuumUnique

end

#print axioms ContinuumUnique.g_sub
#print axioms ContinuumUnique.lip_term
#print axioms ContinuumUnique.g_lip
#print axioms ContinuumUnique.g_lower
#print axioms ContinuumUnique.bdd
#print axioms ContinuumUnique.U_le
#print axioms ContinuumUnique.le_U
#print axioms ContinuumUnique.U_lip
#print axioms ContinuumUnique.U_continuous
#print axioms ContinuumUnique.U_concave
#print axioms ContinuumUnique.U_strictMono
#print axioms ContinuumUnique.U_at
#print axioms ContinuumUnique.continuum_afriat
#print axioms ContinuumUnique.dot_le_one
#print axioms ContinuumUnique.dot_dirk
#print axioms ContinuumUnique.debreu_constant_weight
#print axioms ContinuumUnique.cont_of_lip
#print axioms ContinuumUnique.U_mono_sum
#print axioms ContinuumUnique.T_eq
#print axioms ContinuumUnique.T_sub
#print axioms ContinuumUnique.wq_le_T
#print axioms ContinuumUnique.T_self
#print axioms ContinuumUnique.W_bdd
#print axioms ContinuumUnique.W_le
#print axioms ContinuumUnique.zero_mem_box
#print axioms ContinuumUnique.le_W
#print axioms ContinuumUnique.W_at
#print axioms ContinuumUnique.coef_lower
#print axioms ContinuumUnique.coef_abs
#print axioms ContinuumUnique.T_lip
#print axioms ContinuumUnique.W_lip
#print axioms ContinuumUnique.W_continuous
#print axioms ContinuumUnique.W_concave
#print axioms ContinuumUnique.W_mono
#print axioms ContinuumUnique.debreu_constant_weight_unique
