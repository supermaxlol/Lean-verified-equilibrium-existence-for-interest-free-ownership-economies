import Mathlib

/-!
Stage 336 (extends stage 330): the weight `w q = q_k` reduces to a one-variable inequality.

Debreu's consumer `k` with weight `w q = q_k` trades `x q = q_k · (e_k − q_k q)` at unit price `q`.
The small-constant condition of stage 334 does not cover it (the relative Lipschitz constant of
`q_k` is about `1/q_k ≥ 1`).

* `cs_bound` — Cauchy–Schwarz on the coordinates other than `k`:
  `q·p ≤ q_k p_k + √((1 − q_k²)(1 − p_k²))` for unit `p, q`.
* `weight_pk_afriat` — if `F, L : ℝ → ℝ` satisfy, for all `a, b ∈ [ε, β]`,
    `F b − F a ≤ L a · b · (a − b · (a b + √((1 − a²)(1 − b²))))`
  and `L ∈ [ℓ, Λ]` on `[ε, β]` (`ℓ > 0`), then `V q = F (q_k)`, `λ q = L (q_k)` are continuum
  Afriat numbers for this consumer on every set `P` of unit prices with coordinates in `[ε, β]`.
* `weight_pk_rationalised` — consequently (stage 330) the trades are optimal for one continuous,
  concave, strictly monotone utility on all of `P`.

Scope: this is a reduction only. The one-variable inequality is **not proved here** for any
specific `F, L`. Numerically (grid checks, not proofs) `L a = a √(1 − a²) e^{−K arccos a}`,
`F' = −a L` satisfies it on `[ε, √(1 − ε²)]` for `K` large enough (`K ≈ 10` at `ε = 0.1`,
`K ≈ 20` at `ε = 0.05`). Uniqueness is not addressed, and the general Debreu weight
`α_k = Z_k + A p_k` is not covered.

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

namespace WeightPkReduction

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


/-! ### Stage 336: the weight `q_k` reduces to one variable -/

theorem cs_bound (k : S) (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1)
    (hq : ∑ s, q s ^ 2 = 1) :
    dot q p ≤ q k * p k + Real.sqrt ((1 - q k ^ 2) * (1 - p k ^ 2)) := by
  have e1 := Finset.add_sum_erase univ (fun s => q s * p s) (mem_univ k)
  have e2 := Finset.add_sum_erase univ (fun s => q s ^ 2) (mem_univ k)
  have e3 := Finset.add_sum_erase univ (fun s => p s ^ 2) (mem_univ k)
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ.erase k) q p
  have hq' : ∑ s ∈ univ.erase k, q s ^ 2 = 1 - q k ^ 2 := by linarith
  have hp' : ∑ s ∈ univ.erase k, p s ^ 2 = 1 - p k ^ 2 := by linarith
  rw [hq', hp'] at h
  have h2 := Real.abs_le_sqrt h
  have h3 := le_abs_self (∑ s ∈ univ.erase k, q s * p s)
  have hd : dot q p = q k * p k + ∑ s ∈ univ.erase k, q s * p s := by
    unfold dot
    linarith
  linarith

/-- **Reduction for the weight `q_k`.** The one-variable inequality on `[ε, β]` gives continuum
Afriat numbers `V q = F (q k)`, `λ q = L (q k)` for Debreu's consumer with weight `q_k`. -/
theorem weight_pk_afriat (P : Set (S → ℝ)) (ε β ℓ Λ : ℝ) (hε : 0 < ε) (hℓ : 0 < ℓ) (k : S)
    (F L : ℝ → ℝ) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s)
    (hβ : ∀ q ∈ P, ∀ s, q s ≤ β)
    (hL : ∀ a, ε ≤ a → a ≤ β → ℓ ≤ L a ∧ L a ≤ Λ)
    (hscalar : ∀ a b, ε ≤ a → a ≤ β → ε ≤ b → b ≤ β →
      F b - F a ≤ L a * (b * (a - b * (a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)))))) :
    Afriat P (fun q => F (q k)) (fun q => L (q k)) (fun q s => q k * dirk k q s)
      (min ε ℓ) Λ := by
  set x : (S → ℝ) → S → ℝ := fun q s => q k * dirk k q s with hx
  have hdx : ∀ p q, dot q (x p) = p k * (q k - p k * dot q p) := by
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
  refine ⟨fun q hq => ⟨(min_le_right _ _).trans (hL _ (hpos q hq k) (hβ q hq k)).1,
      (hL _ (hpos q hq k) (hβ q hq k)).2⟩,
    fun q hq s => ⟨(min_le_left _ _).trans (hpos q hq s), hle1 q hq s⟩,
    fun p hp q hq => ?_⟩
  show F (p k) ≤ F (q k) + L (q k) * (dot q (x p) - dot q (x q))
  rw [hbud q hq, hdx, sub_zero]
  have h1 := cs_bound k p q (hP p hp) (hP q hq)
  have h2 := hscalar (q k) (p k) (hpos q hq k) (hβ q hq k) (hpos p hp k) (hβ p hp k)
  have hb : 0 ≤ p k := hε.le.trans (hpos p hp k)
  have hLq : 0 ≤ L (q k) := hℓ.le.trans (hL _ (hpos q hq k) (hβ q hq k)).1
  have h3 : p k * (q k - p k * (q k * p k + Real.sqrt ((1 - q k ^ 2) * (1 - p k ^ 2)))) ≤
      p k * (q k - p k * dot q p) := by
    have h4 : p k * dot q p ≤ p k * (q k * p k + Real.sqrt ((1 - q k ^ 2) * (1 - p k ^ 2))) :=
      mul_le_mul_of_nonneg_left h1 hb
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left h3 hLq
  linarith

/-- **Consequence.** Under the one-variable inequality, Debreu's consumer with weight `q_k` is
rationalised on the whole continuum `P` by one continuous, concave, strictly monotone utility. -/
theorem weight_pk_rationalised (P : Set (S → ℝ)) (ε β ℓ Λ : ℝ) (hε : 0 < ε) (hℓ : 0 < ℓ)
    (k : S) (F L : ℝ → ℝ) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s)
    (hβ : ∀ q ∈ P, ∀ s, q s ≤ β)
    (hL : ∀ a, ε ≤ a → a ≤ β → ℓ ≤ L a ∧ L a ≤ Λ)
    (hscalar : ∀ a b, ε ≤ a → a ≤ β → ε ≤ b → b ≤ β →
      F b - F a ≤ L a * (b * (a - b * (a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))))))
    (hne : P.Nonempty) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => p k * dirk k p s) = 0 ∧
        ∀ y, dot p y ≤ 0 → u y ≤ u (fun s => p k * dirk k p s) := by
  have hA := weight_pk_afriat P ε β ℓ Λ hε hℓ k F L hP hpos hβ hL hscalar
  obtain ⟨hc1, hc2, hc3, -, hc5⟩ :=
    continuum_afriat P (fun q => F (q k)) (fun q => L (q k)) (fun q s => q k * dirk k q s)
      (min ε ℓ) Λ (lt_min hε hℓ) hA hne
  have hbud : ∀ p ∈ P, dot p (fun s => p k * dirk k p s) = 0 := by
    intro p hp
    have e : dot p (fun s => p k * dirk k p s) = p k * dot p (dirk k p) := by
      simp only [dot]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h1 : dot p p = 1 := by
      rw [← hP p hp]
      unfold dot
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, dot_dirk, h1]
    ring
  refine ⟨_, hc1, hc2, hc3, fun p hp => ⟨hbud p hp, fun y hy => ?_⟩⟩
  exact hc5 p hp y (by rw [hbud p hp]; exact hy)

end WeightPkReduction

end

#print axioms WeightPkReduction.g_sub
#print axioms WeightPkReduction.lip_term
#print axioms WeightPkReduction.g_lip
#print axioms WeightPkReduction.g_lower
#print axioms WeightPkReduction.bdd
#print axioms WeightPkReduction.U_le
#print axioms WeightPkReduction.le_U
#print axioms WeightPkReduction.U_lip
#print axioms WeightPkReduction.U_continuous
#print axioms WeightPkReduction.U_concave
#print axioms WeightPkReduction.U_strictMono
#print axioms WeightPkReduction.U_at
#print axioms WeightPkReduction.continuum_afriat
#print axioms WeightPkReduction.dot_le_one
#print axioms WeightPkReduction.dot_dirk
#print axioms WeightPkReduction.debreu_constant_weight
#print axioms WeightPkReduction.cs_bound
#print axioms WeightPkReduction.weight_pk_afriat
#print axioms WeightPkReduction.weight_pk_rationalised
