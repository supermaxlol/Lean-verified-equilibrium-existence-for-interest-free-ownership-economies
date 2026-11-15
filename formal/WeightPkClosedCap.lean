import Mathlib

/-!
# Stage 348: unique demand up to the boundary of the closed cap

This file is stage 347 in full, with `rich_band` and `pk_unique_closed_cap` added at the end of
`PkExplicit`: rationalise on a slightly larger open band, so that boundary prices of the closed
cap `[ε, β]` are interior to the rich set.

## Stage 347: unique demand for Debreu's weight-`p_k` consumer (first-order arc argument)

Stage 335 proved unique demand only for weights with a small relative Lipschitz constant
(`4κ ≤ ε`), via a quadratic upper bound (`key_upper`).  The weight `p_k` is not of that kind.
This file replaces the quadratic bound by a first-order argument that works for any continuum
Afriat data whose affine pieces vary differentiably along arcs:

* `afriat_arc_unique` — generic.  Let `U` be the continuum Afriat utility of stage 330 with
  `p·x(p) = 0` on `P`.  If `P` contains the short arcs leaving `p` in the directions `±z`,
  `z = y − x p`, and `t ↦ V(q t) + λ(q t) · q t · x(p)` is differentiable at `0` along that arc,
  then every budget trade `y ≠ x p` with `p·y = 0` has `U y < U (x p)`.  Proof: the Afriat
  inequalities make that function locally minimal at `0`, so its derivative vanishes, while the
  budget term contributes `λ · q t · z ≤ −ε t ‖z‖²` at first order.
* `weight_pk_unique` — the weight-`p_k` consumer of stage 336, with any differentiable `F, L`
  satisfying the one-variable inequality, has `p_k (e_k − p_k p)` as the **unique** maximiser
  on the budget, for every `p` in a rich `P` with all coordinates in `[ε, β]`, `β < 1`.
* `pk_unique_explicit` — the same for the explicit `F K, L K` of stage 339 (`K σ ≥ 7`).

Scope: uniqueness is at prices `p` around which `P` contains short arcs in every tangent
direction (relatively interior prices, as in stage 335).  Boundary prices of a closed `P`, the
weight `A p_k + Z_k` (stage 346; it needs `Z_k` differentiable for this argument), and the
continuous Mantel/Debreu decomposition are **not** covered.
-/

noncomputable section

namespace WeightPkUnique

open Finset Filter Topology

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


omit [DecidableEq S] in
theorem nsq_neg (z : S → ℝ) : nsq (fun s => -z s) = nsq z := by
  unfold nsq
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
theorem arc_neg (p z : S → ℝ) (t : ℝ) : arc p z (-t) = arc p (fun s => -z s) t := by
  funext s
  unfold arc
  rw [nsq_neg]
  ring

omit [DecidableEq S] in
theorem arc_zero (p z : S → ℝ) : arc p z 0 = p := by
  funext s
  simp [arc]

omit [DecidableEq S] in
theorem arc_diff (p z : S → ℝ) (s : S) : DifferentiableAt ℝ (fun t => arc p z t s) 0 := by
  show DifferentiableAt ℝ (fun t : ℝ =>
    ((1 - t ^ 2 * nsq z) * p s - 2 * t * z s) / (1 + t ^ 2 * nsq z)) 0
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (arc_den z 0).ne'

omit [DecidableEq S] in
/-- **Generic first-order uniqueness on a continuum.** -/
theorem afriat_arc_unique (P : Set (S → ℝ)) (V lam : (S → ℝ) → ℝ) (x : (S → ℝ) → S → ℝ)
    (ε Λ : ℝ) (hε : 0 < ε) (h : Afriat P V lam x ε Λ) (hbud : ∀ q ∈ P, dot q (x q) = 0)
    (p : S → ℝ) (hp : p ∈ P) (_hpu : ∑ s, p s ^ 2 = 1) (y : S → ℝ) (hy : dot p y = 0)
    (hyne : y ≠ x p)
    (hrich : ∀ z : S → ℝ, dot p z = 0 → ∃ t0 > 0, ∀ t, 0 < t → t < t0 → arc p z t ∈ P)
    (hdiff : DifferentiableAt ℝ (fun t => V (arc p (fun s => y s - x p s) t) +
      lam (arc p (fun s => y s - x p s) t) * dot (arc p (fun s => y s - x p s) t) (x p)) 0) :
    U P V lam x y < U P V lam x (x p) := by
  set z : S → ℝ := fun s => y s - x p s with hzdef
  have hz : dot p z = 0 := by
    have e1 : dot p z = dot p y - dot p (x p) := by
      simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
    rw [e1, hy, hbud p hp]
    ring
  have hzn : dot p (fun s => -z s) = 0 := by
    have e1 : dot p (fun s => -z s) = -dot p z := by
      simp only [dot, mul_neg, Finset.sum_neg_distrib]
    rw [e1, hz]
    ring
  have hN : 0 < nsq z := by
    obtain ⟨s, hs⟩ : ∃ s, y s ≠ x p s := by
      by_contra hc
      push Not at hc
      exact hyne (funext hc)
    have hzs : z s ≠ 0 := by simp only [hzdef]; exact sub_ne_zero.2 hs
    have h1 : 0 < z s ^ 2 := by positivity
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum (f := fun s => z s ^ 2) (fun _ _ => sq_nonneg _) (mem_univ s))
  obtain ⟨t1, ht1, hr1⟩ := hrich z hz
  obtain ⟨t2, ht2, hr2⟩ := hrich (fun s => -z s) hzn
  set φ : ℝ → ℝ := fun t => V (arc p z t) + lam (arc p z t) * dot (arc p z t) (x p) with hφ
  have hφ0 : φ 0 = V p := by
    simp only [hφ, arc_zero, hbud p hp, mul_zero, add_zero]
  have hmem : ∀ t, |t| < min t1 t2 → arc p z t ∈ P := by
    intro t ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · rw [abs_of_neg hlt] at ht
      have e : arc p z t = arc p (fun s => -z s) (-t) := by
        rw [← arc_neg, neg_neg]
      rw [e]
      exact hr2 (-t) (by linarith) (by linarith [min_le_right t1 t2])
    · rw [heq, arc_zero]; exact hp
    · rw [abs_of_pos hgt] at ht
      exact hr1 t hgt (by linarith [min_le_left t1 t2])
  have hφge : ∀ t, |t| < min t1 t2 → V p ≤ φ t := by
    intro t ht
    have hq := hmem t ht
    have := h.2.2 p hp (arc p z t) hq
    simp only [g, hbud _ hq, sub_zero] at this
    exact this
  have hmin : IsLocalMin φ 0 := by
    have hball : Metric.ball (0 : ℝ) (min t1 t2) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ (lt_min ht1 ht2)
    filter_upwards [hball] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    rw [hφ0]
    exact hφge t ht
  have hd := hdiff.hasDerivAt
  rw [hmin.deriv_eq_zero] at hd
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ne_of_gt ht))
  have hη : 0 < ε * nsq z / 2 := by positivity
  have ev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope φ 0 t < ε * nsq z / 2 :=
    hsl.eventually (eventually_lt_nhds hη)
  have hc : Continuous fun t : ℝ => t ^ 2 * nsq z := by fun_prop
  have ev2 : ∀ᶠ t in 𝓝 (0 : ℝ), t < min t1 t2 ∧ t ^ 2 * nsq z < 1 := by
    refine (eventually_lt_nhds (lt_min ht1 ht2)).and ?_
    have := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    exact this.eventually (eventually_lt_nhds one_pos)
  obtain ⟨t, hsl1, ⟨htm, htN⟩, htpos⟩ :=
    (ev1.and ((ev2.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin)).exists
  have htpos' : (0 : ℝ) < t := htpos
  have hq := hmem t (by rw [abs_of_pos htpos']; exact htm)
  set q := arc p z t with hqdef
  rw [slope_def_field, hφ0, sub_zero, div_lt_iff₀ htpos'] at hsl1
  have hU := U_le P V lam x ε Λ hε h y q hq
  simp only [g, hbud q hq, sub_zero] at hU
  have hyz : dot q y = dot q (x p) + dot q z := by
    simp only [dot, hzdef, mul_sub, Finset.sum_sub_distrib]
    ring
  have hqz := arc_dot_z p z t hz
  rw [← hqdef] at hqz
  have hden := arc_den z t
  have hqz' : dot q z ≤ -(t * nsq z) := by
    rw [hqz, div_le_iff₀ hden]
    nlinarith [mul_pos htpos' hN]
  have hlam := (h.1 q hq).1
  have hlz : lam q * dot q z ≤ ε * dot q z := by
    have : dot q z ≤ 0 := by nlinarith [mul_pos htpos' hN]
    nlinarith
  have hφt : φ t = V q + lam q * dot q (x p) := rfl
  rw [hyz, mul_add] at hU
  rw [U_at P V lam x ε Λ hε h p hp]
  nlinarith [mul_pos (mul_pos hε htpos') hN, mul_le_mul_of_nonneg_left hqz' hε.le]

/-- **Unique demand for the weight `p_k`.** -/
theorem weight_pk_unique (P : Set (S → ℝ)) (ε β ℓ Λ : ℝ) (hε : 0 < ε) (hℓ : 0 < ℓ)
    (_hβ1 : β < 1) (k : S) (F L : ℝ → ℝ) (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s) (hβ : ∀ q ∈ P, ∀ s, q s ≤ β)
    (hL : ∀ a, ε ≤ a → a ≤ β → ℓ ≤ L a ∧ L a ≤ Λ)
    (hscalar : ∀ a b, ε ≤ a → a ≤ β → ε ≤ b → b ≤ β →
      F b - F a ≤ L a * (b * (a - b * (a * b + Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2))))))
    (hFd : ∀ a, ε ≤ a → a ≤ β → DifferentiableAt ℝ F a)
    (hLd : ∀ a, ε ≤ a → a ≤ β → DifferentiableAt ℝ L a) (hne : P.Nonempty)
    (hrich : ∀ p ∈ P, ∀ z : S → ℝ, dot p z = 0 →
      ∃ t0 > 0, ∀ t, 0 < t → t < t0 → arc p z t ∈ P) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, dot p (fun s => p k * dirk k p s) = 0 ∧
        (∀ y, dot p y ≤ 0 → u y ≤ u (fun s => p k * dirk k p s)) ∧
        ∀ y, dot p y ≤ 0 → y ≠ (fun s => p k * dirk k p s) →
          u y < u (fun s => p k * dirk k p s) := by
  set x : (S → ℝ) → S → ℝ := fun q s => q k * dirk k q s with hx
  have hA := weight_pk_afriat P ε β ℓ Λ hε hℓ k F L hP hpos hβ hL hscalar
  have hε' : 0 < min ε ℓ := lt_min hε hℓ
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    continuum_afriat P (fun q => F (q k)) (fun q => L (q k)) x (min ε ℓ) Λ hε' hA hne
  have hbud : ∀ p ∈ P, dot p (x p) = 0 := by
    intro p hp
    have e : dot p (x p) = p k * dot p (dirk k p) := by
      simp only [hx, dot]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have h1 : dot p p = 1 := by
      rw [← hP p hp]
      unfold dot
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, dot_dirk, h1]
    ring
  refine ⟨U P (fun q => F (q k)) (fun q => L (q k)) x, hc1, hc2, hc3, fun p hp =>
    ⟨hbud p hp, fun y hy => hc5 p hp y (by rw [hbud p hp]; exact hy), fun y hy hyne => ?_⟩⟩
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
    have h1 := hc3 y y' (fun s => by simp only [hy'def]; linarith)
      ⟨k, by simp only [hy'def]; linarith⟩
    have h2 := hc5 p hp y' (by rw [hy', hbud p hp])
    exact h1.trans_le h2
  · have hpk := hpos p hp k
    have hpk1 := hβ p hp k
    have hdiff : DifferentiableAt ℝ (fun t => F ((arc p (fun s => y s - x p s) t) k) +
        L ((arc p (fun s => y s - x p s) t) k) *
          dot (arc p (fun s => y s - x p s) t) (x p)) 0 := by
      set z : S → ℝ := fun s => y s - x p s
      have hk0 : (fun t => arc p z t k) 0 = p k := by simp only [arc_zero]
      have hF : DifferentiableAt ℝ F ((fun t => arc p z t k) 0) := by
        rw [hk0]; exact hFd _ hpk hpk1
      have hL' : DifferentiableAt ℝ L ((fun t => arc p z t k) 0) := by
        rw [hk0]; exact hLd _ hpk hpk1
      have hdot : DifferentiableAt ℝ (fun t => dot (arc p z t) (x p)) 0 := by
        unfold dot
        exact DifferentiableAt.fun_sum fun s _ => (arc_diff p z s).mul_const _
      exact (hF.comp 0 (arc_diff p z k)).add ((hL'.comp 0 (arc_diff p z k)).mul hdot)
    exact afriat_arc_unique P (fun q => F (q k)) (fun q => L (q k)) x (min ε ℓ) Λ hε' hA hbud
      p hp (hP p hp) y heq hyne (hrich p hp) hdiff

end WeightPkUnique

/-! ### The explicit `F K`, `L K` of stage 339 -/

open Real Set

namespace PkExplicit


/-- The integrand `(sin t cos t)² e^{−K t}`. -/
def g (K t : ℝ) : ℝ := (sin t * cos t) ^ 2 * exp (-K * t)

/-- `G K α = ∫₀^α g`. -/
def G (K α : ℝ) : ℝ := ∫ t in (0:ℝ)..α, g K t

/-- The multiplier in angle coordinates. -/
def ell (K α : ℝ) : ℝ := sin α * cos α * exp (-K * α)

theorem g_continuous (K : ℝ) : Continuous (g K) := by
  unfold g; fun_prop

theorem G_hasDerivAt (K α : ℝ) : HasDerivAt (G K) (g K α) α :=
  ((g_continuous K).integral_hasStrictDerivAt 0 α).hasDerivAt

/-- Pointwise sign, `θ ≥ α`. -/
theorem core_pos (K σ α θ : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hα : σ ≤ sin (2 * α))
    (hθ : σ ≤ sin (2 * θ)) (hd0 : 0 ≤ θ - α) (hd1 : θ - α ≤ π / 2) :
    sin (2 * α) ^ 2 ≤ sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) := by
  have hdiff : sin (2 * α) - sin (2 * θ) ≤ 2 * (θ - α) := by
    have h := abs_sin_sub_sin_le (2 * α) (2 * θ)
    have e : |2 * α - 2 * θ| = 2 * (θ - α) := by
      rw [show 2 * α - 2 * θ = -(2 * (θ - α)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hcos : 1 - (θ - α) ^ 2 / 2 ≤ cos (θ - α) := one_sub_sq_div_two_le_cos
  have hsin : 2 / π * (θ - α) ≤ sin (θ - α) := mul_le_sin hd0 hd1
  set d := θ - α with hd
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hsa1 : sa ≤ 1 := sin_le_one _
  have hst1 : st ≤ 1 := sin_le_one _
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hpi3 := pi_gt_three
  have hpi4 := pi_lt_d2
  have hpos := pi_pos
  have h3 : 3 * d ≤ 5 * (2 / π * d) := by
    rw [show 5 * (2 / π * d) = 10 * d / π by ring, le_div_iff₀ hpos]
    nlinarith
  have hdle : d ≤ 2 := by linarith
  have hkσ : 5 * sa ≤ σ * k := by
    have h1 : 7 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk5 : 5 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have hA : sa - 2 * d - d ^ 2 / 2 ≤ st * cos d := by
    have h1 : st * (1 - d ^ 2 / 2) ≤ st * cos d := mul_le_mul_of_nonneg_left hcos hst0
    nlinarith [mul_nonneg (sub_nonneg.mpr hst1) (sq_nonneg d)]
  have hB : 3 * sa * d ≤ st * k * sin d := by
    have h1 : 5 * sa ≤ st * k := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (by linarith : (0:ℝ) ≤ k)]
    have h2 : 0 ≤ 2 / π * d := by positivity
    have h3' : 5 * sa * (2 / π * d) ≤ st * k * sin d :=
      calc 5 * sa * (2 / π * d) ≤ st * k * (2 / π * d) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ st * k * sin d := mul_le_mul_of_nonneg_left hsin (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left h3 hsa0]
  nlinarith [mul_le_mul_of_nonneg_left hA hsa0, mul_nonneg hsa0 (mul_nonneg hd0 (by linarith : (0:ℝ) ≤ 2 - d))]

/-- Pointwise sign, `θ ≤ α`. -/
theorem core_neg (K σ α θ : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hα : σ ≤ sin (2 * α))
    (hθ : σ ≤ sin (2 * θ)) (hd0 : θ - α ≤ 0) (hd1 : -(π / 2) ≤ θ - α) :
    sin (2 * θ) * (sin (2 * α) * cos (θ - α) +
      (K * sin (2 * α) - 2 * cos (2 * α)) * sin (θ - α)) ≤ sin (2 * α) ^ 2 := by
  have hc : cos (θ - α) = cos (α - θ) := by rw [show α - θ = -(θ - α) by ring, cos_neg]
  have hs : sin (θ - α) = - sin (α - θ) := by rw [show α - θ = -(θ - α) by ring, sin_neg, neg_neg]
  rw [hc, hs]
  have he0 : 0 ≤ α - θ := by linarith
  have hdiff : sin (2 * θ) - sin (2 * α) ≤ 2 * (α - θ) := by
    have h := abs_sin_sub_sin_le (2 * θ) (2 * α)
    have e : |2 * θ - 2 * α| = 2 * (α - θ) := by
      rw [show 2 * θ - 2 * α = -(2 * (α - θ)) by ring, abs_neg, abs_of_nonneg (by linarith)]
    rw [e] at h
    exact (abs_le.mp h).2
  have hsin : 2 / π * (α - θ) ≤ sin (α - θ) := mul_le_sin he0 (by linarith)
  have hce : cos (α - θ) ≤ 1 := cos_le_one _
  set e := α - θ with he
  set sa := sin (2 * α) with hsa
  set st := sin (2 * θ) with hst
  set k := K * sa - 2 * cos (2 * α) with hk
  have hca1 : cos (2 * α) ≤ 1 := cos_le_one _
  have hsa0 : 0 ≤ sa := hσ.le.trans hα
  have hst0 : 0 ≤ st := hσ.le.trans hθ
  have hpi4 := pi_lt_d2
  have hpos := pi_pos
  have h3 : 3 * e ≤ 5 * (2 / π * e) := by
    rw [show 5 * (2 / π * e) = 10 * e / π by ring, le_div_iff₀ hpos]
    nlinarith
  have hkσ : 5 * sa ≤ σ * k := by
    have h1 : 7 * sa ≤ K * σ * sa := mul_le_mul_of_nonneg_right hK hsa0
    have h2 : σ * cos (2 * α) ≤ σ := by nlinarith
    rw [hk]; nlinarith
  have hk5 : 5 ≤ k := by
    by_contra h; push Not at h
    nlinarith [mul_pos hσ (sub_pos.mpr h)]
  have h2pe : 0 ≤ 2 / π * e := by positivity
  have hse : 0 ≤ sin e := le_trans h2pe hsin
  have hks : 3 * e ≤ k * sin e := by
    have h1 : 5 * sin e ≤ k * sin e := mul_le_mul_of_nonneg_right hk5 hse
    linarith
  by_cases hX : sa * cos e - k * sin e ≤ 0
  · have : st * (sa * cos e + k * -sin e) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hst0 (by linarith)
    nlinarith [sq_nonneg sa]
  · push Not at hX
    have h1 : st * (sa * cos e - k * sin e) ≤ (sa + 2 * e) * (sa * cos e - k * sin e) :=
      mul_le_mul_of_nonneg_right (by linarith) hX.le
    have h2 : (sa + 2 * e) * (sa * cos e - k * sin e) ≤ (sa + 2 * e) * (sa - k * sin e) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hce hsa0]) (by linarith)
    have h3'' : (sa + 2 * e) * (3 * e) ≤ (sa + 2 * e) * (k * sin e) :=
      mul_le_mul_of_nonneg_left hks (by linarith)
    nlinarith [mul_nonneg hsa0 he0, sq_nonneg e]

/-- The difference whose sign we need, for fixed `θ`. -/
def phi (K θ x : ℝ) : ℝ :=
  sin x * cos x * exp (-K * x) * (sin θ * cos θ) * sin (θ - x) - G K θ + G K x

/-- Its derivative. -/
def phid (K θ x : ℝ) : ℝ :=
  exp (-K * x) / 4 * (sin (2 * x) ^ 2 - sin (2 * θ) * (sin (2 * x) * cos (θ - x) +
      (K * sin (2 * x) - 2 * cos (2 * x)) * sin (θ - x)))

theorem phi_deriv (K θ x : ℝ) : HasDerivAt (phi K θ) (phid K θ x) x := by
  have he : HasDerivAt (fun y => exp (-K * y)) (exp (-K * x) * (-K * 1)) x :=
    ((hasDerivAt_id' x).const_mul (-K)).exp
  have hS : HasDerivAt (fun y => sin (θ - y)) (cos (θ - x) * (0 - 1)) x :=
    ((hasDerivAt_const x θ).sub (hasDerivAt_id' x)).sin
  have h : HasDerivAt (phi K θ) _ x :=
    ((((((hasDerivAt_sin x).mul (hasDerivAt_cos x)).mul he).mul_const
      (sin θ * cos θ)).mul hS).sub_const (G K θ)).add (G_hasDerivAt K x)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold phid g
  rw [sin_two_mul, sin_two_mul, cos_two_mul]
  have hx := sin_sq_add_cos_sq x
  linear_combination (-(sin θ * cos θ) * sin (θ - x) * exp (-K * x)) * hx

theorem phi_self (K θ : ℝ) : phi K θ θ = 0 := by simp [phi]

/-- **The scalar inequality in angle coordinates.** -/
theorem scalar_angle (K σ α0 α1 : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (h0 : 0 ≤ α0)
    (h1 : α1 ≤ π / 2) (hS : ∀ x, α0 ≤ x → x ≤ α1 → σ ≤ sin (2 * x)) (α θ : ℝ)
    (hα0 : α0 ≤ α) (hα1 : α ≤ α1) (hθ0 : α0 ≤ θ) (hθ1 : θ ≤ α1) :
    G K θ - G K α ≤ ell K α * (sin θ * cos θ) * sin (θ - α) := by
  have hcont : Continuous (phi K θ) :=
    continuous_iff_continuousAt.2 fun x => (phi_deriv K θ x).continuousAt
  suffices h : 0 ≤ phi K θ α by unfold phi at h; unfold ell; linarith
  rcases le_total α θ with hle | hle
  · have hanti : AntitoneOn (phi K θ) (Icc α θ) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := phid K θ) (convex_Icc α θ)
        hcont.continuousOn (fun x _ => (phi_deriv K θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_pos K σ x θ hσ hK (hS x (by linarith [hx.1]) (by linarith [hx.2]))
        (hS θ hθ0 hθ1) (by linarith [hx.2]) (by linarith [hx.1])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold phid
      nlinarith
    have := hanti ⟨le_refl α, hle⟩ ⟨hle, le_refl θ⟩ hle
    rw [phi_self] at this; exact this
  · have hmono : MonotoneOn (phi K θ) (Icc θ α) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := phid K θ) (convex_Icc θ α)
        hcont.continuousOn (fun x _ => (phi_deriv K θ x).hasDerivWithinAt)
      intro x hx
      rw [interior_Icc] at hx
      have hcore := core_neg K σ x θ hσ hK (hS x (by linarith [hx.1]) (by linarith [hx.2]))
        (hS θ hθ0 hθ1) (by linarith [hx.1]) (by linarith [hx.2])
      have he : 0 < exp (-K * x) / 4 := by positivity
      unfold phid
      nlinarith
    have := hmono ⟨le_refl θ, hle⟩ ⟨hle, le_refl α⟩ hle
    rw [phi_self] at this; exact this

/-- `F` and `L` in the coordinate `a = q_k = cos α`. -/
def F (K a : ℝ) : ℝ := G K (arccos a)
def L (K a : ℝ) : ℝ := ell K (arccos a)

/-- `sin 2α ≥ σ` on the angle range, from `σ² ≤ 4 a² (1 − a²)` on `[ε, β]`. -/
theorem sin_two_ge (σ ε β : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β) (hβ : β ≤ 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (x : ℝ)
    (hx0 : arccos β ≤ x) (hx1 : x ≤ arccos ε) : σ ≤ sin (2 * x) := by
  have hx0' : 0 ≤ x := (arccos_nonneg β).trans hx0
  have hx1' : x ≤ π / 2 := hx1.trans (arccos_le_pi_div_two.mpr hε)
  have hpos := pi_pos
  have hc1 : cos x ≤ β := by
    have := cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg β) (by linarith) hx0
    rwa [cos_arccos (by linarith) hβ] at this
  have hc0 : ε ≤ cos x := by
    have := cos_le_cos_of_nonneg_of_le_pi hx0' (arccos_le_pi ε) hx1
    rwa [cos_arccos (by linarith) (by linarith)] at this
  have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx0' (by linarith)
  have hy : (2 * sin x * cos x) ^ 2 = 4 * cos x ^ 2 * (1 - cos x ^ 2) := by
    linear_combination (4 * cos x ^ 2) * sin_sq_add_cos_sq x
  have hb := hσa (cos x) hc0 hc1
  rw [← hy] at hb
  have hy0 : 0 ≤ 2 * sin x * cos x := by
    have := hε.trans hc0; positivity
  rw [sin_two_mul]
  by_contra hlt; push Not at hlt
  nlinarith

/-- **Stage 339: the scalar inequality of stage 336, explicitly.** -/
theorem scalar_ab (K σ ε β : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β)
    (hβ : β ≤ 1) (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (a b : ℝ)
    (ha0 : ε ≤ a) (ha1 : a ≤ β) (hb0 : ε ≤ b) (hb1 : b ≤ β) :
    F K b - F K a ≤ L K a * (b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2))))) := by
  have key := scalar_angle K σ (arccos β) (arccos ε) hσ hK (arccos_nonneg _)
    (arccos_le_pi_div_two.mpr hε) (sin_two_ge σ ε β hσ hε hεβ hβ hσa) (arccos a) (arccos b)
    (arccos_le_arccos ha1) (arccos_le_arccos ha0) (arccos_le_arccos hb1) (arccos_le_arccos hb0)
  have hca : cos (arccos a) = a := cos_arccos (by linarith) (by linarith)
  have hcb : cos (arccos b) = b := cos_arccos (by linarith) (by linarith)
  have hsa : sin (arccos a) = √(1 - a ^ 2) := sin_arccos a
  have hsb : sin (arccos b) = √(1 - b ^ 2) := sin_arccos b
  have hid : b * (a - b * (a * b + √((1 - a ^ 2) * (1 - b ^ 2)))) =
      sin (arccos b) * cos (arccos b) * sin (arccos b - arccos a) := by
    rw [sin_sub, hca, hcb, hsa, hsb, Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ 1 - a ^ 2)]
    have hsb2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
    linear_combination (-(a * b)) * hsb2
  rw [hid]
  unfold F L
  linarith [key]

/-- Bounds on `L`, as required by stage 336 (`ℓ ≤ L ≤ Λ`). -/
theorem L_bounds (K σ ε β : ℝ) (hK0 : 0 ≤ K) (hσ : 0 < σ) (hε : 0 ≤ ε) (hεβ : ε ≤ β)
    (hβ : β ≤ 1) (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (a : ℝ)
    (ha0 : ε ≤ a) (ha1 : a ≤ β) :
    σ / 2 * exp (-K * (π / 2)) ≤ L K a ∧ L K a ≤ 1 := by
  have hα0 : 0 ≤ arccos a := arccos_nonneg a
  have hα1 : arccos a ≤ π / 2 := arccos_le_pi_div_two.mpr (by linarith)
  have hpos := pi_pos
  have hs := sin_two_ge σ ε β hσ hε hεβ hβ hσa (arccos a) (arccos_le_arccos ha1)
    (arccos_le_arccos ha0)
  rw [sin_two_mul] at hs
  have hsn : 0 ≤ sin (arccos a) := sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith)
  have hcn : 0 ≤ cos (arccos a) := cos_nonneg_of_mem_Icc ⟨by linarith, hα1⟩
  have hs1 := sin_le_one (arccos a)
  have hc1 := cos_le_one (arccos a)
  have he1 : exp (-K * arccos a) ≤ 1 := by
    rw [← exp_zero]; exact exp_le_exp.mpr (by nlinarith)
  have he2 : exp (-K * (π / 2)) ≤ exp (-K * arccos a) := exp_le_exp.mpr (by nlinarith)
  have hep := exp_pos (-K * (π / 2))
  unfold L ell
  constructor
  · have hsc : σ / 2 ≤ sin (arccos a) * cos (arccos a) := by linarith
    exact mul_le_mul hsc he2 hep.le (mul_nonneg hsn hcn)
  · have hsc : sin (arccos a) * cos (arccos a) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul hsc he1 (exp_pos _).le zero_le_one]

/-- The symmetric range `β² ≤ 1 − ε²` with `σ = 2 ε √(1 − ε²)`. -/
theorem sigma_symmetric (ε β : ℝ) (hε : 0 < ε) (hεβ : ε ≤ β) (hβ : β ^ 2 ≤ 1 - ε ^ 2) :
    0 < 2 * ε * √(1 - ε ^ 2) ∧ β ≤ 1 ∧
      ∀ a, ε ≤ a → a ≤ β → (2 * ε * √(1 - ε ^ 2)) ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2) := by
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have hs : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : √(1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨by positivity, by nlinarith, fun a ha0 ha1 => ?_⟩
  have e : (2 * ε * √(1 - ε ^ 2)) ^ 2 = 4 * ε ^ 2 * (1 - ε ^ 2) := by
    rw [mul_pow, hs2]; ring
  rw [e]
  have h1 : ε ^ 2 ≤ a ^ 2 := by nlinarith
  have h2 : a ^ 2 ≤ 1 - ε ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]


theorem F_diff (K a : ℝ) (h1 : a ≠ -1) (h2 : a ≠ 1) : DifferentiableAt ℝ (F K) a := by
  show DifferentiableAt ℝ (fun a => G K (arccos a)) a
  exact (G_hasDerivAt K (arccos a)).differentiableAt.comp a
    (differentiableAt_arccos.2 ⟨h1, h2⟩)

theorem L_diff (K a : ℝ) (h1 : a ≠ -1) (h2 : a ≠ 1) : DifferentiableAt ℝ (L K) a := by
  show DifferentiableAt ℝ (fun a => ell K (arccos a)) a
  have h : DifferentiableAt ℝ (fun α => sin α * cos α * exp (-K * α)) (arccos a) := by
    fun_prop
  exact h.comp a (differentiableAt_arccos.2 ⟨h1, h2⟩)

/-- **Unique demand for the weight `p_k`, explicit Afriat numbers.** -/
theorem pk_unique_explicit {S : Type*} [Fintype S] [DecidableEq S] (P : Set (S → ℝ))
    (K σ ε β : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hε : 0 < ε) (hεβ : ε ≤ β) (hβ1 : β < 1)
    (hσa : ∀ a, ε ≤ a → a ≤ β → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (k : S)
    (hP : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s)
    (hβ : ∀ q ∈ P, ∀ s, q s ≤ β) (hne : P.Nonempty)
    (hrich : ∀ p ∈ P, ∀ z : S → ℝ, WeightPkUnique.dot p z = 0 →
      ∃ t0 > 0, ∀ t, 0 < t → t < t0 → WeightPkUnique.arc p z t ∈ P) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p ∈ P, WeightPkUnique.dot p (fun s => p k * WeightPkUnique.dirk k p s) = 0 ∧
        (∀ y, WeightPkUnique.dot p y ≤ 0 → u y ≤ u (fun s => p k * WeightPkUnique.dirk k p s)) ∧
        ∀ y, WeightPkUnique.dot p y ≤ 0 → y ≠ (fun s => p k * WeightPkUnique.dirk k p s) →
          u y < u (fun s => p k * WeightPkUnique.dirk k p s) := by
  have hK0 : 0 ≤ K := by
    by_contra hc
    push Not at hc
    nlinarith
  exact WeightPkUnique.weight_pk_unique P ε β (σ / 2 * exp (-K * (π / 2))) 1 hε (by positivity)
    hβ1 k (F K) (L K) hP hpos hβ
    (fun a ha0 ha1 => L_bounds K σ ε β hK0 hσ hε.le hεβ hβ1.le hσa a ha0 ha1)
    (fun a b ha0 ha1 hb0 hb1 => scalar_ab K σ ε β hσ hK hε.le hεβ hβ1.le hσa a b ha0 ha1 hb0 hb1)
    (fun a ha0 ha1 => F_diff K a (by linarith) (by linarith))
    (fun a ha0 ha1 => L_diff K a (by linarith) (by linarith)) hne hrich


open Filter Topology in
/-- The open band `{q unit, ε' < q_s < β'}` is rich. -/
theorem rich_band {S : Type*} [Fintype S] (ε' β' : ℝ) (p : S → ℝ) (hp : ∑ s, p s ^ 2 = 1)
    (hpe : ∀ s, ε' < p s ∧ p s < β') (z : S → ℝ) (hz : WeightPkUnique.dot p z = 0) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      WeightPkUnique.arc p z t ∈
        {q : S → ℝ | ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε' < q s ∧ q s < β'} := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, ε' < WeightPkUnique.arc p z t s ∧
      WeightPkUnique.arc p z t s < β' := by
    rw [eventually_all]
    intro s
    have hc : Continuous fun t : ℝ => WeightPkUnique.arc p z t s := by
      show Continuous fun t : ℝ => ((1 - t ^ 2 * WeightPkUnique.nsq z) * p s - 2 * t * z s) /
        (1 + t ^ 2 * WeightPkUnique.nsq z)
      exact Continuous.div (by fun_prop) (by fun_prop) fun t => (WeightPkUnique.arc_den z t).ne'
    have h0 : WeightPkUnique.arc p z 0 s = p s := by rw [WeightPkUnique.arc_zero]
    have ht := hc.tendsto 0
    rw [h0] at ht
    exact (ht.eventually (eventually_gt_nhds (hpe s).1)).and
      (ht.eventually (eventually_lt_nhds (hpe s).2))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun t ht htd => ⟨WeightPkUnique.arc_unit p z t hp hz, hball ?_⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos ht]
  exact htd

/-- **Boundary prices of the closed cap.**  Rationalise the weight-`p_k` consumer on a slightly
larger open band `ε' < q_s < β'`; the resulting utility has Debreu's trade as its unique
maximiser at every unit price with coordinates in the closed range `[ε, β]`, boundary included. -/
theorem pk_unique_closed_cap {S : Type*} [Fintype S] [DecidableEq S]
    (K σ ε' β' ε β : ℝ) (hσ : 0 < σ) (hK : 7 ≤ K * σ) (hε' : 0 < ε') (hε'ε : ε' < ε)
    (hεβ : ε ≤ β) (hββ' : β < β') (hβ'1 : β' < 1)
    (hσa : ∀ a, ε' ≤ a → a ≤ β' → σ ^ 2 ≤ 4 * a ^ 2 * (1 - a ^ 2)) (k : S)
    (hne : ∃ q : S → ℝ, ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε ≤ q s ∧ q s ≤ β) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ p : S → ℝ, ∑ s, p s ^ 2 = 1 → (∀ s, ε ≤ p s ∧ p s ≤ β) →
        WeightPkUnique.dot p (fun s => p k * WeightPkUnique.dirk k p s) = 0 ∧
        (∀ y, WeightPkUnique.dot p y ≤ 0 →
          u y ≤ u (fun s => p k * WeightPkUnique.dirk k p s)) ∧
        ∀ y, WeightPkUnique.dot p y ≤ 0 → y ≠ (fun s => p k * WeightPkUnique.dirk k p s) →
          u y < u (fun s => p k * WeightPkUnique.dirk k p s) := by
  set P : Set (S → ℝ) := {q | ∑ s, q s ^ 2 = 1 ∧ ∀ s, ε' < q s ∧ q s < β'} with hPdef
  have hsub : ∀ p : S → ℝ, ∑ s, p s ^ 2 = 1 → (∀ s, ε ≤ p s ∧ p s ≤ β) → p ∈ P :=
    fun p hp hb => ⟨hp, fun s => ⟨by linarith [(hb s).1], by linarith [(hb s).2]⟩⟩
  obtain ⟨q0, hq0, hq0b⟩ := hne
  obtain ⟨u, h1, h2, h3, h4⟩ := pk_unique_explicit P K σ ε' β' hσ hK hε' (by linarith) hβ'1 hσa k
    (fun q hq => hq.1) (fun q hq s => (hq.2 s).1.le) (fun q hq s => (hq.2 s).2.le)
    ⟨q0, hsub q0 hq0 hq0b⟩ (fun p hp z hz => rich_band ε' β' p hp.1 hp.2 z hz)
  exact ⟨u, h1, h2, h3, fun p hp hb => h4 p (hsub p hp hb)⟩

end PkExplicit

end

#print axioms WeightPkUnique.g_sub
#print axioms WeightPkUnique.lip_term
#print axioms WeightPkUnique.g_lip
#print axioms WeightPkUnique.g_lower
#print axioms WeightPkUnique.bdd
#print axioms WeightPkUnique.U_le
#print axioms WeightPkUnique.le_U
#print axioms WeightPkUnique.U_lip
#print axioms WeightPkUnique.U_continuous
#print axioms WeightPkUnique.U_concave
#print axioms WeightPkUnique.U_strictMono
#print axioms WeightPkUnique.U_at
#print axioms WeightPkUnique.continuum_afriat
#print axioms WeightPkUnique.dot_le_one
#print axioms WeightPkUnique.dot_dirk
#print axioms WeightPkUnique.debreu_constant_weight
#print axioms WeightPkUnique.cs_bound
#print axioms WeightPkUnique.weight_pk_afriat
#print axioms WeightPkUnique.weight_pk_rationalised
#print axioms WeightPkUnique.nsq_nonneg
#print axioms WeightPkUnique.arc_den
#print axioms WeightPkUnique.arc_dot_p
#print axioms WeightPkUnique.arc_dot_z
#print axioms WeightPkUnique.arc_unit
#print axioms WeightPkUnique.rich_open
#print axioms WeightPkUnique.nsq_neg
#print axioms WeightPkUnique.arc_neg
#print axioms WeightPkUnique.arc_zero
#print axioms WeightPkUnique.arc_diff
#print axioms WeightPkUnique.afriat_arc_unique
#print axioms WeightPkUnique.weight_pk_unique
#print axioms PkExplicit.g_continuous
#print axioms PkExplicit.G_hasDerivAt
#print axioms PkExplicit.core_pos
#print axioms PkExplicit.core_neg
#print axioms PkExplicit.phi_deriv
#print axioms PkExplicit.phi_self
#print axioms PkExplicit.scalar_angle
#print axioms PkExplicit.sin_two_ge
#print axioms PkExplicit.scalar_ab
#print axioms PkExplicit.L_bounds
#print axioms PkExplicit.sigma_symmetric
#print axioms PkExplicit.F_diff
#print axioms PkExplicit.L_diff
#print axioms PkExplicit.pk_unique_explicit
#print axioms PkExplicit.rich_band
#print axioms PkExplicit.pk_unique_closed_cap
