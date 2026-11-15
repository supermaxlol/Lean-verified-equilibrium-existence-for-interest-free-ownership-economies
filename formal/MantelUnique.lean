import Mathlib

/-!
Stage 306: Mantel/Debreu on a continuum of prices with unique demand.

Same setting as stage 302 (prices on `S_ε`, bounded `Z` with Walras' law, Debreu's
decomposition `x k p = α k p (e_k − p_k p)`).  Here each consumer's preference is built from
convex hulls of choices instead of supporting half-spaces:

  `K s = conv { x k q | q ∈ P, q k ≤ s } + ℝ^S_+`     ("at least as good as level `s`"),
  `u y = −inf { s ≥ 0 | y ∈ K s or s ≥ 2 }`.

* `u` is monotone and quasiconcave.
* For every `p ∈ P`, `x k p` is the **unique** maximizer of `u` on the budget `{y | p·y ≤ 0}`:
  every other affordable bundle is strictly worse.  Uniqueness needs only continuity of the
  trade map `q ↦ x k q` at `p`, used through a tilted separating functional.

So every bounded `Z` with Walras' law on `S_ε` whose trade maps are continuous is exactly
the aggregate demand of `|S|` consumers with monotone convex preferences and single-valued
demand.
-/

noncomputable section

open Finset

namespace MantelUnique

variable {S : Type*} [Fintype S] [DecidableEq S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- Direction of consumer `k`'s trade: `e_k − p_k p`. -/
def dir (k : S) (p : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - p k * p s

/-- Weight on consumer `k`. -/
def alpha (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ) : ℝ := Z p k + A * p k

/-- Consumer `k`'s net trade. -/
def xd (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ) (s : S) : ℝ :=
  alpha Z A k p * dir k p s

theorem dot_dir (k : S) (p q : S → ℝ) : dot q (dir k p) = q k - p k * dot q p := by
  have h : ∑ s, q s * dir k p s = ∑ s, (if s = k then q s else 0) - p k * ∑ s, q s * p s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      unfold dir; split_ifs <;> ring
  unfold dot
  rw [h, Finset.sum_ite_eq' univ k q]
  simp

theorem dot_xd (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p q : S → ℝ) :
    dot q (xd Z A k p) = alpha Z A k p * (q k - p k * dot q p) := by
  rw [← dot_dir]
  unfold dot xd
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
theorem dot_self (p : S → ℝ) : dot p p = ∑ s, p s ^ 2 :=
  Finset.sum_congr rfl fun s _ => by ring

/-- **Each consumer's trade is budget-balanced.** -/
theorem xd_budget (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ)
    (hu : ∑ s, p s ^ 2 = 1) : dot p (xd Z A k p) = 0 := by
  rw [dot_xd, dot_self, hu]; ring

/-- **Decomposition.**  The individual trades add up to `Z p`, for any constant `A`. -/
theorem decomposition (Z : (S → ℝ) → S → ℝ) (A : ℝ) (p : S → ℝ) (hu : ∑ s, p s ^ 2 = 1)
    (hW : ∑ s, p s * Z p s = 0) (s : S) : ∑ k, xd Z A k p s = Z p s := by
  have h1 : ∑ k, xd Z A k p s =
      ∑ k, (if s = k then alpha Z A k p else 0) - p s * ∑ k, (p k * Z p k + A * p k ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      unfold xd dir alpha; split_ifs <;> ring
  rw [h1, Finset.sum_ite_eq univ s (fun k => alpha Z A k p), Finset.sum_add_distrib,
    ← Finset.mul_sum, hW, hu]
  simp [alpha]
  ring

omit [Fintype S] [DecidableEq S] in
/-- **Positive weights** once `A` is large. -/
theorem alpha_pos (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s) (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B)
    (k : S) (p : S → ℝ) (hp : p ∈ P) : 0 < alpha Z (B / ε + 1) k p := by
  have hA : 0 ≤ B / ε + 1 := by positivity
  have e : (B / ε + 1) * ε = B + ε := by rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul]
  have h1 : (B / ε + 1) * ε ≤ (B / ε + 1) * p k := mul_le_mul_of_nonneg_left (hpos p hp k) hA
  have h2 : -B ≤ Z p k := (abs_le.1 (hB p hp k)).1
  unfold alpha
  linarith

omit [Fintype S] [DecidableEq S] in
theorem alpha_continuousOn (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hZ : ContinuousOn Z P)
    (A : ℝ) (k : S) : ContinuousOn (alpha Z A k) P :=
  ((continuous_apply k).comp_continuousOn hZ).add
    (continuousOn_const.mul (continuous_apply k).continuousOn)

omit [DecidableEq S] in
theorem dot_lt_one (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1)
    (hne : p ≠ q) : dot q p < 1 := by
  obtain ⟨s, hs⟩ : ∃ s, p s ≠ q s := by
    by_contra h
    exact hne (funext fun s => not_not.1 fun h' => h ⟨s, h'⟩)
  have hpos : 0 < ∑ s, (p s - q s) ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨s, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hs)))⟩
  have e : ∑ s, (p s - q s) ^ 2 = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
    unfold dot
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

/-- **Strict revealed preference.**  If consumer `k`'s choice at `p` is affordable at a
different price `q`, then good `k` is strictly cheaper at `q`. -/
theorem revealed_strict (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p q : S → ℝ)
    (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) (hne : p ≠ q) (hα : 0 < alpha Z A k p)
    (hpk : 0 < p k) (haff : dot q (xd Z A k p) ≤ 0) : q k < p k := by
  rw [dot_xd] at haff
  have h1 : q k - p k * dot q p ≤ 0 := by
    by_contra h
    exact absurd haff (not_le.2 (mul_pos hα (lt_of_not_ge h)))
  have h2 := dot_lt_one p q hp hq hne
  nlinarith


/-! ### Generic trade map `x q = a q • (e_k − q_k q)` and its convex-hull preference -/

/-- Trade of consumer `k` at price `q` with weight `a`. -/
def xg (a : (S → ℝ) → ℝ) (k : S) (q : S → ℝ) (i : S) : ℝ := a q * dir k q i

theorem dot_xg (a : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) :
    dot p (xg a k q) = a q * (p k - q k * dot p q) := by
  rw [← dot_dir]
  unfold dot xg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
theorem dot_le_one (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) :
    dot p q ≤ 1 := by
  by_cases e : q = p
  · rw [e, dot_self, hp]
  · exact (dot_lt_one q p hq hp e).le

omit [DecidableEq S] in
theorem coord_abs (q : S → ℝ) (hq : ∑ s, q s ^ 2 = 1) (i : S) : |q i| ≤ 1 := by
  have h : q i ^ 2 ≤ ∑ s, q s ^ 2 :=
    Finset.single_le_sum (f := fun s => q s ^ 2) (fun s _ => sq_nonneg _) (mem_univ i)
  rw [hq] at h
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem dir_abs (k : S) (q : S → ℝ) (hq : ∑ s, q s ^ 2 = 1) (i : S) : |dir k q i| ≤ 2 := by
  have h1 : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have h2 : |q k * q i| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (q k), abs_nonneg (q i), coord_abs q hq k, coord_abs q hq i]
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  unfold dir
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem xg_abs (a : (S → ℝ) → ℝ) (k : S) (q : S → ℝ) (hq : ∑ s, q s ^ 2 = 1) (M : ℝ)
    (ha0 : 0 ≤ a q) (haM : a q ≤ M) (i : S) : |xg a k q i| ≤ 2 * M := by
  unfold xg
  rw [abs_mul, abs_of_nonneg ha0]
  have := dir_abs k q hq i
  nlinarith [abs_nonneg (dir k q i)]

omit [DecidableEq S] in
theorem halfspace_convex (g : S → ℝ) (m : ℝ) : Convex ℝ {z : S → ℝ | m ≤ dot g z} := by
  intro x hx z hz α β hα hβ hαβ
  have e : dot g (α • x + β • z) = α * dot g x + β * dot g z := by
    unfold dot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  show m ≤ dot g (α • x + β • z)
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left (show m ≤ dot g x from hx) hα
  have h2 := mul_le_mul_of_nonneg_left (show m ≤ dot g z from hz) hβ
  have h3 : m = α * m + β * m := by rw [← add_mul, hαβ, one_mul]
  linarith

omit [DecidableEq S] in
theorem dot_add (g z r : S → ℝ) : dot g (z + r) = dot g z + dot g r := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring

omit [DecidableEq S] in
theorem dot_w_diff (w u v : S → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    -(∑ i, |u i - v i|) ≤ dot w u - dot w v := by
  have h : dot w u - dot w v = ∑ i, w i * (u i - v i) := by
    unfold dot; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := neg_abs_le (w i * (u i - v i))
  rw [abs_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right (hw i) (abs_nonneg (u i - v i))
  linarith

/-- Choices at prices whose `k`-th coordinate is at most `s`. -/
def Aset (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (s : ℝ) : Set (S → ℝ) :=
  {z | ∃ q ∈ P, q k ≤ s ∧ z = xg a k q}

/-- "At least as good as level `s`": convex hull of those choices plus free disposal. -/
def K (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (s : ℝ) : Set (S → ℝ) :=
  {y | ∃ z ∈ convexHull ℝ (Aset a k P s), ∃ r : S → ℝ, (∀ i, 0 ≤ r i) ∧ y = z + r}

/-- Levels reached by `y` (level `2` and above reach everything). -/
def lev (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y : S → ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ (y ∈ K a k P s ∨ 2 ≤ s)}

/-- Consumer `k`'s utility. -/
def uu (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y : S → ℝ) : ℝ := -sInf (lev a k P y)

omit [Fintype S] in
theorem K_mono (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) {s s' : ℝ} (h : s ≤ s') :
    K a k P s ⊆ K a k P s' := by
  rintro y ⟨z, hz, r, hr, e⟩
  have hsub : Aset a k P s ⊆ Aset a k P s' := by
    rintro w ⟨q, hq, hqk, hw⟩
    exact ⟨q, hq, le_trans hqk h, hw⟩
  exact ⟨z, convexHull_mono hsub hz, r, hr, e⟩

omit [Fintype S] in
theorem lev_ne (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y : S → ℝ) :
    (lev a k P y).Nonempty := ⟨2, by norm_num, Or.inr le_rfl⟩

omit [Fintype S] in
theorem lev_bdd (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y : S → ℝ) :
    BddBelow (lev a k P y) := ⟨0, fun _ hs => hs.1⟩

/-- **Unique demand.**  Every affordable bundle other than `x k p` is strictly worse. -/
theorem unique_demand (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (ε a0 M : ℝ) (hε : 0 < ε)
    (ha0 : 0 < a0) (hu : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hpos : ∀ q ∈ P, ∀ s, ε ≤ q s)
    (ha : ∀ q ∈ P, a0 ≤ a q ∧ a q ≤ M) (p : S → ℝ) (hp : p ∈ P)
    (hcont : ∀ d > 0, ∃ ρ > 0, ∀ q ∈ P, 1 - ρ < dot p q →
      ∑ i, |xg a k q i - xg a k p i| ≤ d)
    (y : S → ℝ) (hy : dot p y ≤ 0) (hne : y ≠ xg a k p) :
    uu a k P y < uu a k P (xg a k p) := by
  have hM : 0 < M := lt_of_lt_of_le ha0 ((ha p hp).1.trans (ha p hp).2)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ xg a k p j := by
    by_contra h
    exact hne (funext fun j => not_not.1 fun h' => h ⟨j, h'⟩)
  have hd : 0 < ∑ i, |y i - xg a k p i| :=
    Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨j, mem_univ _, abs_pos.2 (sub_ne_zero.2 hj)⟩
  obtain ⟨ρ0, hρ0, hc⟩ := hcont ((∑ i, |y i - xg a k p i|) / 4) (by positivity)
  have hρ : 0 < min ρ0 1 := lt_min hρ0 one_pos
  have hρ1 : min ρ0 1 ≤ 1 := min_le_right _ _
  have hρρ0 : min ρ0 1 ≤ ρ0 := min_le_left _ _
  have hDb : ∀ q ∈ P, ∑ i, |xg a k q i - xg a k p i| ≤ 4 * M * (Fintype.card S : ℝ) := by
    intro q hq
    have hb : ∀ i, |xg a k q i - xg a k p i| ≤ 4 * M := fun i => by
      obtain ⟨u1, u2⟩ := abs_le.1 (xg_abs a k q (hu q hq) M (ha0.le.trans (ha q hq).1) (ha q hq).2 i)
      obtain ⟨v1, v2⟩ := abs_le.1 (xg_abs a k p (hu p hp) M (ha0.le.trans (ha p hp).1) (ha p hp).2 i)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    calc ∑ i, |xg a k q i - xg a k p i| ≤ ∑ _i : S, 4 * M := Finset.sum_le_sum fun i _ => hb i
      _ = 4 * M * (Fintype.card S : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hD0 : 0 ≤ 4 * M * (Fintype.card S : ℝ) := by positivity
  set d := ∑ i, |y i - xg a k p i| with hd_def
  set ρ := min ρ0 1 with hρ_def
  set D := 4 * M * (Fintype.card S : ℝ) with hD_def
  set δ := min ε (a0 * ε * ρ / (2 * (D + 1))) with hδ_def
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hX : 0 < a0 * ε * ρ := by positivity
  have hδD : δ * D ≤ a0 * ε * ρ / 2 := by
    calc δ * D ≤ a0 * ε * ρ / (2 * (D + 1)) * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hD0
      _ ≤ a0 * ε * ρ / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  set η := min (ε * ρ / 2) (min 1 (δ * d / (4 * M))) with hη_def
  have hη : 0 < η := lt_min (by positivity) (lt_min one_pos (by positivity))
  have hηρ : η ≤ ε * ρ / 2 := min_le_left _ _
  have hη1 : η ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηM : M * η ≤ δ * d / 4 := by
    have h : η ≤ δ * d / (4 * M) := by
      rw [hη_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * M)).1 h
    nlinarith
  -- tilted functional
  set w : S → ℝ := fun i => if 0 ≤ y i - xg a k p i then -1 else 1 with hw_def
  have hw : ∀ i, |w i| ≤ 1 := fun i => by simp only [hw_def]; split_ifs <;> simp
  have hwy : dot w y - dot w (xg a k p) = -d := by
    have h : dot w y - dot w (xg a k p) = ∑ i, w i * (y i - xg a k p i) := by
      unfold dot; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, hd_def, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hw_def]
    split_ifs with hi
    · rw [abs_of_nonneg hi]; ring
    · rw [abs_of_neg (lt_of_not_ge hi)]; ring
  set g : S → ℝ := fun i => p i + δ * w i with hg_def
  have hg : ∀ z, dot g z = dot p z + δ * dot w z := fun z => by
    unfold dot; rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [hg_def]; ring
  set m := δ * dot w (xg a k p) - δ * d / 2 with hm_def
  have hA : Aset a k P (p k + η) ⊆ {z | m ≤ dot g z} := by
    rintro z ⟨q, hq, hqk, rfl⟩
    show m ≤ dot g (xg a k q)
    rw [hg, dot_xg]
    have hwq := dot_w_diff w (xg a k q) (xg a k p) hw
    have ht1 := dot_le_one p q (hu p hp) (hu q hq)
    have hqk0 : 0 < q k := lt_of_lt_of_le hε (hpos q hq k)
    have hpk : ε ≤ p k := hpos p hp k
    obtain ⟨haq0, haqM⟩ := ha q hq
    by_cases hnear : 1 - ρ < dot p q
    · have hcq := hc q hq (by linarith)
      have hX1 : -η ≤ p k - q k * dot p q := by
        have := mul_le_mul_of_nonneg_left ht1 hqk0.le
        linarith
      have k1 := mul_nonneg (ha0.le.trans haq0) (show 0 ≤ p k - q k * dot p q + η by linarith)
      have k2 := mul_nonneg (show 0 ≤ M - a q by linarith) hη.le
      have k3 := mul_le_mul_of_nonneg_left
        (show dot w (xg a k p) - d / 4 ≤ dot w (xg a k q) by linarith) hδ.le
      nlinarith
    · have hfar : dot p q ≤ 1 - ρ := not_lt.1 hnear
      have f1 := mul_le_mul_of_nonneg_left hfar hqk0.le
      have f2 := mul_le_mul_of_nonneg_right hqk (show 0 ≤ 1 - ρ by linarith)
      have f3 := mul_le_mul_of_nonneg_right hpk hρ.le
      have f4 : η * (1 - ρ) ≤ η := by nlinarith
      have hXf : ε * ρ / 2 ≤ p k - q k * dot p q := by nlinarith
      have f5 := mul_le_mul haq0 hXf (by positivity) (ha0.le.trans haq0)
      have f6 := mul_le_mul_of_nonneg_left
        (show dot w (xg a k p) - D ≤ dot w (xg a k q) by linarith [hDb q hq]) hδ.le
      have f7 : 0 < δ * d := mul_pos hδ hd
      nlinarith
  have hhull : convexHull ℝ (Aset a k P (p k + η)) ⊆ {z | m ≤ dot g z} :=
    convexHull_min hA (halfspace_convex g m)
  have hnotK : y ∉ K a k P (p k + η) := by
    rintro ⟨z, hz, r, hr, e⟩
    have h1 : m ≤ dot g z := hhull hz
    have h2 : 0 ≤ dot g r := Finset.sum_nonneg fun i _ => by
      have := (abs_le.1 (hw i)).1
      have h3 : 0 ≤ p i + δ * w i := by nlinarith [hpos p hp i]
      exact mul_nonneg h3 (hr i)
    have h4 : dot g y = dot g z + dot g r := by rw [e, dot_add]
    have h5 : dot g y = dot p y + δ * dot w y := hg y
    have h6 : δ * dot w y = δ * dot w (xg a k p) - δ * d := by
      rw [show dot w y = dot w (xg a k p) - d by linarith]; ring
    have f7 : 0 < δ * d := mul_pos hδ hd
    linarith
  have hpk1 : p k ≤ 1 := (abs_le.1 (coord_abs p (hu p hp) k)).2
  have hlow : p k + η ≤ sInf (lev a k P y) := by
    refine le_csInf (lev_ne a k P y) fun s ⟨_, hs⟩ => ?_
    rcases hs with hs | hs
    · by_contra h
      exact hnotK (K_mono a k P (not_le.1 h).le hs)
    · linarith
  have hup : sInf (lev a k P (xg a k p)) ≤ p k := by
    refine csInf_le (lev_bdd a k P _) ⟨(lt_of_lt_of_le hε (hpos p hp k)).le, Or.inl ?_⟩
    exact ⟨xg a k p, subset_convexHull ℝ _ ⟨p, hp, le_rfl, rfl⟩, 0, fun _ => le_rfl,
      (add_zero _).symm⟩
  unfold uu
  linarith

omit [Fintype S] in
/-- `K` is convex. -/
theorem K_convex (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (s : ℝ) :
    Convex ℝ (K a k P s) := by
  rintro y1 ⟨z1, hz1, r1, hr1, e1⟩ y2 ⟨z2, hz2, r2, hr2, e2⟩ α β hα hβ hαβ
  refine ⟨α • z1 + β • z2, convex_convexHull ℝ _ hz1 hz2 hα hβ hαβ, α • r1 + β • r2,
    fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα (hr1 i)) (mul_nonneg hβ (hr2 i))
  · rw [e1, e2]; funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

omit [Fintype S] in
/-- **Monotone.** -/
theorem uu_mono (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y y' : S → ℝ)
    (h : ∀ i, y i ≤ y' i) : uu a k P y ≤ uu a k P y' := by
  unfold uu
  rw [neg_le_neg_iff]
  refine csInf_le_csInf (lev_bdd a k P y') (lev_ne a k P y) fun s ⟨hs0, hs⟩ => ⟨hs0, ?_⟩
  rcases hs with ⟨z, hz, r, hr, e⟩ | hs
  · refine Or.inl ⟨z, hz, r + (y' - y), fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply]; linarith [hr i, h i]
    · rw [← add_assoc, ← e]; abel
  · exact Or.inr hs

omit [Fintype S] in
/-- **Quasiconcave.** -/
theorem uu_quasiconcave (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y1 y2 : S → ℝ)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    min (uu a k P y1) (uu a k P y2) ≤ uu a k P (α • y1 + β • y2) := by
  have key : sInf (lev a k P (α • y1 + β • y2)) ≤
      max (sInf (lev a k P y1)) (sInf (lev a k P y2)) := by
    refine le_of_forall_pos_lt_add fun e he => ?_
    obtain ⟨s1, hs1, hs1'⟩ := exists_lt_of_csInf_lt (lev_ne a k P y1)
      (show sInf (lev a k P y1) < max (sInf (lev a k P y1)) (sInf (lev a k P y2)) + e by
        linarith [le_max_left (sInf (lev a k P y1)) (sInf (lev a k P y2))])
    obtain ⟨s2, hs2, hs2'⟩ := exists_lt_of_csInf_lt (lev_ne a k P y2)
      (show sInf (lev a k P y2) < max (sInf (lev a k P y1)) (sInf (lev a k P y2)) + e by
        linarith [le_max_right (sInf (lev a k P y1)) (sInf (lev a k P y2))])
    have hmem : max s1 s2 ∈ lev a k P (α • y1 + β • y2) := by
      refine ⟨le_trans hs1.1 (le_max_left _ _), ?_⟩
      rcases hs1.2 with h1 | h1
      · rcases hs2.2 with h2 | h2
        · exact Or.inl (K_convex a k P _ (K_mono a k P (le_max_left _ _) h1)
            (K_mono a k P (le_max_right _ _) h2) hα hβ hαβ)
        · exact Or.inr (le_trans h2 (le_max_right _ _))
      · exact Or.inr (le_trans h1 (le_max_left _ _))
    exact lt_of_le_of_lt (csInf_le (lev_bdd a k P _) hmem) (max_lt hs1' hs2')
  unfold uu
  rw [min_le_iff]
  rcases le_total (sInf (lev a k P y1)) (sInf (lev a k P y2)) with h | h
  · right; rw [max_eq_right h] at key; linarith
  · left; rw [max_eq_left h] at key; linarith

/-- **Mantel/Debreu with unique demand on `S_ε`.**  Every bounded `Z` with Walras' law whose
trade maps are continuous is the aggregate of `|S|` budget-balanced trades, each the unique
maximizer of a monotone quasiconcave utility at every price in the continuum. -/
theorem mantel_unique (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s)
    (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B) (hW : ∀ p ∈ P, ∑ s, p s * Z p s = 0)
    (hcont : ∀ k, ∀ p ∈ P, ∀ d > 0, ∃ ρ > 0, ∀ q ∈ P, 1 - ρ < dot p q →
      ∑ i, |xd Z (B / ε + 1) k q i - xd Z (B / ε + 1) k p i| ≤ d) :
    ∀ p ∈ P, (∀ s, ∑ k, xd Z (B / ε + 1) k p s = Z p s) ∧
      (∀ k, dot p (xd Z (B / ε + 1) k p) = 0) ∧
      (∀ k y, dot p y ≤ 0 → y ≠ xd Z (B / ε + 1) k p →
        uu (alpha Z (B / ε + 1) k) k P y < uu (alpha Z (B / ε + 1) k) k P
          (xd Z (B / ε + 1) k p)) := by
  intro p hp
  refine ⟨decomposition Z _ p (hu p hp) (hW p hp), fun k => xd_budget Z _ k p (hu p hp),
    fun k y hy hne => ?_⟩
  have hA : 0 ≤ B / ε + 1 := by positivity
  have ha : ∀ q ∈ P, ε ≤ alpha Z (B / ε + 1) k q ∧ alpha Z (B / ε + 1) k q ≤ B + (B / ε + 1) :=
    fun q hq => by
      have e : (B / ε + 1) * ε = B + ε := by rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul]
      have h1 : (B / ε + 1) * ε ≤ (B / ε + 1) * q k := mul_le_mul_of_nonneg_left (hpos q hq k) hA
      have h2 : (B / ε + 1) * q k ≤ (B / ε + 1) * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.1 (coord_abs q (hu q hq) k)).2 hA
      obtain ⟨z1, z2⟩ := abs_le.1 (hB q hq k)
      unfold alpha
      constructor <;> linarith
  exact unique_demand (alpha Z (B / ε + 1) k) k P ε ε (B + (B / ε + 1)) hε hε hu hpos ha p hp
    (hcont k p hp) y hy hne

end MantelUnique

end

#print axioms MantelUnique.decomposition
#print axioms MantelUnique.unique_demand
#print axioms MantelUnique.K_convex
#print axioms MantelUnique.uu_mono
#print axioms MantelUnique.uu_quasiconcave
#print axioms MantelUnique.mantel_unique
