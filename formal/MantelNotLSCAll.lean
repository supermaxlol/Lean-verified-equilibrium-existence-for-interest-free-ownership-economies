import Mathlib

/-!
Stage 328 (extends stage 324): the Mantel utility is not lower semicontinuous on ANY compact
price set, including Debreu's `S_ε`.  It never takes a value strictly between `-2` and `-1`
(`uu_gap`), so continuity plus connectedness of `ℝ^S` is impossible (`not_lsc_compact`,
`mantel_debreu_not_lsc`).

Stage 324 (extends stage 316, reproduced below): on a finite price set the Mantel utility takes
finitely many values and is NOT lower semicontinuous, hence not continuous (`not_lsc`,
`mantel_not_lsc`, `mantel_not_continuous`).  A continuous utility needs a different construction.

Stage 316: the Mantel utility is upper semicontinuous (`uu_usc`, `mantel_usc`), via compactness
of convex hulls of compact sets (`hull_compact`, Carathéodory).

Built on stage 307: the 306 bound comes from compactness, continuity is derived, and the result holds on
Debreu's exact domain `S_ε` (`mantel_compact`, `Seps_compact`, `mantel_debreu`).

Built on stage 306: Mantel/Debreu on a continuum of prices with unique demand.

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

namespace MantelNotLSCAll

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


/-! ### Stage 307: the bound and trade-map continuity come from compactness and continuity of `Z` -/

omit [DecidableEq S] in
/-- **Compactness gives the bound.** -/
theorem bound_of_compact (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hP : IsCompact P)
    (hZ : ContinuousOn Z P) : ∃ B, 0 ≤ B ∧ ∀ p ∈ P, ∀ s, |Z p s| ≤ B := by
  obtain ⟨C, hC⟩ := hP.exists_bound_of_continuousOn hZ
  refine ⟨max C 0, le_max_right _ _, fun p hp s => ?_⟩
  have h1 : ‖Z p s‖ ≤ ‖Z p‖ := norm_le_pi_norm (Z p) s
  rw [Real.norm_eq_abs] at h1
  exact le_trans (le_trans h1 (hC p hp)) (le_max_left _ _)

omit [Fintype S] in
theorem xd_continuousOn (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hZ : ContinuousOn Z P)
    (A : ℝ) (k : S) : ContinuousOn (xd Z A k) P := by
  refine continuousOn_pi.2 fun i => ?_
  show ContinuousOn (fun y => alpha Z A k y * dir k y i) P
  exact (alpha_continuousOn Z P hZ A k).mul
    (continuous_const.sub ((continuous_apply k).mul (continuous_apply i))).continuousOn

omit [DecidableEq S] in
theorem sq_dist_sphere (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) :
    ∑ s, (q s - p s) ^ 2 = 2 - 2 * dot p q := by
  have e : ∀ s, (q s - p s) ^ 2 = q s ^ 2 + p s ^ 2 - 2 * (p s * q s) := fun s => by ring
  simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
  unfold dot; ring

omit [DecidableEq S] in
theorem coord_close (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) (δ : ℝ)
    (hδ : 0 < δ) (h : 1 - δ ^ 2 / 4 < dot p q) (i : S) : |q i - p i| < δ := by
  have h1 : (q i - p i) ^ 2 ≤ ∑ s, (q s - p s) ^ 2 :=
    Finset.single_le_sum (f := fun s => (q s - p s) ^ 2) (fun s _ => sq_nonneg _) (mem_univ i)
  rw [sq_dist_sphere p q hp hq] at h1
  have h2 : (q i - p i) ^ 2 < δ ^ 2 := by nlinarith
  exact abs_lt_of_sq_lt_sq h2 hδ.le

/-- **Continuity of `Z` gives the continuity hypothesis of stage 306.** -/
theorem trade_cont (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hZ : ContinuousOn Z P)
    (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (A : ℝ) (k : S) (p : S → ℝ) (hp : p ∈ P) :
    ∀ d > 0, ∃ ρ > 0, ∀ q ∈ P, 1 - ρ < dot p q →
      ∑ i, |xd Z A k q i - xd Z A k p i| ≤ d := by
  intro d hd
  have hc := xd_continuousOn Z P hZ A k p hp
  have hd' : 0 < d / ((Fintype.card S : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc _ hd'
  refine ⟨δ ^ 2 / 4, by positivity, fun q hq hqd => ?_⟩
  have hdist : dist q p < δ := (dist_pi_lt_iff hδ).2 fun i => by
    rw [Real.dist_eq]; exact coord_close p q (hu p hp) (hu q hq) δ hδ hqd i
  have hx := hδc hq hdist
  have hi : ∀ i, |xd Z A k q i - xd Z A k p i| ≤ d / ((Fintype.card S : ℝ) + 1) := fun i => by
    have := dist_le_pi_dist (xd Z A k q) (xd Z A k p) i
    rw [Real.dist_eq] at this; linarith
  calc ∑ i, |xd Z A k q i - xd Z A k p i| ≤ ∑ _i : S, d / ((Fintype.card S : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = (Fintype.card S : ℝ) * (d / ((Fintype.card S : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ d := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

/-- **Mantel/Debreu with unique demand from continuity alone.**  On a compact price set in `S_ε`,
every continuous `Z` with Walras' law is the aggregate of `|S|` budget-balanced trades, each the
unique maximizer of a monotone quasiconcave utility at every price.  No bound and no separate
continuity hypothesis on the trade maps. -/
theorem mantel_compact (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hP : IsCompact P) (hZ : ContinuousOn Z P) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1)
    (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s) (hW : ∀ p ∈ P, ∑ s, p s * Z p s = 0) :
    ∃ A : ℝ, ∀ p ∈ P, (∀ s, ∑ k, xd Z A k p s = Z p s) ∧ (∀ k, dot p (xd Z A k p) = 0) ∧
      (∀ k y, dot p y ≤ 0 → y ≠ xd Z A k p →
        uu (alpha Z A k) k P y < uu (alpha Z A k) k P (xd Z A k p)) := by
  obtain ⟨B, hB0, hB⟩ := bound_of_compact Z P hP hZ
  exact ⟨B / ε + 1, mantel_unique Z P ε B hε hB0 hu hpos hB hW
    (fun k p hp => trade_cont Z P hZ hu _ k p hp)⟩

/-! ### Debreu's own price domain `S_ε` is compact -/

/-- Debreu's price domain: unit-sphere prices with every coordinate at least `ε`. -/
def Seps (ε : ℝ) : Set (S → ℝ) := {p | ∑ s, p s ^ 2 = 1 ∧ ∀ s, ε ≤ p s}

omit [DecidableEq S] in
theorem Seps_compact (ε : ℝ) : IsCompact (Seps (S := S) ε) := by
  have hset : Seps (S := S) ε =
      {p : S → ℝ | ∑ s, p s ^ 2 = 1} ∩ ⋂ s, {p : S → ℝ | ε ≤ p s} := by
    ext p; simp [Seps]
  have hcl : IsClosed (Seps (S := S) ε) := by
    rw [hset]
    exact (isClosed_eq (continuous_finsetSum _ fun s _ => (continuous_apply s).pow 2)
      continuous_const).inter
        (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s))
  have hbd : Bornology.IsBounded (Seps (S := S) ε) := by
    refine (Metric.isBounded_closedBall (x := (0 : S → ℝ)) (r := 1)).subset fun p hp => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    rw [Real.norm_eq_abs]
    exact coord_abs p hp.1 s
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

/-- **Mantel/Debreu on `S_ε` with unique demand.**  Every continuous `Z` on Debreu's domain with
Walras' law is the aggregate of `|S|` trades, each the unique maximizer of a monotone quasiconcave
utility on its budget at every price. -/
theorem mantel_debreu (Z : (S → ℝ) → S → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hZ : ContinuousOn Z (Seps ε)) (hW : ∀ p ∈ Seps ε, ∑ s, p s * Z p s = 0) :
    ∃ A : ℝ, ∀ p ∈ Seps ε, (∀ s, ∑ k, xd Z A k p s = Z p s) ∧ (∀ k, dot p (xd Z A k p) = 0) ∧
      (∀ k y, dot p y ≤ 0 → y ≠ xd Z A k p →
        uu (alpha Z A k) k (Seps ε) y < uu (alpha Z A k) k (Seps ε) (xd Z A k p)) :=
  mantel_compact Z (Seps ε) ε hε (Seps_compact ε) hZ (fun _ hp => hp.1) (fun _ hp => hp.2) hW


/-! ### Upper semicontinuity of the Mantel utility (stage 316) -/

section Hull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Simplex weights on `Fin n`. -/
def wsimp (n : ℕ) : Set (Fin n → ℝ) := {w | (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

theorem wsimp_compact (n : ℕ) : IsCompact (wsimp n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h : wsimp n = (⋂ j, {w : Fin n → ℝ | 0 ≤ w j}) ∩ {w | ∑ j, w j = 1} := by
      ext w; simp [wsimp]
    rw [h]
    exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset fun w hw => ?_
    have hw' : (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 := hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have h1 : w j ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw'.1 i) (Finset.mem_univ j)
    constructor <;> linarith [hw'.1 j, hw'.2]

theorem sum_emb {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M] (e : ι ↪ κ)
    (g : κ → M) (hg : ∀ j, j ∉ Finset.univ.map e → g j = 0) : ∑ j, g j = ∑ i, g (e i) :=
  calc ∑ j, g j = ∑ j ∈ Finset.univ.map e, g j :=
        (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hg j hj)).symm
    _ = ∑ i, g (e i) := Finset.sum_map _ _ _

/-- **The convex hull of a compact set is compact** (finite dimension, via Carathéodory). -/
theorem hull_compact {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · rw [h, convexHull_empty]; exact isCompact_empty
  let N := Module.finrank ℝ E + 1
  let Φ : (Fin N → ℝ) × (Fin N → E) → E := fun wz => ∑ j, wz.1 j • wz.2 j
  have hΦ : Continuous Φ := continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)
  have hD : IsCompact (wsimp N ×ˢ Set.pi Set.univ (fun _ : Fin N => s)) :=
    (wsimp_compact N).prod (isCompact_univ_pi fun _ => hs)
  have heq : convexHull ℝ s = Φ '' (wsimp N ×ˢ Set.pi Set.univ (fun _ : Fin N => s)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, hι, z, w, hz, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ Fintype.card (Fin N) := by
        rw [Fintype.card_fin]
        exact hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
      let w' : Fin N → ℝ := Function.extend e w 0
      let z' : Fin N → E := Function.extend e z (fun _ => x0)
      have hw'e : ∀ i, w' (e i) = w i := fun i => e.injective.extend_apply _ _ i
      have hz'e : ∀ i, z' (e i) = z i := fun i => e.injective.extend_apply _ _ i
      have hw'n : ∀ j, j ∉ Finset.univ.map e → w' j = 0 := by
        intro j hj
        have hne : ¬∃ i, e i = j := by
          rintro ⟨i, rfl⟩; exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ i))
        show Function.extend e w 0 j = 0
        rw [Function.extend_apply' _ _ _ hne]; rfl
      have hz'mem : ∀ j, z' j ∈ s := by
        intro j
        by_cases h : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := h; rw [hz'e]; exact hz ⟨i, rfl⟩
        · show Function.extend e z (fun _ => x0) j ∈ s
          rw [Function.extend_apply' _ _ _ h]; exact hx0
      refine ⟨(w', z'), ⟨?_, Set.mem_univ_pi.2 fun j => hz'mem j⟩, ?_⟩
      · show (∀ j, 0 ≤ w' j) ∧ ∑ j, w' j = 1
        refine ⟨fun j => ?_, ?_⟩
        · by_cases h : ∃ i, e i = j
          · obtain ⟨i, rfl⟩ := h; rw [hw'e]; exact (hw0 i).le
          · show (0 : ℝ) ≤ Function.extend e w 0 j
            rw [Function.extend_apply' _ _ _ h]; simp
        · rw [sum_emb e w' hw'n]; simp only [hw'e]; exact hw1
      · show ∑ j, w' j • z' j = x
        rw [sum_emb e (fun j => w' j • z' j) (fun j hj => by simp only [hw'n j hj, zero_smul])]
        simp only [hw'e, hz'e]; exact hx
    · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      have hw' : (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 := hw
      exact (convex_convexHull ℝ s).sum_mem (fun j _ => hw'.1 j) hw'.2
        (fun j _ => subset_convexHull ℝ s (Set.mem_univ_pi.1 hz j))
  rw [heq]
  exact hD.image hΦ

end Hull

omit [Fintype S] in
theorem xg_continuousOn (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (ha : ContinuousOn a P) :
    ContinuousOn (xg a k) P :=
  continuousOn_pi.2 fun i => ha.mul
    (continuous_const.sub ((continuous_apply k).mul (continuous_apply i))).continuousOn

omit [Fintype S] in
theorem Aset_compact (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hP : IsCompact P)
    (ha : ContinuousOn a P) (σ : ℝ) : IsCompact (Aset a k P σ) := by
  have h : Aset a k P σ = xg a k '' (P ∩ {q | q k ≤ σ}) := by
    ext z
    constructor
    · rintro ⟨q, hq, hqk, rfl⟩; exact ⟨q, ⟨hq, hqk⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hqk⟩, rfl⟩; exact ⟨q, hq, hqk, rfl⟩
  rw [h]
  exact (hP.inter_right (isClosed_le (continuous_apply k) continuous_const)).image_of_continuousOn
    ((xg_continuousOn a k P ha).mono Set.inter_subset_left)

open Pointwise in
theorem K_closed (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hP : IsCompact P)
    (ha : ContinuousOn a P) (σ : ℝ) : IsClosed (K a k P σ) := by
  have h : K a k P σ = convexHull ℝ (Aset a k P σ) + {r : S → ℝ | ∀ i, 0 ≤ r i} := by
    ext y
    rw [Set.mem_add]
    constructor
    · rintro ⟨z, hz, r, hr, rfl⟩; exact ⟨z, hz, r, hr, rfl⟩
    · rintro ⟨z, hz, r, hr, rfl⟩; exact ⟨z, hz, r, hr, rfl⟩
  rw [h]
  exact IsClosed.add_left_of_isCompact
    (by
      have : {r : S → ℝ | ∀ i, 0 ≤ r i} = ⋂ i, {r : S → ℝ | 0 ≤ r i} := by ext r; simp
      rw [this]; exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    (hull_compact (Aset_compact a k P hP ha σ))

omit [Fintype S] in
theorem lev_iff (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (y : S → ℝ) (τ : ℝ) :
    sInf (lev a k P y) ≤ τ ↔ ∀ δ > 0, τ + δ ∈ lev a k P y := by
  constructor
  · intro h δ hδ
    obtain ⟨s, hs, hlt⟩ := Real.lt_sInf_add_pos (lev_ne a k P y) hδ
    have hle : s ≤ τ + δ := by linarith
    refine ⟨le_trans hs.1 hle, ?_⟩
    rcases hs.2 with h2 | h2
    · exact Or.inl (K_mono a k P hle h2)
    · exact Or.inr (le_trans h2 hle)
  · intro h
    apply le_of_forall_pos_le_add
    intro δ hδ
    exact csInf_le (lev_bdd a k P y) (h δ hδ)

theorem lev_closed (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hP : IsCompact P)
    (ha : ContinuousOn a P) (σ : ℝ) : IsClosed {y | σ ∈ lev a k P y} := by
  by_cases h0 : 0 ≤ σ
  · by_cases h2 : 2 ≤ σ
    · have : {y | σ ∈ lev a k P y} = Set.univ := by
        ext y; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact ⟨h0, Or.inr h2⟩
      rw [this]; exact isClosed_univ
    · have : {y | σ ∈ lev a k P y} = K a k P σ := by
        ext y; simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨_, h | h⟩
          · exact h
          · exact absurd h h2
        · intro h; exact ⟨h0, Or.inl h⟩
      rw [this]; exact K_closed a k P hP ha σ
  · have : {y | σ ∈ lev a k P y} = ∅ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => h0 h.1
    rw [this]; exact isClosed_empty

/-- **The Mantel utility is upper semicontinuous.** -/
theorem uu_usc (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hP : IsCompact P)
    (ha : ContinuousOn a P) : UpperSemicontinuous (uu a k P) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro t
  have h : uu a k P ⁻¹' Set.Ici t = ⋂ δ ∈ Set.Ioi (0 : ℝ), {y | -t + δ ∈ lev a k P y} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_iInter, Set.mem_Ioi, Set.mem_ofPred_eq]
    unfold uu
    rw [← lev_iff]
    constructor <;> intro h <;> linarith
  rw [h]
  exact isClosed_biInter fun δ _ => lev_closed a k P hP ha _

/-- **The utilities of stages 306/307 are upper semicontinuous.** -/
theorem mantel_usc (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hP : IsCompact P)
    (hZ : ContinuousOn Z P) (A : ℝ) (k : S) : UpperSemicontinuous (uu (alpha Z A k) k P) :=
  uu_usc _ k P hP (alpha_continuousOn Z P hZ A k)

/-! ### Stage 324: the Mantel utility is not lower semicontinuous on a finite price set -/

section NotLSC

/-- The levels that can be the infimum: `0`, `2`, and the `k`-th coordinates of prices in `P`. -/
def Tset (k : S) (P : Set (S → ℝ)) : Set ℝ := {0, 2} ∪ (fun q => q k) '' P

omit [Fintype S] [DecidableEq S] in
theorem Tset_finite (k : S) (P : Set (S → ℝ)) (hfin : P.Finite) : (Tset k P).Finite :=
  Set.Finite.union (by simp) (hfin.image _)

omit [Fintype S] in
/-- On a finite price set, the infimum level of every bundle is one of finitely many values. -/
theorem inf_mem_T (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hfin : P.Finite)
    (y : S → ℝ) : sInf (lev a k P y) ∈ Tset k P := by
  generalize hm : sInf (lev a k P y) = m
  by_contra hmT
  have hT : IsClosed (Tset k P) := (Tset_finite k P hfin).isCompact.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT.isOpen_compl m hmT
  have h0 : 0 ≤ m := by rw [← hm]; exact le_csInf (lev_ne a k P y) fun s hs => hs.1
  have h2 : m ≤ 2 := by rw [← hm]; exact csInf_le (lev_bdd a k P y) ⟨by norm_num, Or.inr le_rfl⟩
  have hm0 : m ≠ 0 := fun h => hmT (by rw [h]; unfold Tset; exact Set.mem_union_left _ (by simp))
  have hm2 : m ≠ 2 := fun h => hmT (by rw [h]; unfold Tset; exact Set.mem_union_left _ (by simp))
  have hmpos : 0 < m := lt_of_le_of_ne h0 (Ne.symm hm0)
  have hm2' : m < 2 := lt_of_le_of_ne h2 hm2
  have hmin : 0 < min (min ε m) (2 - m) := lt_min (lt_min hε hmpos) (by linarith)
  have e1 := min_le_left (min ε m) (2 - m)
  have e2 := min_le_right (min ε m) (2 - m)
  have e3 := min_le_left ε m
  have e4 := min_le_right ε m
  set δ := min (min ε m) (2 - m) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδε : δ < ε := by rw [hδ]; linarith
  have hδm : δ < m := by rw [hδ]; linarith
  have hδ2 : m + δ < 2 := by rw [hδ]; linarith
  have hlev : m + δ ∈ lev a k P y := (lev_iff a k P y m).1 (le_of_eq hm) δ hδpos
  rcases hlev.2 with hK | h2'
  · obtain ⟨z, hz, r, hr, e⟩ := hK
    have hsub : Aset a k P (m + δ) ⊆ Aset a k P (m - δ) := by
      rintro w ⟨q, hq, hqk, hw⟩
      refine ⟨q, hq, ?_, hw⟩
      have hqT : q k ∈ Tset k P := by
        unfold Tset; exact Set.mem_union_right _ ⟨q, hq, rfl⟩
      have hnot : q k ∉ Metric.ball m ε := fun hb => hball hb hqT
      rw [Metric.mem_ball, Real.dist_eq, not_lt] at hnot
      rcases le_or_gt (q k) m with h | h
      · rw [abs_of_nonpos (by linarith)] at hnot; linarith
      · rw [abs_of_pos (by linarith)] at hnot; linarith
    have hmem : m - δ ∈ lev a k P y :=
      ⟨by linarith, Or.inl ⟨z, convexHull_mono hsub hz, r, hr, e⟩⟩
    have hc := csInf_le (lev_bdd a k P y) hmem
    rw [hm] at hc
    linarith
  · linarith

omit [Fintype S] in
/-- **Finite range.**  On a finite price set the Mantel utility takes finitely many values. -/
theorem uu_range_finite (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hfin : P.Finite) :
    (Set.range (uu a k P)).Finite := by
  apply ((Tset_finite k P hfin).image (fun t => -t)).subset
  rintro _ ⟨y, rfl⟩
  exact ⟨_, inf_mem_T a k P hfin y, rfl⟩

/-- At a price `p ∈ P` the chosen trade has utility at least `-1`. -/
theorem uu_at_choice (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (p : S → ℝ) (hp : p ∈ P)
    (hu : ∑ s, p s ^ 2 = 1) (hpk : 0 ≤ p k) : -1 ≤ uu a k P (xg a k p) := by
  have hmem : p k ∈ lev a k P (xg a k p) :=
    ⟨hpk, Or.inl ⟨xg a k p, subset_convexHull ℝ _ ⟨p, hp, le_rfl, rfl⟩, 0, fun _ => le_rfl,
      by simp⟩⟩
  have h1 := csInf_le (lev_bdd a k P _) hmem
  have h2 := (abs_le.1 (coord_abs p hu k)).2
  unfold uu
  linarith

/-- A bundle far below every chosen trade has the bottom utility `-2`. -/
theorem uu_far (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (C : ℝ)
    (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (hC : ∀ q ∈ P, |a q| ≤ C) :
    uu a k P (fun _ => -(2 * C) - 1) = -2 := by
  have hlev : ∀ s ∈ lev a k P (fun _ => -(2 * C) - 1), 2 ≤ s := by
    rintro s ⟨_, hK | h2⟩
    · exfalso
      obtain ⟨z, hz, r, hr, e⟩ := hK
      have hconv : Convex ℝ {z : S → ℝ | ∀ i, -(2 * C) ≤ z i} := by
        intro x hx w hw c d hc hd hcd
        show ∀ i, -(2 * C) ≤ c * x i + d * w i
        intro i
        have f1 := mul_le_mul_of_nonneg_left (hx i) hc
        have f2 := mul_le_mul_of_nonneg_left (hw i) hd
        have f3 : c * -(2 * C) + d * -(2 * C) = -(2 * C) := by rw [← add_mul, hcd, one_mul]
        linarith
      have hsub : Aset a k P s ⊆ {z : S → ℝ | ∀ i, -(2 * C) ≤ z i} := by
        rintro w ⟨q, hq, _, rfl⟩
        show ∀ i, -(2 * C) ≤ xg a k q i
        intro i
        have h1 := dir_abs k q (hPs q hq) i
        have h2 := hC q hq
        have h3 : |xg a k q i| ≤ 2 * C := by
          unfold xg
          rw [abs_mul]
          nlinarith [abs_nonneg (a q), abs_nonneg (dir k q i)]
        exact (abs_le.1 h3).1
      have hz' := convexHull_min hsub hconv hz
      have hk := congrFun e k
      simp only [Pi.add_apply] at hk
      have := hz' k
      have := hr k
      linarith
    · exact h2
  have hle : sInf (lev a k P (fun _ => -(2 * C) - 1)) ≤ 2 :=
    csInf_le (lev_bdd a k P _) ⟨by norm_num, Or.inr le_rfl⟩
  have hge : 2 ≤ sInf (lev a k P (fun _ => -(2 * C) - 1)) := le_csInf (lev_ne a k P _) hlev
  unfold uu
  linarith

/-- **Not lower semicontinuous.**  On a finite set of normalised prices with `p k ≥ 0` for some
`p ∈ P`, the Mantel utility is not lower semicontinuous: it is upper semicontinuous (stage 316),
so lower semicontinuity would make it continuous, and a continuous function on the connected space
`ℝ^S` cannot take finitely many values while reaching both `-2` and a value `≥ -1`. -/
theorem not_lsc (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hfin : P.Finite)
    (ha : ContinuousOn a P) (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (p : S → ℝ) (hp : p ∈ P)
    (hpk : 0 ≤ p k) : ¬ LowerSemicontinuous (uu a k P) := by
  intro hl
  have hc : Continuous (uu a k P) :=
    continuous_iff_lower_upperSemicontinuous.2 ⟨hl, uu_usc a k P hfin.isCompact ha⟩
  obtain ⟨C, hC⟩ := (hfin.image fun q => |a q|).bddAbove
  have hC' : ∀ q ∈ P, |a q| ≤ C := fun q hq => hC ⟨q, hq, rfl⟩
  have h1 := uu_far a k P C hPs hC'
  have h2 := uu_at_choice a k P p hp (hPs p hp) hpk
  have hsub : Set.Icc (-2 : ℝ) (uu a k P (xg a k p)) ⊆ Set.range (uu a k P) :=
    (isPreconnected_range hc).Icc_subset ⟨_, h1⟩ ⟨_, rfl⟩
  exact ((Set.Icc_infinite (by linarith)).mono hsub) (uu_range_finite a k P hfin)

/-- **The utilities of stages 306/307/316 are not lower semicontinuous on finite price sets.** -/
theorem mantel_not_lsc (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hfin : P.Finite)
    (hZ : ContinuousOn Z P) (A : ℝ) (k : S) (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, 0 ≤ q s) (hne : P.Nonempty) :
    ¬ LowerSemicontinuous (uu (alpha Z A k) k P) := by
  obtain ⟨p, hp⟩ := hne
  exact not_lsc _ k P hfin (alpha_continuousOn Z P hZ A k) hPs p hp (hpos p hp k)

/-- Hence they are not continuous either. -/
theorem mantel_not_continuous (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hfin : P.Finite)
    (hZ : ContinuousOn Z P) (A : ℝ) (k : S) (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, 0 ≤ q s) (hne : P.Nonempty) :
    ¬ Continuous (uu (alpha Z A k) k P) := fun hc =>
  mantel_not_lsc Z P hfin hZ A k hPs hpos hne hc.lowerSemicontinuous

end NotLSC

/-! ### Stage 328: not lower semicontinuous on any compact price set, including `S_ε` -/

section Gap

/-- Every price on the unit sphere has `k`-th coordinate at most `1`, so level `1` already
contains every chosen trade. -/
theorem K_sub_one (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ))
    (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (s : ℝ) : K a k P s ⊆ K a k P 1 := by
  rintro y ⟨z, hz, r, hr, e⟩
  have hsub : Aset a k P s ⊆ Aset a k P 1 := by
    rintro w ⟨q, hq, _, hw⟩
    exact ⟨q, hq, (abs_le.1 (coord_abs q (hPs q hq) k)).2, hw⟩
  exact ⟨z, convexHull_mono hsub hz, r, hr, e⟩

/-- **The gap.**  The utility never takes a value strictly between `-2` and `-1`. -/
theorem uu_gap (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ))
    (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (y : S → ℝ) :
    uu a k P y = -2 ∨ -1 ≤ uu a k P y := by
  by_cases hy : y ∈ K a k P 1
  · right
    have hmem : (1 : ℝ) ∈ lev a k P y := ⟨zero_le_one, Or.inl hy⟩
    have h1 := csInf_le (lev_bdd a k P y) hmem
    unfold uu
    linarith
  · left
    have hlev : ∀ s ∈ lev a k P y, 2 ≤ s := by
      rintro s ⟨_, hK | h2⟩
      · exact absurd (K_sub_one a k P hPs s hK) hy
      · exact h2
    have hle : sInf (lev a k P y) ≤ 2 :=
      csInf_le (lev_bdd a k P y) ⟨by norm_num, Or.inr le_rfl⟩
    have hge : 2 ≤ sInf (lev a k P y) := le_csInf (lev_ne a k P y) hlev
    unfold uu
    linarith

/-- **Not lower semicontinuous on any compact price set.**  The utility is upper
semicontinuous (stage 316); lower semicontinuity would make it continuous, and a continuous
function on the connected space `ℝ^S` reaching `-2` and a value `≥ -1` would take the value
`-3/2`, which the gap forbids. -/
theorem not_lsc_compact (a : (S → ℝ) → ℝ) (k : S) (P : Set (S → ℝ)) (hP : IsCompact P)
    (ha : ContinuousOn a P) (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1) (p : S → ℝ) (hp : p ∈ P)
    (hpk : 0 ≤ p k) : ¬ LowerSemicontinuous (uu a k P) := by
  intro hl
  have hc : Continuous (uu a k P) :=
    continuous_iff_lower_upperSemicontinuous.2 ⟨hl, uu_usc a k P hP ha⟩
  obtain ⟨C, hC⟩ := (hP.image_of_continuousOn (continuous_abs.comp_continuousOn ha)).bddAbove
  have hC' : ∀ q ∈ P, |a q| ≤ C := fun q hq => hC ⟨q, hq, rfl⟩
  have h1 := uu_far a k P C hPs hC'
  have h2 := uu_at_choice a k P p hp (hPs p hp) hpk
  have hsub : Set.Icc (-2 : ℝ) (uu a k P (xg a k p)) ⊆ Set.range (uu a k P) :=
    (isPreconnected_range hc).Icc_subset ⟨_, h1⟩ ⟨_, rfl⟩
  have hmid : (-3 / 2 : ℝ) ∈ Set.Icc (-2 : ℝ) (uu a k P (xg a k p)) :=
    ⟨by norm_num, by linarith⟩
  obtain ⟨y, hy⟩ := hsub hmid
  rcases uu_gap a k P hPs y with h | h <;> linarith

/-- **The utilities of stages 306/307/316 are not lower semicontinuous on any compact price
set of nonnegative normalised prices.** -/
theorem mantel_not_lsc_compact (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hP : IsCompact P)
    (hZ : ContinuousOn Z P) (A : ℝ) (k : S) (hPs : ∀ q ∈ P, ∑ s, q s ^ 2 = 1)
    (hpos : ∀ q ∈ P, ∀ s, 0 ≤ q s) (hne : P.Nonempty) :
    ¬ LowerSemicontinuous (uu (alpha Z A k) k P) := by
  obtain ⟨p, hp⟩ := hne
  exact not_lsc_compact _ k P hP (alpha_continuousOn Z P hZ A k) hPs p hp (hpos p hp k)

/-- **On Debreu's domain `S_ε`** the utilities are not lower semicontinuous. -/
theorem mantel_debreu_not_lsc (Z : (S → ℝ) → S → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hZ : ContinuousOn Z (Seps ε)) (A : ℝ) (k : S) (hne : (Seps (S := S) ε).Nonempty) :
    ¬ LowerSemicontinuous (uu (alpha Z A k) k (Seps ε)) :=
  mantel_not_lsc_compact Z _ (Seps_compact ε) hZ A k (fun _ hq => hq.1)
    (fun _ hq s => hε.le.trans (hq.2 s)) hne

/-- Hence not continuous either. -/
theorem mantel_debreu_not_continuous (Z : (S → ℝ) → S → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hZ : ContinuousOn Z (Seps ε)) (A : ℝ) (k : S) (hne : (Seps (S := S) ε).Nonempty) :
    ¬ Continuous (uu (alpha Z A k) k (Seps ε)) := fun hc =>
  mantel_debreu_not_lsc Z ε hε hZ A k hne hc.lowerSemicontinuous

end Gap

end MantelNotLSCAll

end

#print axioms MantelNotLSCAll.decomposition
#print axioms MantelNotLSCAll.unique_demand
#print axioms MantelNotLSCAll.K_convex
#print axioms MantelNotLSCAll.uu_mono
#print axioms MantelNotLSCAll.uu_quasiconcave
#print axioms MantelNotLSCAll.mantel_unique
#print axioms MantelNotLSCAll.bound_of_compact
#print axioms MantelNotLSCAll.xd_continuousOn
#print axioms MantelNotLSCAll.trade_cont
#print axioms MantelNotLSCAll.mantel_compact
#print axioms MantelNotLSCAll.Seps_compact
#print axioms MantelNotLSCAll.mantel_debreu
#print axioms MantelNotLSCAll.wsimp_compact
#print axioms MantelNotLSCAll.hull_compact
#print axioms MantelNotLSCAll.Aset_compact
#print axioms MantelNotLSCAll.K_closed
#print axioms MantelNotLSCAll.lev_iff
#print axioms MantelNotLSCAll.lev_closed
#print axioms MantelNotLSCAll.uu_usc
#print axioms MantelNotLSCAll.mantel_usc
#print axioms MantelNotLSCAll.Tset_finite
#print axioms MantelNotLSCAll.inf_mem_T
#print axioms MantelNotLSCAll.uu_range_finite
#print axioms MantelNotLSCAll.uu_at_choice
#print axioms MantelNotLSCAll.uu_far
#print axioms MantelNotLSCAll.not_lsc
#print axioms MantelNotLSCAll.mantel_not_lsc
#print axioms MantelNotLSCAll.mantel_not_continuous
#print axioms MantelNotLSCAll.K_sub_one
#print axioms MantelNotLSCAll.uu_gap
#print axioms MantelNotLSCAll.not_lsc_compact
#print axioms MantelNotLSCAll.mantel_not_lsc_compact
#print axioms MantelNotLSCAll.mantel_debreu_not_lsc
#print axioms MantelNotLSCAll.mantel_debreu_not_continuous
