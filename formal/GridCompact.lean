import Mathlib

/-!
# Stage 349: the compactness step of the grid route

Stage 343 (`GridLimit`) took a sequence of grid economies and assumed the grid utilities
converge.  This file proves the compactness step that supplies a limit, under explicit
uniform bounds:

* `lipSet_compact` (Arzelà–Ascoli): in `C(X, ℝ)` with the compact-open topology, the set of
  `M`-Lipschitz functions with `|f x₀| ≤ B` is compact.  No compactness of `X` is needed.
* `mem_of_cluster`: every closed property that holds eventually along the sequence also holds
  at each cluster point.  Concavity (`concaveSet_closed`) and a uniform monotone modulus
  (`modulusSet_closed`) are closed, so they pass to the limit.
* `grid_cluster`: if `u n` rationalises a continuous trade map `x` on grids `G n ⊆ P` that
  become dense in `P`, and all `u n` lie in one Lipschitz set, then some cluster point `U`
  rationalises `x` on all of `P`: `p · y ≤ 0 → U y ≤ U (x p)`.

What is assumed and NOT proved here: the uniform Lipschitz constant and the uniform bound for
the grid utilities.  Uniqueness of the maximiser does not pass to the limit, and strict
monotonicity passes only through a uniform modulus.  The cluster point is a limit along a
subnet (a cluster point of the sequence), not necessarily of a subsequence.
-/

namespace GridCompact

open Filter Topology Set

section Lip

variable {X : Type*} [PseudoMetricSpace X]

/-- `M`-Lipschitz functions with `|f x₀| ≤ B`. -/
def LipSet (x0 : X) (M B : ℝ) : Set C(X, ℝ) :=
  {f | (∀ a b, dist (f a) (f b) ≤ M * dist a b) ∧ |f x0| ≤ B}

theorem lip_small {M d ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hd0 : 0 ≤ d) (hd : d < ε / (M + 1)) :
    M * d < ε := by
  have hM1 : 0 < M + 1 := by linarith
  have hq : 0 < ε / (M + 1) := div_pos hε hM1
  have h1 : (M + 1) * (ε / (M + 1)) = ε := by field_simp
  have h2 : M * d ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hd.le hM
  nlinarith

/-- The pointwise image of the Lipschitz set. -/
def LipFun (x0 : X) (M B : ℝ) : Set (X → ℝ) :=
  {g | (∀ a b, dist (g a) (g b) ≤ M * dist a b) ∧ |g x0| ≤ B}

theorem lipFun_closed (x0 : X) (M B : ℝ) : IsClosed (LipFun x0 M B) := by
  unfold LipFun
  rw [Set.ofPred_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ((continuous_apply a).dist (continuous_apply b)) continuous_const
  · exact isClosed_le (continuous_abs.comp (continuous_apply x0)) continuous_const

theorem lipFun_sub_pi (x0 : X) (M B : ℝ) :
    LipFun x0 M B ⊆ Set.pi Set.univ (fun a => Set.Icc (-(B + M * dist a x0)) (B + M * dist a x0)) := by
  intro g hg a _
  obtain ⟨hL, hB⟩ := hg
  have h1 := hL a x0
  rw [Real.dist_eq] at h1
  have h2 : |g a| ≤ B + M * dist a x0 := by
    have := abs_sub_abs_le_abs_sub (g a) (g x0)
    linarith
  exact ⟨by linarith [neg_abs_le (g a)], by linarith [le_abs_self (g a)]⟩

theorem lipFun_compact (x0 : X) (M B : ℝ) : IsCompact (LipFun x0 M B) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (lipFun_closed x0 M B)
    (lipFun_sub_pi x0 M B)

theorem lip_continuous {M : ℝ} (hM : 0 ≤ M) {g : X → ℝ}
    (hg : ∀ a b, dist (g a) (g b) ≤ M * dist a b) : Continuous g := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (M + 1), div_pos hε (by linarith), fun a ha => ?_⟩
  exact (hg a b).trans_lt (lip_small hM hε dist_nonneg ha)

theorem image_lipSet (x0 : X) (M B : ℝ) (hM : 0 ≤ M) :
    ContinuousMap.toFun '' LipSet x0 M B = LipFun x0 M B := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro hg
    exact ⟨⟨g, lip_continuous hM hg.1⟩, hg, rfl⟩

/-- **Arzelà–Ascoli for a Lipschitz ball.** -/
theorem lipSet_compact (x0 : X) (M B : ℝ) (hM : 0 ≤ M) : IsCompact (LipSet x0 M B) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [image_lipSet x0 M B hM]
    exact lipFun_compact x0 M B
  · intro z
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε / (M + 1), div_pos hε (by linarith), fun w hw f => ?_⟩
    have h := f.2.1 z w
    rw [dist_comm z w] at h
    exact h.trans_lt (lip_small hM hε dist_nonneg hw)

end Lip

section Cluster

variable {Y : Type*} [TopologicalSpace Y]

/-- A closed property that holds eventually along `u` holds at every cluster point. -/
theorem mem_of_cluster {C : Set Y} (hC : IsClosed C) {u : ℕ → Y} {U : Y}
    (hU : MapClusterPt U atTop u) (hu : ∀ᶠ n in atTop, u n ∈ C) : U ∈ C := by
  by_contra h
  have hf := (mapClusterPt_iff_frequently.1 hU) Cᶜ (hC.isOpen_compl.mem_nhds h)
  obtain ⟨n, h1, h2⟩ := (hf.and_eventually hu).exists
  exact h1 h2

end Cluster

section Goods

variable {S : Type*} [Fintype S]

/-- Value of a bundle. -/
def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- Concave functions on the goods space. -/
def ConcaveSet : Set C(S → ℝ, ℝ) :=
  {f | ∀ a b : S → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    t * f a + (1 - t) * f b ≤ f (t • a + (1 - t) • b)}

omit [Fintype S] in
theorem concaveSet_closed : IsClosed (ConcaveSet (S := S)) := by
  unfold ConcaveSet
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le ((continuous_const.mul (continuous_eval_const a)).add
        (continuous_const.mul (continuous_eval_const b))) (continuous_eval_const _)

/-- A uniform monotone modulus `m`: `a ≤ b` coordinatewise gives `f a + m a b ≤ f b`. -/
def ModulusSet (m : (S → ℝ) → (S → ℝ) → ℝ) : Set C(S → ℝ, ℝ) :=
  {f | ∀ a b : S → ℝ, (∀ s, a s ≤ b s) → f a + m a b ≤ f b}

omit [Fintype S] in
theorem modulusSet_closed (m : (S → ℝ) → (S → ℝ) → ℝ) : IsClosed (ModulusSet m) := by
  unfold ModulusSet
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_le ((continuous_eval_const a).add continuous_const) (continuous_eval_const b)

theorem dot_sub_le (p q y : S → ℝ) : dot q y - dot p y ≤ dist q p * ∑ s, |y s| := by
  unfold dot
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 : q s * y s - p s * y s ≤ |q s - p s| * |y s| := by
    rw [← abs_mul, show q s * y s - p s * y s = (q s - p s) * y s by ring]
    exact le_abs_self _
  have h2 : |q s - p s| ≤ dist q p := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist q p s
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

theorem dot_shift (p y : S → ℝ) (t : ℝ) :
    dot p (fun s => y s - t) = dot p y - t * ∑ s, p s := by
  unfold dot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The compactness step of the grid route.**  If the grid utilities lie in one Lipschitz
set and rationalise the continuous trade map `x` on grids that become dense in `P`, some
cluster point `U` of them rationalises `x` on all of `P`. -/
theorem grid_cluster (M B : ℝ) (hM : 0 ≤ M) (u : ℕ → C(S → ℝ, ℝ))
    (hu : ∀ n, u n ∈ LipSet 0 M B) (P : Set (S → ℝ)) (G : ℕ → Set (S → ℝ))
    (hGP : ∀ n, G n ⊆ P)
    (hdense : ∀ p ∈ P, ∀ δ > 0, ∀ᶠ n in atTop, ∃ q ∈ G n, dist q p < δ)
    (hP : ∀ p ∈ P, 0 < ∑ s, p s)
    (x : (S → ℝ) → (S → ℝ)) (hx : ContinuousOn x P)
    (hopt : ∀ n, ∀ q ∈ G n, ∀ y, dot q y ≤ 0 → u n y ≤ u n (x q)) :
    ∃ U ∈ LipSet 0 M B, MapClusterPt U atTop u ∧
      ∀ p ∈ P, ∀ y, dot p y ≤ 0 → U y ≤ U (x p) := by
  obtain ⟨U, hUK, hU⟩ := (lipSet_compact (0 : S → ℝ) M B hM).exists_mapClusterPt
    (f := atTop) (u := u) (tendsto_principal.2 (Eventually.of_forall hu))
  refine ⟨U, hUK, hU, ?_⟩
  -- strict budget first
  have hstrict : ∀ p ∈ P, ∀ y, dot p y < 0 → U y ≤ U (x p) := by
    intro p hp y hy
    by_contra hlt
    push Not at hlt
    set η := (U y - U (x p)) / 3 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    -- continuity of `x` at `p`
    obtain ⟨δ1, hδ1, hx1⟩ := (Metric.continuousOn_iff.1 hx) p hp (η / (M + 1))
      (div_pos hη0 (by linarith))
    -- budget stays negative nearby
    set A := ∑ s, |y s| with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun s _ => abs_nonneg _
    set δ2 := -dot p y / (A + 1) with hδ2
    have hδ20 : 0 < δ2 := div_pos (by linarith) (by linarith)
    have hev : ∀ᶠ n in atTop, u n y ≤ u n (x p) + η := by
      filter_upwards [hdense p hp (min δ1 δ2) (lt_min hδ1 hδ20)] with n hn
      obtain ⟨q, hqG, hqd⟩ := hn
      have hq1 : dist q p < δ1 := hqd.trans_le (min_le_left _ _)
      have hq2 : dist q p < δ2 := hqd.trans_le (min_le_right _ _)
      have hbud : dot q y ≤ 0 := by
        have h1 := dot_sub_le p q y
        have h2 : dist q p * A ≤ δ2 * A := mul_le_mul_of_nonneg_right hq2.le hA0
        have h3 : δ2 * (A + 1) = -dot p y := by rw [hδ2]; field_simp
        nlinarith
      have hopt' := hopt n q hqG y hbud
      have hxq : dist (x q) (x p) < η / (M + 1) := hx1 q (hGP n hqG) hq1
      have hL := (hu n).1 (x q) (x p)
      have hsm : M * dist (x q) (x p) < η := by
        have h4 : M * dist (x q) (x p) ≤ M * (η / (M + 1)) :=
          mul_le_mul_of_nonneg_left hxq.le hM
        have h5 : (M + 1) * (η / (M + 1)) = η := by field_simp
        have h6 : 0 < η / (M + 1) := div_pos hη0 (by linarith)
        nlinarith
      rw [Real.dist_eq] at hL
      have := le_abs_self (u n (x q) - u n (x p))
      linarith
    -- the cluster point is frequently close at `y` and at `x p`
    have hW : {f : C(S → ℝ, ℝ) | |f y - U y| < η ∧ |f (x p) - U (x p)| < η} ∈ 𝓝 U := by
      refine IsOpen.mem_nhds ?_ ?_
      · rw [Set.ofPred_and]
        exact (isOpen_lt (continuous_abs.comp ((continuous_eval_const y).sub continuous_const))
          continuous_const).inter
          (isOpen_lt (continuous_abs.comp ((continuous_eval_const (x p)).sub continuous_const))
          continuous_const)
      · simp [hη0]
    have hfr := (mapClusterPt_iff_frequently.1 hU) _ hW
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := (hfr.and_eventually hev).exists
    have a1 := neg_abs_le (u n y - U y)
    have a2 := le_abs_self (u n (x p) - U (x p))
    linarith
  -- extend to the closed budget by shifting down every coordinate
  intro p hp y hy
  by_contra hlt
  push Not at hlt
  set ε := U y - U (x p) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set t := ε / 2 / (M + 1) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have hb : dot p (fun s => y s - t) < 0 := by
    rw [dot_shift]
    have := hP p hp
    nlinarith
  have h1 := hstrict p hp _ hb
  have hd : dist y (fun s => y s - t) ≤ t := by
    rw [dist_pi_le_iff ht0.le]
    intro s
    rw [Real.dist_eq, show y s - (y s - t) = t by ring, abs_of_pos ht0]
  have h2 := hUK.1 y (fun s => y s - t)
  rw [Real.dist_eq] at h2
  have htlt : t < ε / (M + 1) := by
    have hM1 : 0 < M + 1 := by linarith
    rw [ht, div_lt_div_iff_of_pos_right hM1]
    linarith
  have h3 : M * dist y (fun s => y s - t) < ε :=
    lip_small hM hε0 dist_nonneg (hd.trans_lt htlt)
  have := le_abs_self (U y - U (fun s => y s - t))
  linarith

/-- Concavity and a uniform monotone modulus pass to the cluster point. -/
theorem grid_cluster_shape (M B : ℝ) (hM : 0 ≤ M) (u : ℕ → C(S → ℝ, ℝ))
    (hu : ∀ n, u n ∈ LipSet 0 M B) (P : Set (S → ℝ)) (G : ℕ → Set (S → ℝ))
    (hGP : ∀ n, G n ⊆ P)
    (hdense : ∀ p ∈ P, ∀ δ > 0, ∀ᶠ n in atTop, ∃ q ∈ G n, dist q p < δ)
    (hP : ∀ p ∈ P, 0 < ∑ s, p s)
    (x : (S → ℝ) → (S → ℝ)) (hx : ContinuousOn x P)
    (hopt : ∀ n, ∀ q ∈ G n, ∀ y, dot q y ≤ 0 → u n y ≤ u n (x q))
    (m : (S → ℝ) → (S → ℝ) → ℝ)
    (hcav : ∀ n, u n ∈ ConcaveSet) (hmod : ∀ n, u n ∈ ModulusSet m) :
    ∃ U : C(S → ℝ, ℝ), U ∈ LipSet 0 M B ∧ U ∈ ConcaveSet ∧ U ∈ ModulusSet m ∧
      ∀ p ∈ P, ∀ y, dot p y ≤ 0 → U y ≤ U (x p) := by
  obtain ⟨U, hUK, hU, hopt'⟩ := grid_cluster M B hM u hu P G hGP hdense hP x hx hopt
  exact ⟨U, hUK, mem_of_cluster (concaveSet_closed (S := S)) hU (Eventually.of_forall hcav),
    mem_of_cluster (modulusSet_closed (S := S) m) hU (Eventually.of_forall hmod), hopt'⟩

/-- One limit utility per consumer (each consumer's trades are fixed, so no joint subsequence
is needed). -/
theorem grid_cluster_family {I : Type*} (M B : ℝ) (hM : 0 ≤ M) (u : I → ℕ → C(S → ℝ, ℝ))
    (hu : ∀ i n, u i n ∈ LipSet 0 M B) (P : Set (S → ℝ)) (G : ℕ → Set (S → ℝ))
    (hGP : ∀ n, G n ⊆ P)
    (hdense : ∀ p ∈ P, ∀ δ > 0, ∀ᶠ n in atTop, ∃ q ∈ G n, dist q p < δ)
    (hP : ∀ p ∈ P, 0 < ∑ s, p s)
    (x : I → (S → ℝ) → (S → ℝ)) (hx : ∀ i, ContinuousOn (x i) P)
    (hopt : ∀ i n, ∀ q ∈ G n, ∀ y, dot q y ≤ 0 → u i n y ≤ u i n (x i q)) :
    ∃ U : I → C(S → ℝ, ℝ), ∀ i, U i ∈ LipSet 0 M B ∧
      ∀ p ∈ P, ∀ y, dot p y ≤ 0 → U i y ≤ U i (x i p) := by
  have h := fun i => grid_cluster M B hM (u i) (hu i) P G hGP hdense hP (x i) (hx i) (hopt i)
  choose U hUK _ hUo using h
  exact ⟨U, fun i => ⟨hUK i, hUo i⟩⟩

end Goods

end GridCompact

#print axioms GridCompact.lip_small
#print axioms GridCompact.lipFun_closed
#print axioms GridCompact.lipFun_sub_pi
#print axioms GridCompact.lipFun_compact
#print axioms GridCompact.lip_continuous
#print axioms GridCompact.image_lipSet
#print axioms GridCompact.lipSet_compact
#print axioms GridCompact.mem_of_cluster
#print axioms GridCompact.concaveSet_closed
#print axioms GridCompact.modulusSet_closed
#print axioms GridCompact.dot_sub_le
#print axioms GridCompact.dot_shift
#print axioms GridCompact.grid_cluster
#print axioms GridCompact.grid_cluster_shape
#print axioms GridCompact.grid_cluster_family
