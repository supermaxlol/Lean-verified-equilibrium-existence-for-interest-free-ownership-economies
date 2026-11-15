import Mathlib

/-!
Stage 338 (complements stages 333 and 337): with a single price, the aggregate floor is exact.

Stage 333 showed a necessary condition for scale-1 Mantel: `−Z s ≤ ∑_i e_i s`. Stage 337 gave a
sufficient one tied to Debreu's decomposition. With **one** price the necessary condition is
also sufficient:

* `single_price_exact` — if `p > 0`, `p·Z = 0`, endowments are nonnegative with `p·e_i > 0`,
  and `−Z s ≤ ∑_i e_i s` for every good `s`, then there are nonnegative consumptions `c_i` with
  `∑_i (c_i − e_i) = Z` and `p·c_i = p·e_i`. Each `c_i` is the **unique** maximiser on its
  budget of a continuous, concave, strictly monotone utility.
* The utility is `ku p c₀ c = ∑_s p_s · kink(c_s − c₀_s)` with `kink t = min t (t/2)`.

Scope: one price only. With several prices the gap between `∑_i max_k` and `max_k ∑_i` in
stage 337 remains open; this stage shows the gap comes from having several prices, not from
the floor itself.
-/

noncomputable section

open Finset

namespace SinglePriceExact

variable {S I : Type*} [Fintype S] [Fintype I]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- A concave, strictly increasing kink at zero. -/
def kink (t : ℝ) : ℝ := min t (t / 2)

theorem kink_le (t : ℝ) : kink t ≤ t := min_le_left _ _

theorem kink_lt (t : ℝ) (h : 0 < t) : kink t < t :=
  lt_of_le_of_lt (min_le_right _ _) (by linarith)

theorem kink_zero : kink 0 = 0 := by simp [kink]

theorem kink_strictMono : StrictMono kink := by
  intro a b h
  unfold kink
  exact lt_min (lt_of_le_of_lt (min_le_left _ _) h)
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))

theorem kink_continuous : Continuous kink :=
  continuous_id.min (continuous_id.div_const 2)

theorem kink_concave : ConcaveOn ℝ Set.univ kink := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, kink]
  have h1 := mul_le_mul_of_nonneg_left (min_le_left x (x / 2)) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right x (x / 2)) ha
  have h3 := mul_le_mul_of_nonneg_left (min_le_left y (y / 2)) hb
  have h4 := mul_le_mul_of_nonneg_left (min_le_right y (y / 2)) hb
  exact le_min (by linarith) (by linarith)

/-- The utility with kink at `c₀`. -/
def ku (p c0 : S → ℝ) (c : S → ℝ) : ℝ := ∑ s, p s * kink (c s - c0 s)

theorem ku_continuous (p c0 : S → ℝ) : Continuous (ku p c0) := by
  unfold ku
  exact continuous_finsetSum _ fun s _ =>
    continuous_const.mul (kink_continuous.comp ((continuous_apply s).sub continuous_const))

theorem ku_concave (p c0 : S → ℝ) (hp : ∀ s, 0 ≤ p s) : ConcaveOn ℝ Set.univ (ku p c0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [ku, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have e : (a • x + b • y) s - c0 s = a * (x s - c0 s) + b * (y s - c0 s) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (c0 s) * hab
  rw [e]
  have k := kink_concave.2 (Set.mem_univ (x s - c0 s)) (Set.mem_univ (y s - c0 s)) ha hb hab
  simp only [smul_eq_mul] at k
  have e2 : a * (p s * kink (x s - c0 s)) + b * (p s * kink (y s - c0 s)) =
      p s * (a * kink (x s - c0 s) + b * kink (y s - c0 s)) := by ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left k (hp s)

theorem ku_strictMono (p c0 : S → ℝ) (hp : ∀ s, 0 < p s) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) : ku p c0 y < ku p c0 z := by
  unfold ku
  obtain ⟨s0, hs0⟩ := hlt
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_left (kink_strictMono.monotone (by linarith [hyz s])) (hp s).le
  · exact ⟨s0, mem_univ _, mul_lt_mul_of_pos_left (kink_strictMono (by linarith)) (hp s0)⟩

theorem ku_le_dot (p c0 y : S → ℝ) (hp : ∀ s, 0 < p s) :
    ku p c0 y ≤ dot p y - dot p c0 := by
  unfold ku dot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro s _
  have := mul_le_mul_of_nonneg_left (kink_le (y s - c0 s)) (hp s).le
  linarith [mul_sub (p s) (y s) (c0 s)]

/-- The kink utility has `c₀` as its unique maximiser on the budget through `c₀`. -/
theorem ku_unique (p c0 : S → ℝ) (hp : ∀ s, 0 < p s) (y : S → ℝ)
    (hy : dot p y ≤ dot p c0) (hne : y ≠ c0) : ku p c0 y < ku p c0 c0 := by
  have h0 : ku p c0 c0 = 0 := by simp [ku, kink_zero]
  rw [h0]
  by_cases hpos : ∃ s, c0 s < y s
  · obtain ⟨s0, hs0⟩ := hpos
    have hlt : ku p c0 y < dot p y - dot p c0 := by
      unfold ku dot
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_lt_sum
      · intro s _
        have := mul_le_mul_of_nonneg_left (kink_le (y s - c0 s)) (hp s).le
        linarith [mul_sub (p s) (y s) (c0 s)]
      · refine ⟨s0, mem_univ _, ?_⟩
        have := mul_lt_mul_of_pos_left (kink_lt (y s0 - c0 s0) (by linarith)) (hp s0)
        linarith [mul_sub (p s0) (y s0) (c0 s0)]
    linarith
  · push Not at hpos
    obtain ⟨s0, hs0⟩ : ∃ s, y s ≠ c0 s := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hlt : dot p y < dot p c0 := by
      unfold dot
      apply Finset.sum_lt_sum
      · intro s _
        exact mul_le_mul_of_nonneg_left (hpos s) (hp s).le
      · exact ⟨s0, mem_univ _, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hpos s0) hs0) (hp s0)⟩
    linarith [ku_le_dot p c0 y hp]

/-- **Stage 338: one price, the aggregate floor is exact.** -/
theorem single_price_exact [Nonempty I] (p : S → ℝ) (hp : ∀ s, 0 < p s) (Z : S → ℝ)
    (hW : dot p Z = 0) (e : I → S → ℝ)
    (hpe : ∀ i, 0 < dot p (e i)) (hfloor : ∀ s, -Z s ≤ ∑ i, e i s) :
    ∃ c : I → S → ℝ, (∀ i s, 0 ≤ c i s) ∧ (∀ s, ∑ i, (c i s - e i s) = Z s) ∧
      (∀ i, dot p (c i) = dot p (e i)) ∧
      ∀ i, ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
        (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
        ∀ y, dot p y ≤ dot p (e i) → y ≠ c i → u y < u (c i) := by
  set D : ℝ := ∑ i, dot p (e i) with hD
  have hD0 : 0 < D := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    exact lt_of_lt_of_le (hpe i0)
      (Finset.single_le_sum (f := fun i => dot p (e i)) (fun i _ => (hpe i).le) (mem_univ i0))
  set E : S → ℝ := fun s => ∑ i, e i s with hE
  have hpE : dot p E = D := by
    simp only [hE, hD, dot, Finset.mul_sum]
    exact Finset.sum_comm
  set c : I → S → ℝ := fun i s => dot p (e i) / D * (E s + Z s) with hc
  have hθ : ∑ i, dot p (e i) / D = 1 := by
    rw [← Finset.sum_div, ← hD]
    exact div_self hD0.ne'
  have hdotc : ∀ i, dot p (c i) = dot p (e i) := by
    intro i
    have e1 : dot p (c i) = dot p (e i) / D * (dot p E + dot p Z) := by
      simp only [hc, dot]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e1, hpE, hW, add_zero]
    field_simp
  refine ⟨c, fun i s => ?_, fun s => ?_, hdotc, fun i => ⟨ku p (c i), ku_continuous _ _,
    ku_concave _ _ fun s => (hp s).le, ku_strictMono _ _ hp, fun y hy hne => ?_⟩⟩
  · exact mul_nonneg (div_nonneg (hpe i).le hD0.le) (by linarith [hfloor s])
  · rw [Finset.sum_sub_distrib]
    simp only [hc]
    rw [← Finset.sum_mul, hθ, one_mul]
    simp only [hE]
    ring
  · exact ku_unique p (c i) hp y (by rw [hdotc i]; exact hy) hne

end SinglePriceExact

end

#print axioms SinglePriceExact.kink_le
#print axioms SinglePriceExact.kink_lt
#print axioms SinglePriceExact.kink_zero
#print axioms SinglePriceExact.kink_strictMono
#print axioms SinglePriceExact.kink_continuous
#print axioms SinglePriceExact.kink_concave
#print axioms SinglePriceExact.ku_continuous
#print axioms SinglePriceExact.ku_concave
#print axioms SinglePriceExact.ku_strictMono
#print axioms SinglePriceExact.ku_le_dot
#print axioms SinglePriceExact.ku_unique
#print axioms SinglePriceExact.single_price_exact
