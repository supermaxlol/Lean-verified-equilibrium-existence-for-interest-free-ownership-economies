import Mathlib

/-!
# Stage 325 — the rescaling in stage 323 is necessary

Stage 323 realizes *a positive multiple* of an arbitrary Walras-law excess-demand
field from arbitrary positive endowments. This file shows the multiple cannot be
dropped: with nonnegative consumption, aggregate excess demand in good `i` is
bounded below by minus the total endowment of `i`. Hence for every endowment
profile there is a continuous, degree-zero homogeneous field satisfying Walras'
law that no allocation realizes exactly at any price, and every scale at which a
field with `z i < 0` is realized is at most `(∑ₖ eₖᵢ) / (-zᵢ)`.
-/

namespace RescaleNecessary

open Finset

/-- Value of a bundle. -/
def dot {S : Type*} [Fintype S] (p q : S → ℝ) : ℝ := ∑ s, p s * q s

/-- **Lower bound.** Nonnegative consumption forces aggregate excess demand in each
good to be at least minus the total endowment of that good. -/
theorem excess_lower {K S : Type*} [Fintype K] (c e : K → S → ℝ)
    (hc : ∀ k i, 0 ≤ c k i) (i : S) :
    -(∑ k, e k i) ≤ ∑ k, (c k i - e k i) := by
  rw [Finset.sum_sub_distrib]
  have : 0 ≤ ∑ k, c k i := Finset.sum_nonneg fun k _ => hc k i
  linarith

/-- **Not realizable.** An excess demand below minus total endowment in some good
is not the aggregate excess demand of any nonnegative allocation. -/
theorem not_realizable {K S : Type*} [Fintype K] (e : K → S → ℝ) (z : S → ℝ) (i : S)
    (hz : z i < -(∑ k, e k i)) :
    ¬ ∃ c : K → S → ℝ, (∀ k i, 0 ≤ c k i) ∧ ∀ s, ∑ k, (c k s - e k s) = z s := by
  rintro ⟨c, hc, hsum⟩
  have := excess_lower c e hc i
  rw [hsum i] at this
  linarith

/-- **Scale bound.** If `lam • z` is realized and `z i < 0`, then
`lam ≤ (∑ₖ eₖᵢ) / (-zᵢ)`. -/
theorem scale_bound {K S : Type*} [Fintype K] (e : K → S → ℝ) (z : S → ℝ) (i : S)
    (hzi : z i < 0) (lam : ℝ) (c : K → S → ℝ) (hc : ∀ k i, 0 ≤ c k i)
    (hsum : ∀ s, ∑ k, (c k s - e k s) = lam * z s) :
    lam ≤ (∑ k, e k i) / (-z i) := by
  have h := excess_lower c e hc i
  rw [hsum i] at h
  rw [le_div_iff₀ (by linarith)]
  have : lam * -z i = -(lam * z i) := by ring
  linarith

/-- The counterexample field: sell `M` of good `i`, buy its value in good `j`. -/
noncomputable def zbad {S : Type*} [DecidableEq S] (M : ℝ) (i j : S) (p : S → ℝ) : S → ℝ :=
  fun s => (if s = i then -M else 0) + (if s = j then 1 else 0) * (p i * M / p j)

theorem zbad_at_i {S : Type*} [DecidableEq S] (M : ℝ) (i j : S) (hij : i ≠ j)
    (p : S → ℝ) : zbad M i j p i = -M := by
  simp [zbad, hij]

theorem zbad_walras {S : Type*} [Fintype S] [DecidableEq S] (M : ℝ) (i j : S)
    (hij : i ≠ j) (p : S → ℝ) (hp : ∀ s, 0 < p s) : dot p (zbad M i j p) = 0 := by
  have hj : p j ≠ 0 := (hp j).ne'
  unfold dot
  rw [Fintype.sum_eq_add i j hij]
  · have e1 : zbad M i j p i = -M := zbad_at_i M i j hij p
    have e2 : zbad M i j p j = p i * M / p j := by simp [zbad, hij.symm]
    rw [e1, e2, mul_div_assoc', mul_div_cancel_left₀ _ hj]
    ring
  · rintro x ⟨hi, hx⟩
    simp [zbad, hi, hx]

theorem zbad_homogeneous {S : Type*} [DecidableEq S] (M : ℝ) (i j : S) (p : S → ℝ)
    (t : ℝ) (ht : 0 < t) : zbad M i j (fun s => t * p s) = zbad M i j p := by
  funext s
  simp only [zbad]
  rw [mul_assoc t (p i) M, mul_div_mul_left _ _ ht.ne']

theorem zbad_continuousOn {S : Type*} [Fintype S] [DecidableEq S] (M : ℝ) (i j : S) :
    ContinuousOn (zbad M i j) {p : S → ℝ | ∀ s, 0 < p s} := by
  refine continuousOn_pi.2 fun s => ?_
  have hq : ContinuousOn (fun p : S → ℝ => p i * M / p j) {p : S → ℝ | ∀ s, 0 < p s} :=
    ((continuous_apply i).continuousOn.mul continuousOn_const).div
      (continuous_apply j).continuousOn fun p hp => (hp j).ne'
  show ContinuousOn (fun p : S → ℝ => (if s = i then -M else 0) +
    (if s = j then (1 : ℝ) else 0) * (p i * M / p j)) _
  exact continuousOn_const.add (continuousOn_const.mul hq)

/-- **Rescaling is necessary.** For every endowment profile and any two distinct goods
there is a continuous, degree-zero homogeneous excess-demand field obeying Walras'
law on the positive orthant that no nonnegative allocation realizes exactly at any
price. So the positive multiple in stage 323 cannot be removed. -/
theorem rescale_necessary {K S : Type*} [Fintype K] [Fintype S] [DecidableEq S]
    (e : K → S → ℝ) (i j : S) (hij : i ≠ j) :
    ∃ Z : (S → ℝ) → S → ℝ,
      ContinuousOn Z {p | ∀ s, 0 < p s} ∧
      (∀ p : S → ℝ, ∀ t, 0 < t → Z (fun s => t * p s) = Z p) ∧
      (∀ p : S → ℝ, (∀ s, 0 < p s) → dot p (Z p) = 0) ∧
      ∀ p, ¬ ∃ c : K → S → ℝ, (∀ k i, 0 ≤ c k i) ∧ ∀ s, ∑ k, (c k s - e k s) = Z p s := by
  refine ⟨zbad (∑ k, e k i + 1) i j, zbad_continuousOn _ i j,
    fun p t ht => zbad_homogeneous _ i j p t ht,
    fun p hp => zbad_walras _ i j hij p hp, fun p => ?_⟩
  apply not_realizable e _ i
  rw [zbad_at_i _ i j hij]
  linarith

/-- **Any admissible scale is bounded.** For the field `zbad M i j` with `M > 0`, every
scale at which it is realized at some price is at most `(∑ₖ eₖᵢ) / M`. -/
theorem scale_forced {K S : Type*} [Fintype K] [DecidableEq S] (e : K → S → ℝ)
    (M : ℝ) (hM : 0 < M) (i j : S) (hij : i ≠ j) (p : S → ℝ) (lam : ℝ)
    (c : K → S → ℝ) (hc : ∀ k i, 0 ≤ c k i)
    (hsum : ∀ s, ∑ k, (c k s - e k s) = lam * zbad M i j p s) :
    lam ≤ (∑ k, e k i) / M := by
  have h := scale_bound e (zbad M i j p) i (by rw [zbad_at_i M i j hij]; linarith) lam c hc hsum
  rwa [zbad_at_i M i j hij, neg_neg] at h

end RescaleNecessary

#print axioms RescaleNecessary.excess_lower
#print axioms RescaleNecessary.not_realizable
#print axioms RescaleNecessary.scale_bound
#print axioms RescaleNecessary.zbad_at_i
#print axioms RescaleNecessary.zbad_walras
#print axioms RescaleNecessary.zbad_homogeneous
#print axioms RescaleNecessary.zbad_continuousOn
#print axioms RescaleNecessary.rescale_necessary
#print axioms RescaleNecessary.scale_forced
