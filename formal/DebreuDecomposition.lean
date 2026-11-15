import Mathlib

/-!
Stage 256: the Debreu decomposition (first half of Sonnenschein–Mantel–Debreu surjectivity).

At a price `p`, let `proj p i` be the projection of the `i`-th unit vector onto the budget
hyperplane `p · x = 0`.  Then any vector `z` with `p · z = 0` is

  `z = ∑ i, (z i + lam * p i) • proj p i`     for every `lam`,

each summand has zero value at `p` (it obeys Walras' law on its own), and at a strictly
positive price the coefficients can be made strictly positive.  So every Walrasian excess
demand splits into one "agent" per good, each demanding a positive multiple of the
budget-feasible direction of its own good.

Not proved here: that each summand is the demand of a fixed preference relation.  That
construction is the remaining half of Mantel surjectivity.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace DebreuDecomposition

variable {S : Type*} [Fintype S] [DecidableEq S]

def nsq (p : S → ℝ) : ℝ := ∑ s, p s ^ 2

/-- Projection of the unit vector of good `i` onto the hyperplane orthogonal to `p`. -/
def proj (p : S → ℝ) (i : S) : S → ℝ :=
  fun s => (if s = i then 1 else 0) - p i / nsq p * p s

theorem nsq_pos (p : S → ℝ) (t : S) (hp : ∀ s, 0 < p s) : 0 < nsq p := by
  unfold nsq
  have h1 : p t ^ 2 ≤ ∑ s, p s ^ 2 :=
    Finset.single_le_sum (f := fun s => p s ^ 2) (fun s _ => sq_nonneg (p s))
      (Finset.mem_univ t)
  have h2 : 0 < p t ^ 2 := pow_pos (hp t) 2
  linarith

/-- Each projected direction has zero value: the agent obeys Walras' law individually. -/
theorem proj_walras (p : S → ℝ) (hp : nsq p ≠ 0) (i : S) :
    ∑ s, p s * proj p i s = 0 := by
  have h1 : ∀ s, p s * proj p i s
      = (if s = i then p s else 0) - p i / nsq p * p s ^ 2 := by
    intro s
    unfold proj
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  have h2 : p i / nsq p * ∑ s, p s ^ 2 = p i := by
    show p i / nsq p * nsq p = p i
    field_simp
  rw [h2, sub_self]

/-- **Debreu decomposition.** -/
theorem decomposition (p z : S → ℝ) (hp : nsq p ≠ 0) (hwal : ∑ s, p s * z s = 0)
    (lam : ℝ) (t : S) :
    ∑ i, (z i + lam * p i) * proj p i t = z t := by
  have h1 : ∀ i, (z i + lam * p i) * proj p i t
      = (if t = i then z i + lam * p i else 0)
        - p t / nsq p * (p i * z i + lam * p i ^ 2) := by
    intro i
    unfold proj
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hwal]
  simp only [Finset.mem_univ, ite_true]
  have h2 : p t / nsq p * (0 + lam * ∑ i, p i ^ 2) = lam * p t := by
    show p t / nsq p * (0 + lam * nsq p) = lam * p t
    field_simp
    ring
  rw [h2]
  ring

/-- At a strictly positive price the coefficients can be chosen strictly positive. -/
theorem exists_positive_coeff (p z : S → ℝ) (hp : ∀ s, 0 < p s) :
    ∃ lam : ℝ, ∀ i, 0 < z i + lam * p i := by
  refine ⟨∑ i, |z i| / p i + 1, fun i => ?_⟩
  have h1 : |z i| / p i ≤ ∑ j, |z j| / p j :=
    Finset.single_le_sum (f := fun j => |z j| / p j)
      (fun j _ => div_nonneg (abs_nonneg _) (hp j).le) (Finset.mem_univ i)
  have h2 : (|z i| / p i + 1) * p i ≤ (∑ j, |z j| / p j + 1) * p i :=
    mul_le_mul_of_nonneg_right (by linarith) (hp i).le
  have h3 : (|z i| / p i + 1) * p i = |z i| + p i := by
    have := (hp i).ne'
    field_simp
  have h4 := neg_abs_le (z i)
  have h5 := hp i
  linarith

/-- **Positive decomposition into individually Walrasian agents.** -/
theorem positive_decomposition [Nonempty S] (p z : S → ℝ) (hp : ∀ s, 0 < p s)
    (hwal : ∑ s, p s * z s = 0) :
    ∃ β : S → ℝ, (∀ i, 0 < β i) ∧ (∀ t, ∑ i, β i * proj p i t = z t) ∧
      (∀ i, ∑ s, p s * (β i * proj p i s) = 0) := by
  obtain ⟨lam, hlam⟩ := exists_positive_coeff p z hp
  have hn : nsq p ≠ 0 := (nsq_pos p (Classical.arbitrary S) hp).ne'
  refine ⟨fun i => z i + lam * p i, hlam, fun t => decomposition p z hn hwal lam t,
    fun i => ?_⟩
  have h : ∑ s, p s * ((z i + lam * p i) * proj p i s)
      = (z i + lam * p i) * ∑ s, p s * proj p i s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h, proj_walras p hn i, mul_zero]

end DebreuDecomposition

end

#print axioms DebreuDecomposition.nsq_pos
#print axioms DebreuDecomposition.proj_walras
#print axioms DebreuDecomposition.decomposition
#print axioms DebreuDecomposition.exists_positive_coeff
#print axioms DebreuDecomposition.positive_decomposition
