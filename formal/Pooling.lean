import Mathlib

/-!
Stage 304: pooling (takaful) for interest-free lending.

`N` borrowers on a finite probability space; `L i ω` is borrower `i`'s shortfall (what an
interest-free lender loses on it).  A mutual fund collects a contribution per member and pays
the average shortfall.

* Mean floor: a fund that always covers losses must collect at least the expected average
  loss.  Pooling never removes the mean; someone pays it.
* Variance of the average is `(1/N²) ∑ᵢ ∑ⱼ Cov(i,j)`.  With equal variance `v` and common
  correlation `ρ` it is exactly `ρ v + (1 − ρ) v / N`: it falls with `N` but never below `ρ v`.
* Reserve: collecting `mean + k` per member fails with probability at most
  `(ρ v + (1 − ρ) v / N) / k²` (finite Chebyshev).
-/

noncomputable section

open Finset

namespace Pooling

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def E (π : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, π ω * X ω

def cov (π : Ω → ℝ) (L : ι → Ω → ℝ) (i j : ι) : ℝ :=
  E π fun ω => (L i ω - E π (L i)) * (L j ω - E π (L j))

/-- Average shortfall per member. -/
def avg (L : ι → Ω → ℝ) (ω : Ω) : ℝ := (∑ i, L i ω) / (Fintype.card ι : ℝ)

/-- Expected average shortfall. -/
def mbar (π : Ω → ℝ) (L : ι → Ω → ℝ) : ℝ := (∑ i, E π (L i)) / (Fintype.card ι : ℝ)

theorem E_avg (π : Ω → ℝ) (L : ι → Ω → ℝ) : E π (avg L) = mbar π L := by
  unfold E avg mbar
  have h1 : ∀ ω, π ω * ((∑ i, L i ω) / (Fintype.card ι : ℝ)) =
      ∑ i, π ω * L i ω / (Fintype.card ι : ℝ) := fun ω => by
    rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_comm, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by unfold E; rw [Finset.sum_div]

/-- **Mean floor.** -/
theorem mean_floor (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (L : ι → Ω → ℝ)
    (f : ℝ) (hcover : ∀ ω, 0 < π ω → avg L ω ≤ f) : mbar π L ≤ f := by
  rw [← E_avg]
  unfold E
  calc ∑ ω, π ω * avg L ω ≤ ∑ ω, π ω * f := Finset.sum_le_sum fun ω _ => by
        rcases (hπ ω).lt_or_eq with h | h
        · exact mul_le_mul_of_nonneg_left (hcover ω h) (hπ ω)
        · rw [← h]; simp
    _ = f := by rw [← Finset.sum_mul, hπ1, one_mul]

/-- **Variance of a sum** is the sum of covariances. -/
theorem var_sum (π : Ω → ℝ) (L : ι → Ω → ℝ) :
    E π (fun ω => (∑ i, (L i ω - E π (L i))) ^ 2) = ∑ i, ∑ j, cov π L i j := by
  unfold cov
  unfold E
  calc ∑ ω, π ω * (∑ i, (L i ω - ∑ ω', π ω' * L i ω')) ^ 2
      = ∑ ω, ∑ i, ∑ j, π ω * ((L i ω - ∑ ω', π ω' * L i ω') *
          (L j ω - ∑ ω', π ω' * L j ω')) := Finset.sum_congr rfl fun ω _ => by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, ∑ j, π ω * ((L i ω - ∑ ω', π ω' * L i ω') *
          (L j ω - ∑ ω', π ω' * L j ω')) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Variance of the average. -/
theorem var_avg (π : Ω → ℝ) (L : ι → Ω → ℝ) :
    E π (fun ω => (avg L ω - mbar π L) ^ 2) =
      (∑ i, ∑ j, cov π L i j) / (Fintype.card ι : ℝ) ^ 2 := by
  rw [← var_sum]
  show ∑ ω, π ω * (avg L ω - mbar π L) ^ 2 =
    (∑ ω, π ω * (∑ i, (L i ω - E π (L i))) ^ 2) / (Fintype.card ι : ℝ) ^ 2
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have e : avg L ω - mbar π L = (∑ i, (L i ω - E π (L i))) / (Fintype.card ι : ℝ) := by
    unfold avg mbar; rw [Finset.sum_sub_distrib, sub_div]
  rw [e, div_pow, mul_div_assoc]

/-- **Equicorrelated losses.** -/
theorem cov_sum_equi (π : Ω → ℝ) (L : ι → Ω → ℝ) (v ρ : ℝ) [DecidableEq ι]
    (hcov : ∀ i j, cov π L i j = if i = j then v else ρ * v) :
    ∑ i, ∑ j, cov π L i j =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * (ρ * v) + (1 - ρ) * v) := by
  have row : ∀ i : ι, ∑ j, cov π L i j = (Fintype.card ι : ℝ) * (ρ * v) + (1 - ρ) * v := by
    intro i
    have h : ∀ j, cov π L i j = ρ * v + (if i = j then (1 - ρ) * v else 0) := fun j => by
      rw [hcov]; split_ifs <;> ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [row, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Variance of the average with common correlation**: `ρ v + (1 − ρ) v / N`. -/
theorem var_avg_equi (π : Ω → ℝ) (L : ι → Ω → ℝ) (v ρ : ℝ) [DecidableEq ι] [Nonempty ι]
    (hcov : ∀ i j, cov π L i j = if i = j then v else ρ * v) :
    E π (fun ω => (avg L ω - mbar π L) ^ 2) = ρ * v + (1 - ρ) * v / (Fintype.card ι : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [var_avg, cov_sum_equi π L v ρ hcov]
  field_simp

/-- **The floor**: with `0 ≤ ρ ≤ 1` and `v ≥ 0`, no pool size gets the variance below `ρ v`. -/
theorem var_floor (v ρ N : ℝ) (hv : 0 ≤ v) (hρ1 : ρ ≤ 1) (hN : 0 < N) :
    ρ * v ≤ ρ * v + (1 - ρ) * v / N := by
  have : 0 ≤ (1 - ρ) * v / N := div_nonneg (mul_nonneg (by linarith) hv) hN.le
  linarith

/-- **Finite Chebyshev.** -/
theorem chebyshev (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (X : Ω → ℝ) (m k : ℝ) (hk : 0 < k) :
    ∑ ω ∈ univ.filter (fun ω => k ≤ |X ω - m|), π ω ≤ E π (fun ω => (X ω - m) ^ 2) / k ^ 2 := by
  have hk2 : 0 < k ^ 2 := by positivity
  unfold E
  rw [Finset.sum_div]
  calc ∑ ω ∈ univ.filter (fun ω => k ≤ |X ω - m|), π ω
      ≤ ∑ ω ∈ univ.filter (fun ω => k ≤ |X ω - m|), π ω * (X ω - m) ^ 2 / k ^ 2 :=
        Finset.sum_le_sum fun ω hω => by
          have h1 := (mem_filter.1 hω).2
          have h2 : k ^ 2 ≤ (X ω - m) ^ 2 := by
            rw [← sq_abs (X ω - m)]; exact pow_le_pow_left₀ hk.le h1 2
          rw [le_div_iff₀ hk2]
          exact mul_le_mul_of_nonneg_left h2 (hπ ω)
    _ ≤ ∑ ω, π ω * (X ω - m) ^ 2 / k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          div_nonneg (mul_nonneg (hπ ω) (sq_nonneg _)) hk2.le

/-- **Reserve theorem.**  Collecting `mean + k` per member, the fund falls short with
probability at most `(ρ v + (1 − ρ) v / N) / k²`. -/
theorem reserve (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (L : ι → Ω → ℝ) (v ρ k : ℝ) [DecidableEq ι]
    [Nonempty ι] (hk : 0 < k) (hcov : ∀ i j, cov π L i j = if i = j then v else ρ * v) :
    ∑ ω ∈ univ.filter (fun ω => mbar π L + k < avg L ω), π ω ≤
      (ρ * v + (1 - ρ) * v / (Fintype.card ι : ℝ)) / k ^ 2 := by
  rw [← var_avg_equi π L v ρ hcov]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ω _ _ => hπ ω)
    (chebyshev π hπ (avg L) (mbar π L) k hk)
  intro ω hω
  have h := (mem_filter.1 hω).2
  refine mem_filter.2 ⟨mem_univ _, ?_⟩
  rw [abs_of_pos (by linarith)]
  linarith

end Pooling

end

#print axioms Pooling.E_avg
#print axioms Pooling.mean_floor
#print axioms Pooling.var_sum
#print axioms Pooling.var_avg
#print axioms Pooling.cov_sum_equi
#print axioms Pooling.var_avg_equi
#print axioms Pooling.var_floor
#print axioms Pooling.chebyshev
#print axioms Pooling.reserve
