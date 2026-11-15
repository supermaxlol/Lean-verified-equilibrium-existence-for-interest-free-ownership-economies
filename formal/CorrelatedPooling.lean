import Mathlib

/-!
Stage 322: pooling a finite number of correlated risks.

Finite probability space, `N` losses `L i`.  Each has variance `v`, and every pair has covariance
`c` (equicorrelated).  Complements stage 310, which took the limit `N → ∞`.

* `ex_tot`, `var_tot`: the variance of the total is the sum of all covariances.
* `var_equi`: `Var(total) = N v + N (N − 1) c`.
* `avg_formula`: per member, `Var(total)/N² = c + (v − c)/N`.
* `corr_lower`: variances are nonnegative, so `c ≥ −v/(N − 1)`.
* `chebyshev`, `pool_tail_avg`: the chance the pool's loss deviates from its mean by `b` per member
  is at most `(c + (v − c)/N)/b²`.
* `floor_le`, `avg_antitone`, `n_needed`: the bound falls with `N` but never below `c/b²`, and
  `N ≥ (v − c)/δ` members bring it within `δ/b²` of that floor.

Honest limits: equicorrelation; Chebyshev, not exponential, bounds (independent case: stage 317).
The floor is for the variance and this bound; the actual tail floor under a common factor is
stage 310's.
-/

open Finset BigOperators

noncomputable section

namespace CorrelatedPooling

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def Ex (π X : Ω → ℝ) : ℝ := ∑ ω, π ω * X ω

def cov (π X Y : Ω → ℝ) : ℝ := Ex π (fun ω => (X ω - Ex π X) * (Y ω - Ex π Y))

def tot (L : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, L i ω

def Pr (π Y : Ω → ℝ) (t : ℝ) : ℝ := ∑ ω, if t ≤ Y ω then π ω else 0

theorem ex_tot (π : Ω → ℝ) (L : ι → Ω → ℝ) : Ex π (tot L) = ∑ i, Ex π (L i) := by
  unfold Ex tot
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- **The variance of the total is the sum of all covariances.** -/
theorem var_tot (π : Ω → ℝ) (L : ι → Ω → ℝ) :
    cov π (tot L) (tot L) = ∑ i, ∑ j, cov π (L i) (L j) := by
  have h : ∀ ω, (tot L ω - Ex π (tot L)) * (tot L ω - Ex π (tot L)) =
      ∑ i, ∑ j, (L i ω - Ex π (L i)) * (L j ω - Ex π (L j)) := by
    intro ω
    rw [ex_tot]
    unfold tot
    rw [← Finset.sum_sub_distrib, Finset.sum_mul_sum]
  unfold cov
  simp only [h]
  unfold Ex
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem var_nonneg (π X : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) : 0 ≤ cov π X X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hπ ω) (mul_self_nonneg _)

/-- **Equicorrelated variance.** -/
theorem var_equi [DecidableEq ι] (π : Ω → ℝ) (L : ι → Ω → ℝ) (v c : ℝ)
    (hv : ∀ i, cov π (L i) (L i) = v) (hc : ∀ i j, i ≠ j → cov π (L i) (L j) = c) :
    cov π (tot L) (tot L) =
      (Fintype.card ι : ℝ) * v + (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * c := by
  have hrow : ∀ i, ∑ j, cov π (L i) (L j) = v + ((Fintype.card ι : ℝ) - 1) * c := by
    intro i
    have e : ∀ j, cov π (L i) (L j) = c + (if j = i then v - c else 0) := by
      intro j
      split_ifs with h
      · subst h; rw [hv]; ring
      · rw [hc i j (Ne.symm h)]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  rw [var_tot]
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem avg_formula (N v c : ℝ) (hN : 0 < N) :
    (N * v + N * (N - 1) * c) / N ^ 2 = c + (v - c) / N := by
  field_simp
  ring

/-- **Correlation cannot be too negative.** -/
theorem corr_lower [DecidableEq ι] (π : Ω → ℝ) (L : ι → Ω → ℝ) (v c : ℝ) (hπ : ∀ ω, 0 ≤ π ω)
    (hv : ∀ i, cov π (L i) (L i) = v) (hc : ∀ i j, i ≠ j → cov π (L i) (L j) = c)
    (hN : 1 < (Fintype.card ι : ℝ)) : -v / ((Fintype.card ι : ℝ) - 1) ≤ c := by
  have h0 := var_nonneg π (tot L) hπ
  rw [var_equi π L v c hv hc] at h0
  rw [div_le_iff₀ (by linarith)]
  nlinarith

omit [Fintype ι] in
theorem cheb_core (π X : Ω → ℝ) (m t : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (ht : 0 < t) :
    (∑ ω, if t ≤ |X ω - m| then π ω else 0) ≤
      (∑ ω, π ω * ((X ω - m) * (X ω - m))) / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h
  · rw [le_div_iff₀ ht2]
    have hsq : t ^ 2 ≤ (X ω - m) * (X ω - m) := by
      have := abs_mul_abs_self (X ω - m)
      nlinarith [abs_nonneg (X ω - m)]
    have := mul_le_mul_of_nonneg_left hsq (hπ ω)
    linarith
  · exact div_nonneg (mul_nonneg (hπ ω) (mul_self_nonneg _)) ht2.le

omit [Fintype ι] in
theorem chebyshev (π X : Ω → ℝ) (t : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (ht : 0 < t) :
    Pr π (fun ω => |X ω - Ex π X|) t ≤ cov π X X / t ^ 2 :=
  cheb_core π X (Ex π X) t hπ ht

/-- **Tail bound for a finite correlated pool, per member.** -/
theorem pool_tail_avg [DecidableEq ι] (π : Ω → ℝ) (L : ι → Ω → ℝ) (v c b : ℝ)
    (hπ : ∀ ω, 0 ≤ π ω) (hv : ∀ i, cov π (L i) (L i) = v)
    (hc : ∀ i j, i ≠ j → cov π (L i) (L j) = c) (hN : 0 < (Fintype.card ι : ℝ)) (hb : 0 < b) :
    Pr π (fun ω => |tot L ω - Ex π (tot L)|) ((Fintype.card ι : ℝ) * b) ≤
      (c + (v - c) / (Fintype.card ι : ℝ)) / b ^ 2 := by
  have h := chebyshev π (tot L) ((Fintype.card ι : ℝ) * b) hπ (mul_pos hN hb)
  rw [var_equi π L v c hv hc] at h
  refine h.trans (le_of_eq ?_)
  rw [← avg_formula _ v c hN]
  field_simp

theorem floor_le (N v c : ℝ) (hN : 0 < N) (hvc : c ≤ v) : c ≤ c + (v - c) / N := by
  have : 0 ≤ (v - c) / N := div_nonneg (by linarith) hN.le
  linarith

theorem avg_antitone (N1 N2 v c : ℝ) (h1 : 0 < N1) (hle : N1 ≤ N2) (hvc : c ≤ v) :
    c + (v - c) / N2 ≤ c + (v - c) / N1 := by
  have h2 : 0 < N2 := by linarith
  have : (v - c) / N2 ≤ (v - c) / N1 := by
    rw [div_le_div_iff₀ h2 h1]
    exact mul_le_mul_of_nonneg_left hle (by linarith)
  linarith

theorem n_needed (N v c δ : ℝ) (hN : 0 < N) (hδ : 0 < δ) (h : (v - c) / δ ≤ N) :
    (v - c) / N ≤ δ := by
  rw [div_le_iff₀ hN]
  rw [div_le_iff₀ hδ] at h
  linarith [mul_comm N δ]

end CorrelatedPooling

end

#print axioms CorrelatedPooling.ex_tot
#print axioms CorrelatedPooling.var_tot
#print axioms CorrelatedPooling.var_nonneg
#print axioms CorrelatedPooling.var_equi
#print axioms CorrelatedPooling.avg_formula
#print axioms CorrelatedPooling.corr_lower
#print axioms CorrelatedPooling.cheb_core
#print axioms CorrelatedPooling.chebyshev
#print axioms CorrelatedPooling.pool_tail_avg
#print axioms CorrelatedPooling.floor_le
#print axioms CorrelatedPooling.avg_antitone
#print axioms CorrelatedPooling.n_needed
