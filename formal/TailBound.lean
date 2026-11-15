import Mathlib

/-!
Stage 317: exponential tail bounds for the intermediation buffer (sharpening stage 311).

Finite probability space `Ω` with weights `π`.  Stage 311 sized buffers with Chebyshev, so the
buffer needed for failure probability `ε` grew like `1/√ε`.  Here:

* `chernoff`: `P(X ≥ t) ≤ e^{−λt} E[e^{λX}]` for every `λ ≥ 0`.
* `exp_le_chord`, `mgf_le`: a loss in `[0,1]` with mean `m` has `E[e^{λX}] ≤ exp(m(e^λ − 1))`
  (convexity of `exp`; Bennett/Poisson-type bound, no variance needed).
* `mgf_indep`: for independent losses (product weights) the moment generating function of the
  total factorizes.
* `pool_tail`: `N` independent losses in `[0,1]` with means `≤ m`:
  `P(total ≥ t) ≤ exp(−λt + N m (e^λ − 1))`.
* `buffer_size`: a buffer `B ≥ (N m (e^λ − 1) + log(1/ε))/λ` fails with probability at most `ε`.
  The buffer now grows like `log(1/ε)` rather than `1/√ε`.

Honest limits: losses are normalized to `[0,1]` and independent; the common-factor (correlated)
case of stage 310 is not covered by this bound.  `λ` is a free parameter, not optimized.
-/

open Finset BigOperators

noncomputable section

namespace TailBound

variable {Ω : Type*} [Fintype Ω]

def Ex (π X : Ω → ℝ) : ℝ := ∑ ω, π ω * X ω

def Pr (π X : Ω → ℝ) (t : ℝ) : ℝ := ∑ ω, if t ≤ X ω then π ω else 0

/-- **Chernoff / exponential Markov bound.** -/
theorem chernoff (π X : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (t l : ℝ) (hl : 0 ≤ l) :
    Pr π X t ≤ Real.exp (-(l * t)) * Ex π (fun ω => Real.exp (l * X ω)) := by
  unfold Pr Ex
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have e : Real.exp (-(l * t)) * (π ω * Real.exp (l * X ω)) = π ω * Real.exp (l * (X ω - t)) := by
    rw [mul_left_comm, ← Real.exp_add, show -(l * t) + l * X ω = l * (X ω - t) by ring]
  rw [e]
  split_ifs with h
  · have : 1 ≤ Real.exp (l * (X ω - t)) := Real.one_le_exp (mul_nonneg hl (by linarith))
    nlinarith [hπ ω]
  · exact mul_nonneg (hπ ω) (Real.exp_pos _).le

omit [Fintype Ω] in
theorem exp_le_chord (l x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (l * x) ≤ 1 + x * (Real.exp l - 1) := by
  have h : Real.exp ((1 - x) • (0 : ℝ) + x • l) ≤ (1 - x) • Real.exp 0 + x • Real.exp l :=
    convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm l x]
  linarith

/-- **Moment generating function of a bounded loss.** -/
theorem mgf_le (π X : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1)
    (hX0 : ∀ ω, 0 ≤ X ω) (hX1 : ∀ ω, X ω ≤ 1) (l : ℝ) :
    Ex π (fun ω => Real.exp (l * X ω)) ≤ Real.exp (Ex π X * (Real.exp l - 1)) := by
  have h1 : Ex π (fun ω => Real.exp (l * X ω)) ≤ 1 + Ex π X * (Real.exp l - 1) := by
    unfold Ex
    calc ∑ ω, π ω * Real.exp (l * X ω) ≤ ∑ ω, π ω * (1 + X ω * (Real.exp l - 1)) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (exp_le_chord l _ (hX0 ω) (hX1 ω)) (hπ ω)
      _ = ∑ ω, π ω + (∑ ω, π ω * X ω) * (Real.exp l - 1) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ = 1 + (∑ ω, π ω * X ω) * (Real.exp l - 1) := by rw [hπ1]
  exact h1.trans (by linarith [Real.add_one_le_exp (Ex π X * (Real.exp l - 1))])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product (independent) weights on loan outcomes. -/
def pw (π : Ω → ℝ) (x : ι → Ω) : ℝ := ∏ i, π (x i)

/-- Total loss of the pool. -/
def total (L : ι → Ω → ℝ) (x : ι → Ω) : ℝ := ∑ i, L i (x i)

/-- **Independence factorizes the moment generating function.** -/
theorem mgf_indep (π : Ω → ℝ) (L : ι → Ω → ℝ) (l : ℝ) :
    Ex (pw π) (fun x => Real.exp (l * total L x)) =
      ∏ i, Ex π (fun ω => Real.exp (l * L i ω)) := by
  unfold Ex pw total
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  show (∏ i, π (x i)) * Real.exp (l * ∑ i, L i (x i)) = ∏ i, π (x i) * Real.exp (l * L i (x i))
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

/-- **Exponential tail bound for a pool of independent bounded losses.** -/
theorem pool_tail (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (L : ι → Ω → ℝ)
    (hL0 : ∀ i ω, 0 ≤ L i ω) (hL1 : ∀ i ω, L i ω ≤ 1) (m : ℝ) (hm : ∀ i, Ex π (L i) ≤ m)
    (t l : ℝ) (hl : 0 ≤ l) :
    Pr (pw π) (total L) t ≤ Real.exp (-(l * t) + Fintype.card ι * m * (Real.exp l - 1)) := by
  have hpw : ∀ x : ι → Ω, 0 ≤ pw π x := fun x => Finset.prod_nonneg fun i _ => hπ (x i)
  have h1 := chernoff (pw (ι := ι) π) (total L) hpw t l hl
  rw [mgf_indep] at h1
  have hel : 0 ≤ Real.exp l - 1 := by linarith [Real.one_le_exp hl]
  have h2 : ∏ i, Ex π (fun ω => Real.exp (l * L i ω)) ≤ ∏ _i : ι, Real.exp (m * (Real.exp l - 1)) :=
    Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg fun ω _ => mul_nonneg (hπ ω) (Real.exp_pos _).le)
      (fun i _ => (mgf_le π (L i) hπ hπ1 (hL0 i) (hL1 i) l).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hm i) hel)))
  rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul] at h2
  calc Pr (pw π) (total L) t
      ≤ Real.exp (-(l * t)) * ∏ i, Ex π (fun ω => Real.exp (l * L i ω)) := h1
    _ ≤ Real.exp (-(l * t)) * Real.exp (Fintype.card ι * (m * (Real.exp l - 1))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-(l * t) + Fintype.card ι * m * (Real.exp l - 1)) := by
        rw [← Real.exp_add]; ring_nf

/-- **Buffer sizing: logarithmic in `1/ε`.** -/
theorem buffer_size (π : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hπ1 : ∑ ω, π ω = 1) (L : ι → Ω → ℝ)
    (hL0 : ∀ i ω, 0 ≤ L i ω) (hL1 : ∀ i ω, L i ω ≤ 1) (m : ℝ) (hm : ∀ i, Ex π (L i) ≤ m)
    (ε l B : ℝ) (hε : 0 < ε) (hl : 0 < l)
    (hB : (Fintype.card ι * m * (Real.exp l - 1) + Real.log (1 / ε)) / l ≤ B) :
    Pr (pw π) (total L) B ≤ ε := by
  have h1 := pool_tail π hπ hπ1 L hL0 hL1 m hm B l hl.le
  rw [div_le_iff₀ hl] at hB
  have hlog : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  have h2 : -(l * B) + Fintype.card ι * m * (Real.exp l - 1) ≤ Real.log ε := by
    rw [hlog] at hB; nlinarith
  calc Pr (pw π) (total L) B ≤ _ := h1
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.2 h2
    _ = ε := Real.exp_log hε

end TailBound

end

#print axioms TailBound.chernoff
#print axioms TailBound.exp_le_chord
#print axioms TailBound.mgf_le
#print axioms TailBound.mgf_indep
#print axioms TailBound.pool_tail
#print axioms TailBound.buffer_size
