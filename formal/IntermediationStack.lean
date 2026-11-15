import Mathlib

/-!
Stage 311: the interest-free intermediation stack (capstone of 301–310).

A lender advances principal `I` per member at zero markup.  The member's shortfall after collateral
is the per-member pooled loss `X ω` (stage 304).  The shortfall is absorbed by a per-member buffer

  `B = κ − c·a + k + (1 − h)·C`

with these parts:
* `κ`: takaful contribution (a non-return-bearing contribution to the pool, not interest);
* `c·a`: verification cost at audit probability `a` (stages 301 and 308);
* `k`: reserve capital held against the correlated tail (stages 304 and 310);
* `(1 − h)·C`: haircut lender-of-last-resort liquidity against collateral `C` (stage 305).

The lender receives `I − max (X − B) 0`, so never more than principal.  Results:
* `receipts_le`, `receipts_full`: zero markup, and full repayment whenever `X ≤ B`;
* `fail_le`: P(not repaid in full) ≤ Var X / (B − E X)² (Chebyshev, proved here);
* `shortfall_le`: the lender's expected loss is at most Var X / (B − E X);
* `buffer_ps`: profit sharing audits with probability `a ≤ θ` (stage 308), so sizing the buffer at
  `a = θ` is conservative;
* `stack`: the capstone.  If the buffer sized at `θ` exceeds the mean loss and the pool has
  stage-304 variance `ρ v + (1 − ρ) v / N`, the lender is never paid above principal, is paid in full
  outside the failure event, and both failure probability and expected loss are bounded by explicit
  functions of `N`;
* `stack_limit`, `stack_sizing`: as `N → ∞` these bounds fall to the correlated floor `ρ v / d`;
  any target failure probability `α` is met once `Var ≤ α (B − E X)²`.

Honest limits: Chebyshev bounds only (no distributional tail); the buffer components are taken as
given numbers, so their financing is not modelled here; shortfall `X` is exogenous to the contract.
-/

open Finset BigOperators Filter Topology

noncomputable section

namespace IntermediationStack

variable {Ω : Type*} [Fintype Ω]

def Ex (π X : Ω → ℝ) : ℝ := ∑ ω, π ω * X ω

def Var (π X : Ω → ℝ) : ℝ := ∑ ω, π ω * (X ω - Ex π X) ^ 2

/-- Per-member buffer: contribution net of verification, reserve, haircut LOLR liquidity. -/
def buffer (κ c a k h C : ℝ) : ℝ := κ - c * a + k + (1 - h) * C

/-- Lender's receipts per member: principal less any unabsorbed shortfall. -/
def receipts (I : ℝ) (X : Ω → ℝ) (B : ℝ) (ω : Ω) : ℝ := I - max (X ω - B) 0

def failProb (π X : Ω → ℝ) (B : ℝ) : ℝ := ∑ ω, if B < X ω then π ω else 0

def shortfall (π X : Ω → ℝ) (B : ℝ) : ℝ := ∑ ω, π ω * max (X ω - B) 0

omit [Fintype Ω] in
theorem receipts_le (I : ℝ) (X : Ω → ℝ) (B : ℝ) (ω : Ω) : receipts I X B ω ≤ I := by
  unfold receipts; linarith [le_max_right (X ω - B) 0]

omit [Fintype Ω] in
theorem receipts_full (I : ℝ) (X : Ω → ℝ) (B : ℝ) (ω : Ω) (h : X ω ≤ B) :
    receipts I X B ω = I := by
  unfold receipts; rw [max_eq_right (by linarith), sub_zero]

theorem var_nonneg (π X : Ω → ℝ) (hπ : ∀ ω, 0 ≤ π ω) : 0 ≤ Var π X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hπ ω) (sq_nonneg _)

theorem buffer_ps (κ c a θ k h C : ℝ) (hc : 0 ≤ c) (ha : a ≤ θ) :
    buffer κ c θ k h C ≤ buffer κ c a k h C := by
  unfold buffer; nlinarith

theorem exp_receipts (π X : Ω → ℝ) (I B : ℝ) (h1 : ∑ ω, π ω = 1) :
    Ex π (receipts I X B) = I - shortfall π X B := by
  show ∑ ω, π ω * (I - max (X ω - B) 0) = I - ∑ ω, π ω * max (X ω - B) 0
  rw [Finset.sum_congr rfl fun ω _ =>
      (by ring : π ω * (I - max (X ω - B) 0) = π ω * I - π ω * max (X ω - B) 0),
    Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]

/-- **Chebyshev for the stack.** -/
theorem fail_le (π X : Ω → ℝ) (B : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hμ : Ex π X < B) :
    failProb π X B ≤ Var π X / (B - Ex π X) ^ 2 := by
  have hd : 0 < B - Ex π X := by linarith
  rw [le_div_iff₀ (pow_pos hd 2)]
  unfold failProb Var
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · have h1 : B - Ex π X ≤ X ω - Ex π X := by linarith
    have h2 : (B - Ex π X) ^ 2 ≤ (X ω - Ex π X) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 (hπ ω)
  · rw [zero_mul]; exact mul_nonneg (hπ ω) (sq_nonneg _)

/-- **Expected unabsorbed shortfall.** -/
theorem shortfall_le (π X : Ω → ℝ) (B : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hμ : Ex π X < B) :
    shortfall π X B ≤ Var π X / (B - Ex π X) := by
  have hd : 0 < B - Ex π X := by linarith
  rw [le_div_iff₀ hd]
  unfold shortfall Var
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hπ ω)
  rcases le_or_gt (X ω) B with h | h
  · rw [max_eq_right (by linarith), zero_mul]; exact sq_nonneg _
  · rw [max_eq_left (by linarith)]
    have e1 : X ω - B ≤ X ω - Ex π X := by linarith
    have e2 : B - Ex π X ≤ X ω - Ex π X := by linarith
    nlinarith [mul_le_mul e1 e2 hd.le (by linarith : (0 : ℝ) ≤ X ω - Ex π X)]

/-- **The interest-free intermediation stack.** -/
theorem stack (π X : Ω → ℝ) (I κ c a θ k h C ρ v : ℝ) (N : ℕ)
    (hπ : ∀ ω, 0 ≤ π ω) (h1 : ∑ ω, π ω = 1) (hc : 0 ≤ c) (ha : a ≤ θ)
    (hcover : Ex π X < buffer κ c θ k h C)
    (hpool : Var π X = ρ * v + (1 - ρ) * v / N) :
    (∀ ω, receipts I X (buffer κ c a k h C) ω ≤ I) ∧
    (∀ ω, X ω ≤ buffer κ c a k h C → receipts I X (buffer κ c a k h C) ω = I) ∧
    failProb π X (buffer κ c a k h C) ≤
      (ρ * v + (1 - ρ) * v / N) / (buffer κ c θ k h C - Ex π X) ^ 2 ∧
    I - Ex π (receipts I X (buffer κ c a k h C)) ≤
      (ρ * v + (1 - ρ) * v / N) / (buffer κ c θ k h C - Ex π X) := by
  have hB : buffer κ c θ k h C ≤ buffer κ c a k h C := buffer_ps κ c a θ k h C hc ha
  have hμ : Ex π X < buffer κ c a k h C := lt_of_lt_of_le hcover hB
  have hd0 : 0 < buffer κ c θ k h C - Ex π X := by linarith
  have hV := var_nonneg π X hπ
  refine ⟨fun ω => receipts_le I X _ ω, fun ω hω => receipts_full I X _ ω hω, ?_, ?_⟩
  · rw [← hpool]
    refine (fail_le π X _ hπ hμ).trans ?_
    exact div_le_div_of_nonneg_left hV (pow_pos hd0 2) (by nlinarith)
  · rw [← hpool, exp_receipts π X I _ h1, sub_sub_cancel]
    refine (shortfall_le π X _ hπ hμ).trans ?_
    exact div_le_div_of_nonneg_left hV hd0 (by linarith)

/-- **The large-pool limit of the stack's bounds** is the correlated floor. -/
theorem stack_limit (ρ v d : ℝ) :
    Tendsto (fun N : ℕ => (ρ * v + (1 - ρ) * v / N) / d) atTop (𝓝 (ρ * v / d)) := by
  have h : Tendsto (fun N : ℕ => (1 - ρ) * v / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ * v) atTop (𝓝 (ρ * v))).add
    h).div_const d
  rw [add_zero] at h2
  exact h2

/-- **Sizing the stack to a target failure probability.** -/
theorem stack_sizing (π X : Ω → ℝ) (B α : ℝ) (hπ : ∀ ω, 0 ≤ π ω) (hμ : Ex π X < B)
    (hα : Var π X ≤ α * (B - Ex π X) ^ 2) : failProb π X B ≤ α := by
  have hd : 0 < B - Ex π X := by linarith
  refine (fail_le π X B hπ hμ).trans ?_
  rw [div_le_iff₀ (pow_pos hd 2)]
  exact hα

end IntermediationStack

end

#print axioms IntermediationStack.receipts_le
#print axioms IntermediationStack.receipts_full
#print axioms IntermediationStack.var_nonneg
#print axioms IntermediationStack.buffer_ps
#print axioms IntermediationStack.exp_receipts
#print axioms IntermediationStack.fail_le
#print axioms IntermediationStack.shortfall_le
#print axioms IntermediationStack.stack
#print axioms IntermediationStack.stack_limit
#print axioms IntermediationStack.stack_sizing
