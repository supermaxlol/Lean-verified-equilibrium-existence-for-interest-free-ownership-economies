import Mathlib

/-!
Stage 269: every division of ownership is Pareto efficient (homothetic utility).

Setting of stage 268: states `S`, probabilities `π`, output `Y`, felicity `u` with a
homogeneous supergradient `m`.  Household `i` holds the share `w i` of output in every
state, shares summing to one.

* `share_gap` — the utility gain of any bundle over the share bundle is at most `h w` times
  its extra cost at the state prices `π s * m (Y s)`;
* `ownership_pareto` — no feasible allocation makes every household at least as well off
  as under the share allocation and one household strictly better off.

Together with `share_optimal` of stage 268 this is the second welfare theorem within the
class: each division of ownership is efficient and is supported by the same state prices.
-/

noncomputable section

open Finset BigOperators

namespace OwnershipEfficiency

variable {I S : Type*} [Fintype I] [Fintype S]

theorem share_gap (π Y x : S → ℝ) (u m h : ℝ → ℝ) (w : ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hw : 0 < w)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ y : ℝ, 0 < y → m (w * y) = h w * m y) (hx : ∀ s, 0 < x s) :
    ∑ s, π s * u (x s) - ∑ s, π s * u (w * Y s)
      ≤ h w * (∑ s, π s * m (Y s) * x s - w * ∑ s, π s * m (Y s) * Y s) := by
  have hterm : ∀ s, π s * u (x s) ≤ π s * u (w * Y s)
      + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
    intro s
    have h1 := hsg (x s) (w * Y s) (hx s) (mul_pos hw (hY s))
    rw [hhom (Y s) (hY s)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hπ s)
    have e : π s * (u (w * Y s) + h w * m (Y s) * (x s - w * Y s))
        = π s * u (w * Y s) + h w * (π s * m (Y s) * x s - w * (π s * m (Y s) * Y s)) := by
      ring
    linarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  linarith

/-- **Every division of ownership is Pareto efficient.** -/
theorem ownership_pareto (π Y : S → ℝ) (u m h : ℝ → ℝ) (w : I → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hY : ∀ s, 0 < Y s) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hm : ∀ y : ℝ, 0 < y → 0 ≤ m y)
    (hsg : ∀ a b : ℝ, 0 < a → 0 < b → u a ≤ u b + m b * (a - b))
    (hhom : ∀ v y : ℝ, 0 < v → 0 < y → m (v * y) = h v * m y)
    (hh : ∀ v : ℝ, 0 < v → 0 < h v)
    (x' : I → S → ℝ) (hx' : ∀ i s, 0 < x' i s) (hfeas : ∀ s, ∑ i, x' i s ≤ Y s)
    (hweak : ∀ i, ∑ s, π s * u (w i * Y s) ≤ ∑ s, π s * u (x' i s)) (k : I) :
    ¬ ∑ s, π s * u (w k * Y s) < ∑ s, π s * u (x' k s) := by
  intro hk
  have hgap : ∀ i, ∑ s, π s * u (x' i s) - ∑ s, π s * u (w i * Y s)
      ≤ h (w i) * (∑ s, π s * m (Y s) * x' i s - w i * ∑ s, π s * m (Y s) * Y s) :=
    fun i => share_gap π Y (x' i) u m h (w i) hπ hY (hw i) hsg
      (fun y hy => hhom (w i) y (hw i) hy) (hx' i)
  have hg0 : ∀ i, 0 ≤ ∑ s, π s * m (Y s) * x' i s - w i * ∑ s, π s * m (Y s) * Y s := by
    intro i
    by_contra hc
    have := mul_neg_of_pos_of_neg (hh _ (hw i)) (lt_of_not_ge hc)
    have := hgap i
    have := hweak i
    linarith
  have hgk : 0 < ∑ s, π s * m (Y s) * x' k s - w k * ∑ s, π s * m (Y s) * Y s := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos (hh _ (hw k)).le (le_of_not_gt hc)
    have := hgap k
    linarith
  have hpos : 0 < ∑ i, (∑ s, π s * m (Y s) * x' i s - w i * ∑ s, π s * m (Y s) * Y s) :=
    Finset.sum_pos' (fun i _ => hg0 i) ⟨k, Finset.mem_univ k, hgk⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, Finset.sum_comm] at hpos
  have hle : ∑ s, ∑ i, π s * m (Y s) * x' i s ≤ ∑ s, π s * m (Y s) * Y s :=
    Finset.sum_le_sum (fun s _ => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hfeas s) (mul_nonneg (hπ s) (hm _ (hY s))))
  linarith

end OwnershipEfficiency

end

#print axioms OwnershipEfficiency.share_gap
#print axioms OwnershipEfficiency.ownership_pareto
