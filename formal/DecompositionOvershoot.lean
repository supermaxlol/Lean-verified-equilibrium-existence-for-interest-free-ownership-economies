import Mathlib

/-!
Stage 340 (complements stages 337 and 338): Debreu's decomposition can overshoot the
necessary endowment floor.

Stage 337 gives a sufficient floor, `−mx_i(p_k) ≤ e_i`, tied to the one-consumer-per-good
decomposition `mx p Z i k s = (Z_k i + c p_k i)(δ_{si} − p_k i p_k s)` with
`c = 1 + ∑_k ∑_i |Z_k i| / p_k i`. Stage 333 gives the necessary floor
`−Z_k s ≤ ∑_i e_i s`. Here is an explicit case where the gap is strict:

* two goods, two prices `p₀ = (3/5, 4/5)` and `p₁ = (4/5, 3/5)`, and `Z ≡ 0`;
* the necessary floor is `0` (`−Z = 0`);
* any endowments meeting the stage-337 floor have `e₀ 0 + e₁ 0 ≥ 12/125 > 0`.

The definitions below restate those of `MantelExactFloor` verbatim (same formulas), in a
self-contained file. With one price there is no gap (stage 338), so the overshoot comes from
the per-consumer maximum over several prices.
-/

noncomputable section

open Finset

namespace DecompositionOvershoot

variable {O S : Type*} [Fintype O] [Fintype S] [DecidableEq S]

def mdir (p : O → S → ℝ) (i : S) (k : O) (s : S) : ℝ := (if s = i then 1 else 0) - p k i * p k s
def mcoef (p Z : O → S → ℝ) (c : ℝ) (i : S) (k : O) : ℝ := Z k i + c * p k i
def cZ (p Z : O → S → ℝ) : ℝ := 1 + ∑ k, ∑ i, |Z k i| / p k i
def mx (p Z : O → S → ℝ) (i : S) (k : O) (s : S) : ℝ := mcoef p Z (cZ p Z) i k * mdir p i k s

/-- The two prices. -/
def p2 : Fin 2 → Fin 2 → ℝ := ![![3 / 5, 4 / 5], ![4 / 5, 3 / 5]]

/-- Zero excess demand at both prices. -/
def Z0 : Fin 2 → Fin 2 → ℝ := fun _ _ => 0

theorem p2_unit (k : Fin 2) : ∑ s, p2 k s ^ 2 = 1 := by
  fin_cases k <;> simp [p2, Fin.sum_univ_two] <;> norm_num

theorem p2_pos (k s : Fin 2) : 0 < p2 k s := by
  fin_cases k <;> fin_cases s <;> simp [p2]

theorem Z0_walras (k : Fin 2) : ∑ s, p2 k s * Z0 k s = 0 := by simp [Z0]

theorem cZ0 : cZ p2 Z0 = 1 := by simp [cZ, Z0]

theorem mx_00 : mx p2 Z0 0 1 0 = 36 / 125 := by
  rw [mx, cZ0]
  simp [mcoef, mdir, Z0, p2]; norm_num

theorem mx_10 : mx p2 Z0 1 0 0 = -48 / 125 := by
  rw [mx, cZ0]
  simp [mcoef, mdir, Z0, p2]; norm_num

/-- **Stage 340: the decomposition floor overshoots.** Every endowment profile meeting the
stage-337 floor puts at least `12/125` of good `0` in the economy, although the necessary
aggregate floor `max_k (−Z_k 0)` is `0`. -/
theorem overshoot (e : Fin 2 → Fin 2 → ℝ) (he : ∀ i k s, -mx p2 Z0 i k s ≤ e i s) :
    12 / 125 ≤ ∑ i, e i 0 ∧ ∀ k, -Z0 k 0 = 0 := by
  refine ⟨?_, fun k => by simp [Z0]⟩
  have h0 := he 0 1 0
  have h1 := he 1 0 0
  rw [mx_00] at h0
  rw [mx_10] at h1
  rw [Fin.sum_univ_two]
  linarith

end DecompositionOvershoot

end

#print axioms DecompositionOvershoot.p2_unit
#print axioms DecompositionOvershoot.p2_pos
#print axioms DecompositionOvershoot.Z0_walras
#print axioms DecompositionOvershoot.cZ0
#print axioms DecompositionOvershoot.mx_00
#print axioms DecompositionOvershoot.mx_10
#print axioms DecompositionOvershoot.overshoot
