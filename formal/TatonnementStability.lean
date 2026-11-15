import Mathlib

/-!
Stage 255: stability of price adjustment under the weak axiom.

Excess demand `z` satisfies Walras' law `q · z q = 0` and the weak axiom in the form used
by `equilibrium_unique_of_warp`.  `pstar` is an equilibrium (`z pstar = 0`).

* `warp_value_pos` — away from equilibrium, the equilibrium price values excess demand
  positively: `0 < pstar · z q`;
* `lyapunov_deriv` — along any price path with `dp/dt = z p`, the squared distance to
  `pstar` has derivative `-2 * pstar · z (p t)`;
* `distance_deriv_neg` — that derivative is strictly negative off equilibrium;
* `tatonnement_distance_antitone` — the distance to equilibrium never increases.

This is Lyapunov (monotone) stability.  Asymptotic convergence of the path to `pstar` is
not proved here.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace TatonnementStability

variable {S : Type*} [Fintype S]

/-- Squared distance to the equilibrium price. -/
def dist2 (pstar q : S → ℝ) : ℝ := ∑ s, (q s - pstar s) ^ 2

theorem warp_value_pos (z : (S → ℝ) → (S → ℝ))
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (pstar : S → ℝ) (hstar : ∀ s, z pstar s = 0) (q : S → ℝ) (hq : z q ≠ z pstar) :
    0 < ∑ s, pstar s * z q s :=
  hwarp q pstar (by simp [hstar]) (fun h => hq h.symm)

theorem warp_value_nonneg (z : (S → ℝ) → (S → ℝ))
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (pstar : S → ℝ) (hstar : ∀ s, z pstar s = 0) (q : S → ℝ) :
    0 ≤ ∑ s, pstar s * z q s := by
  by_cases hq : z q = z pstar
  · have h0 : ∀ s, z q s = 0 := fun s => by rw [hq]; exact hstar s
    simp [h0]
  · exact (warp_value_pos z hwarp pstar hstar q hq).le

/-- Walras' law turns the Lyapunov derivative into the value of excess demand at the
equilibrium price. -/
theorem lyapunov_value (z : (S → ℝ) → (S → ℝ)) (hwal : ∀ q, ∑ s, q s * z q s = 0)
    (pstar q : S → ℝ) :
    ∑ s, 2 * (q s - pstar s) * z q s = -2 * ∑ s, pstar s * z q s := by
  have h : ∑ s, 2 * (q s - pstar s) * z q s
      = 2 * (∑ s, q s * z q s) - 2 * ∑ s, pstar s * z q s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h, hwal q]
  ring

theorem lyapunov_deriv (z : (S → ℝ) → (S → ℝ)) (pstar : S → ℝ) (p : ℝ → S → ℝ) (t : ℝ)
    (hp : ∀ s, HasDerivAt (fun τ => p τ s) (z (p t) s) t) :
    HasDerivAt (fun τ => dist2 pstar (p τ))
      (∑ s, 2 * (p t s - pstar s) * z (p t) s) t := by
  have hterm : ∀ s, HasDerivAt (fun τ => (p τ s - pstar s) ^ 2)
      (2 * (p t s - pstar s) * z (p t) s) t := by
    intro s
    have h1 : HasDerivAt (fun τ => p τ s - pstar s) (z (p t) s) t :=
      (hp s).sub_const (pstar s)
    have h2 := h1.mul h1
    convert h2 using 1
    · funext τ
      simp only [Pi.mul_apply]
      ring
    · ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hterm s)
  exact hsum

/-- Off equilibrium the distance to equilibrium is strictly falling. -/
theorem distance_deriv_neg (z : (S → ℝ) → (S → ℝ)) (hwal : ∀ q, ∑ s, q s * z q s = 0)
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (pstar : S → ℝ) (hstar : ∀ s, z pstar s = 0) (q : S → ℝ) (hq : z q ≠ z pstar) :
    ∑ s, 2 * (q s - pstar s) * z q s < 0 := by
  rw [lyapunov_value z hwal pstar q]
  have := warp_value_pos z hwarp pstar hstar q hq
  linarith

/-- **Monotone stability.** Along any tâtonnement path the distance to equilibrium is
non-increasing. -/
theorem tatonnement_distance_antitone (z : (S → ℝ) → (S → ℝ))
    (hwal : ∀ q, ∑ s, q s * z q s = 0)
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (pstar : S → ℝ) (hstar : ∀ s, z pstar s = 0)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t) :
    Antitone (fun t => dist2 pstar (p t)) := by
  have hd := fun t => lyapunov_deriv z pstar p t (hp t)
  apply antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv, lyapunov_value z hwal pstar (p t)]
  have := warp_value_nonneg z hwarp pstar hstar (p t)
  linarith

end TatonnementStability

end

#print axioms TatonnementStability.warp_value_pos
#print axioms TatonnementStability.warp_value_nonneg
#print axioms TatonnementStability.lyapunov_value
#print axioms TatonnementStability.lyapunov_deriv
#print axioms TatonnementStability.distance_deriv_neg
#print axioms TatonnementStability.tatonnement_distance_antitone
