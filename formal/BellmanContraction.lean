import Mathlib

/-!
Stage 258: the Bellman equation by contraction mapping.

Part 1 (finite state space).
* `blackwell` — Blackwell's sufficient conditions: a monotone, `β`-discounting operator on
  value functions is a `β`-contraction in the sup metric;
* `blackwell_fixed_point` — for `β < 1` it has exactly one fixed point, and value
  iteration converges to it from any starting guess;
* `bellmanOp` — the Bellman operator of a finite Markov decision problem;
  `mdp_bellman` — it has a unique value function, value iteration converges to it, and a
  stationary greedy policy attains the maximum in every state.

Part 2 (infinite-horizon log saver, continuous wealth).
* `saver_bellman_le`, `saver_bellman_eq` — `V W = A + log W / (1 - β)` satisfies the
  Bellman equation `V W = max_c log c + β V (R (W - c))`, with the maximum attained at
  `c = (1 - β) W`: the saver keeps the fraction `β` of wealth every period.

Part 2 verifies the candidate value function.  The uniqueness statement of Part 1 is for
finite state spaces and does not cover the unbounded log case.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace BellmanContraction

variable {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]

/-- **Blackwell's sufficient conditions.** -/
theorem blackwell (T : (X → ℝ) → (X → ℝ)) (β : ℝ) (hβ : 0 ≤ β)
    (hmono : ∀ v w : X → ℝ, (∀ x, v x ≤ w x) → ∀ x, T v x ≤ T w x)
    (hdisc : ∀ (v : X → ℝ) (c : ℝ), 0 ≤ c → ∀ x, T (fun y => v y + c) x ≤ T v x + β * c)
    (v w : X → ℝ) : dist (T v) (T w) ≤ β * dist v w := by
  have key : ∀ v w : X → ℝ, ∀ x, T v x - T w x ≤ β * dist v w := by
    intro v w x
    have h1 : ∀ y, v y ≤ w y + dist v w := by
      intro y
      have h := dist_le_pi_dist v w y
      rw [Real.dist_eq] at h
      have h' := le_abs_self (v y - w y)
      linarith
    have h2 := hmono v (fun y => w y + dist v w) h1 x
    have h3 := hdisc w (dist v w) dist_nonneg x
    linarith
  rw [dist_pi_le_iff (mul_nonneg hβ dist_nonneg)]
  intro x
  rw [Real.dist_eq, abs_le]
  have h1 := key v w x
  have h2 := key w v x
  rw [dist_comm w v] at h2
  constructor <;> linarith

/-- **Unique fixed point and convergence of value iteration.** -/
theorem blackwell_fixed_point (T : (X → ℝ) → (X → ℝ)) (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hmono : ∀ v w : X → ℝ, (∀ x, v x ≤ w x) → ∀ x, T v x ≤ T w x)
    (hdisc : ∀ (v : X → ℝ) (c : ℝ), 0 ≤ c → ∀ x, T (fun y => v y + c) x ≤ T v x + β * c) :
    ∃ V : X → ℝ, T V = V ∧ (∀ W, T W = W → W = V) ∧
      ∀ v0, Tendsto (fun n => T^[n] v0) atTop (𝓝 V) := by
  have hK : (⟨β, hβ⟩ : NNReal) < 1 := show β < ((1 : NNReal) : ℝ) by rw [NNReal.coe_one]; exact hβ1
  have hc : ContractingWith ⟨β, hβ⟩ T :=
    ⟨hK, LipschitzWith.of_dist_le_mul (fun v w => blackwell T β hβ hmono hdisc v w)⟩
  exact ⟨ContractingWith.fixedPoint T hc, hc.fixedPoint_isFixedPt,
    fun W hW => hc.fixedPoint_unique hW, fun v0 => hc.tendsto_iterate_fixedPoint v0⟩

/-- Bellman operator of a finite Markov decision problem with reward `r`, transition
probabilities `P` and discount factor `β`. -/
def bellmanOp (r : X → A → ℝ) (P : X → A → X → ℝ) (β : ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty (fun a => r x a + β * ∑ y, P x a y * v y)

theorem bellmanOp_ge (r : X → A → ℝ) (P : X → A → X → ℝ) (β : ℝ) (v : X → ℝ) (x : X)
    (a : A) : r x a + β * ∑ y, P x a y * v y ≤ bellmanOp r P β v x :=
  Finset.le_sup' (fun a => r x a + β * ∑ y, P x a y * v y) (Finset.mem_univ a)

theorem bellmanOp_mono (r : X → A → ℝ) (P : X → A → X → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hP : ∀ x a y, 0 ≤ P x a y) (v w : X → ℝ) (h : ∀ x, v x ≤ w x) (x : X) :
    bellmanOp r P β v x ≤ bellmanOp r P β w x := by
  refine Finset.sup'_le _ _ (fun a _ => ?_)
  have h1 : ∑ y, P x a y * v y ≤ ∑ y, P x a y * w y :=
    Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (hP x a y))
  have h2 := mul_le_mul_of_nonneg_left h1 hβ
  have h3 := bellmanOp_ge r P β w x a
  show r x a + β * ∑ y, P x a y * v y ≤ bellmanOp r P β w x
  linarith

theorem bellmanOp_disc (r : X → A → ℝ) (P : X → A → X → ℝ) (β : ℝ)
    (hPsum : ∀ x a, ∑ y, P x a y = 1) (v : X → ℝ) (c : ℝ) (x : X) :
    bellmanOp r P β (fun y => v y + c) x ≤ bellmanOp r P β v x + β * c := by
  refine Finset.sup'_le _ _ (fun a _ => ?_)
  have hs : ∑ y, P x a y * (v y + c) = ∑ y, P x a y * v y + c := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hPsum x a, one_mul]
  have h3 := bellmanOp_ge r P β v x a
  show r x a + β * ∑ y, P x a y * (v y + c) ≤ bellmanOp r P β v x + β * c
  rw [hs]
  linarith

/-- **Bellman equation for a finite Markov decision problem.** There is exactly one value
function, value iteration converges to it, and a stationary policy is optimal in every
state. -/
theorem mdp_bellman (r : X → A → ℝ) (P : X → A → X → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hP : ∀ x a y, 0 ≤ P x a y) (hPsum : ∀ x a, ∑ y, P x a y = 1) :
    ∃ V : X → ℝ, bellmanOp r P β V = V ∧ (∀ W, bellmanOp r P β W = W → W = V) ∧
      (∀ v0, Tendsto (fun n => (bellmanOp r P β)^[n] v0) atTop (𝓝 V)) ∧
      (∀ x a, r x a + β * ∑ y, P x a y * V y ≤ V x) ∧
      ∃ π : X → A, ∀ x, V x = r x (π x) + β * ∑ y, P x (π x) y * V y := by
  obtain ⟨V, hV, huniq, hiter⟩ := blackwell_fixed_point (bellmanOp r P β) β hβ hβ1
    (bellmanOp_mono r P β hβ hP) (fun v c _ x => bellmanOp_disc r P β hPsum v c x)
  refine ⟨V, hV, huniq, hiter, fun x a => ?_, ?_⟩
  · have h := bellmanOp_ge r P β V x a
    rw [hV] at h
    exact h
  · have hex : ∀ x, ∃ a, bellmanOp r P β V x = r x a + β * ∑ y, P x a y * V y := by
      intro x
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun a => r x a + β * ∑ y, P x a y * V y)
      exact ⟨a, ha⟩
    choose π hπ using hex
    refine ⟨π, fun x => ?_⟩
    have h := hπ x
    rw [hV] at h
    exact h

/-! ### Infinite-horizon log saver -/

/-- Constant of the log saver's value function. -/
def valueConst (β R : ℝ) : ℝ :=
  (Real.log (1 - β) + β / (1 - β) * (Real.log β + Real.log R)) / (1 - β)

/-- Value function of the infinite-horizon log saver with gross return `R`. -/
def saverValue (β R W : ℝ) : ℝ := valueConst β R + Real.log W / (1 - β)

theorem log_split (β c W : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hcW : c < W) :
    Real.log c + β / (1 - β) * Real.log (W - c)
      ≤ Real.log ((1 - β) * W) + β / (1 - β) * Real.log (β * W) := by
  have h1β : 0 < 1 - β := by linarith
  have hW : 0 < W := by linarith
  have hk : 0 < β / (1 - β) := div_pos hβ h1β
  have hs : 0 < W - c := by linarith
  have hcs : 0 < (1 - β) * W := mul_pos h1β hW
  have has : 0 < β * W := mul_pos hβ hW
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hcs)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hs has)
  rw [Real.log_div hc.ne' hcs.ne'] at h1
  rw [Real.log_div hs.ne' has.ne'] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hk.le
  have h4 : c / ((1 - β) * W) - 1 + β / (1 - β) * ((W - c) / (β * W) - 1) = 0 := by
    have := hβ.ne'
    have := hW.ne'
    have := h1β.ne'
    field_simp
    ring
  linarith

/-- The Bellman gap of any consumption choice equals the static log-split gap. -/
theorem saver_gap (β R c W : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (hc : 0 < c)
    (hcW : c < W) :
    saverValue β R W - (Real.log c + β * saverValue β R (R * (W - c)))
      = (Real.log ((1 - β) * W) + β / (1 - β) * Real.log (β * W))
        - (Real.log c + β / (1 - β) * Real.log (W - c)) := by
  have h1β : 0 < 1 - β := by linarith
  have hW : 0 < W := by linarith
  have hs : 0 < W - c := by linarith
  unfold saverValue valueConst
  rw [Real.log_mul hR.ne' hs.ne', Real.log_mul h1β.ne' hW.ne', Real.log_mul hβ.ne' hW.ne']
  have := h1β.ne'
  field_simp
  ring

/-- **Bellman inequality.** No feasible consumption beats the value function. -/
theorem saver_bellman_le (β R c W : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hR : 0 < R)
    (hc : 0 < c) (hcW : c < W) :
    Real.log c + β * saverValue β R (R * (W - c)) ≤ saverValue β R W := by
  have h1 := saver_gap β R c W hβ hβ1 hR hc hcW
  have h2 := log_split β c W hβ hβ1 hc hcW
  linarith

/-- **Bellman equality.** Consuming the fraction `1 - β` of wealth attains the value. -/
theorem saver_bellman_eq (β R W : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hR : 0 < R) (hW : 0 < W) :
    Real.log ((1 - β) * W) + β * saverValue β R (R * (β * W)) = saverValue β R W := by
  have h1β : 0 < 1 - β := by linarith
  have hc : 0 < (1 - β) * W := mul_pos h1β hW
  have hcW : (1 - β) * W < W := by nlinarith [mul_pos hβ hW]
  have h := saver_gap β R ((1 - β) * W) W hβ hβ1 hR hc hcW
  have e : W - (1 - β) * W = β * W := by ring
  rw [e] at h
  linarith

end BellmanContraction

end

#print axioms BellmanContraction.blackwell
#print axioms BellmanContraction.blackwell_fixed_point
#print axioms BellmanContraction.bellmanOp_mono
#print axioms BellmanContraction.bellmanOp_disc
#print axioms BellmanContraction.mdp_bellman
#print axioms BellmanContraction.log_split
#print axioms BellmanContraction.saver_gap
#print axioms BellmanContraction.saver_bellman_le
#print axioms BellmanContraction.saver_bellman_eq
