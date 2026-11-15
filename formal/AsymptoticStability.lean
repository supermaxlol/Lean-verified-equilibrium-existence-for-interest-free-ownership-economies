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


/-!
Stage 259: asymptotic convergence of price adjustment (LaSalle-type argument).

`norm_conserved` — Walras' law keeps the price path on a sphere.
`tatonnement_converges` — if the path stays in a closed set `C` on which the equilibrium
price values excess demand positively away from `pstar`, and `z` is continuous, then the
path converges to `pstar`.
`tatonnement_converges_warp` — under the weak axiom, with `pstar` the only equilibrium on
the sphere through the starting price, the tâtonnement path converges to `pstar`.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace TatonnementStability

variable {S : Type*} [Fintype S]

theorem dist2_continuous (pstar : S → ℝ) : Continuous (fun q : S → ℝ => dist2 pstar q) := by
  unfold dist2
  exact continuous_finsetSum _ (fun s _ => ((continuous_apply s).sub continuous_const).pow 2)

theorem coord_le (pstar q : S → ℝ) (s : S) : (q s - pstar s) ^ 2 ≤ dist2 pstar q :=
  Finset.single_le_sum (f := fun s => (q s - pstar s) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ s)

theorem dist2_nonneg (pstar q : S → ℝ) : 0 ≤ dist2 pstar q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem dist2_self (pstar : S → ℝ) : dist2 pstar pstar = 0 := by
  simp [dist2]

/-- Closed shell around the equilibrium inside `C`. -/
def shell (pstar : S → ℝ) (C : Set (S → ℝ)) (L M : ℝ) : Set (S → ℝ) :=
  C ∩ {q | L ≤ dist2 pstar q ∧ dist2 pstar q ≤ M}

theorem shell_compact (pstar : S → ℝ) (C : Set (S → ℝ)) (hC : IsClosed C) (L M : ℝ) :
    IsCompact (shell pstar C L M) := by
  have hcl : IsClosed (shell pstar C L M) :=
    hC.inter ((isClosed_le continuous_const (dist2_continuous pstar)).inter
      (isClosed_le (dist2_continuous pstar) continuous_const))
  have hsub : shell pstar C L M ⊆ Set.pi Set.univ
      (fun s : S => Set.Icc (pstar s - Real.sqrt M) (pstar s + Real.sqrt M)) := by
    intro q hq s _
    have h1 : (q s - pstar s) ^ 2 ≤ M := (coord_le pstar q s).trans hq.2.2
    have h2 := abs_le.1 (Real.abs_le_sqrt h1)
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hcl hsub

/-- Walras' law conserves the Euclidean norm of the price path. -/
theorem norm_conserved (z : (S → ℝ) → (S → ℝ)) (hwal : ∀ q, ∑ s, q s * z q s = 0)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t) (t : ℝ) :
    ∑ s, p t s ^ 2 = ∑ s, p 0 s ^ 2 := by
  have hd := fun t => lyapunov_deriv z (fun _ => 0) p t (hp t)
  have hzero : ∀ t, deriv (fun τ => dist2 (fun _ => 0) (p τ)) t = 0 := by
    intro t
    rw [(hd t).deriv]
    have h := hwal (p t)
    have h2 : ∑ s, 2 * (p t s - 0) * z (p t) s = 2 * ∑ s, p t s * z (p t) s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [h2, h, mul_zero]
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) hzero t 0
  simpa [dist2] using h

/-- **Asymptotic stability.** -/
theorem tatonnement_converges (z : (S → ℝ) → (S → ℝ)) (hz : Continuous z)
    (hwal : ∀ q, ∑ s, q s * z q s = 0) (pstar : S → ℝ) (C : Set (S → ℝ)) (hC : IsClosed C)
    (hpos : ∀ q ∈ C, q ≠ pstar → 0 < ∑ s, pstar s * z q s)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t)
    (hpC : ∀ t, p t ∈ C) :
    Tendsto p atTop (𝓝 pstar) := by
  have hd : ∀ t, HasDerivAt (fun τ => dist2 pstar (p τ))
      (-2 * ∑ s, pstar s * z (p t) s) t := by
    intro t
    have h := lyapunov_deriv z pstar p t (hp t)
    rw [lyapunov_value z hwal pstar (p t)] at h
    exact h
  have hg0 : ∀ t, 0 ≤ ∑ s, pstar s * z (p t) s := by
    intro t
    by_cases h : p t = pstar
    · rw [h]
      exact (hwal pstar).ge
    · exact (hpos _ (hpC t) h).le
  have hanti : Antitone (fun τ => dist2 pstar (p τ)) := by
    apply antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
    intro t
    rw [(hd t).deriv]
    have := hg0 t
    linarith
  have hbdd : BddBelow (Set.range (fun τ => dist2 pstar (p τ))) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact dist2_nonneg pstar (p t)⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hLle : ∀ t, (⨅ τ, dist2 pstar (p τ)) ≤ dist2 pstar (p t) := fun t => ciInf_le hbdd t
  have hL0 : 0 ≤ ⨅ τ, dist2 pstar (p τ) := le_ciInf (fun t => dist2_nonneg pstar (p t))
  have hLzero : (⨅ τ, dist2 pstar (p τ)) = 0 := by
    by_contra hne
    have hLpos : 0 < ⨅ τ, dist2 pstar (p τ) := lt_of_le_of_ne hL0 (Ne.symm hne)
    have hKc := shell_compact pstar C hC (⨅ τ, dist2 pstar (p τ)) (dist2 pstar (p 0))
    have hKmem : ∀ t, 0 ≤ t →
        p t ∈ shell pstar C (⨅ τ, dist2 pstar (p τ)) (dist2 pstar (p 0)) :=
      fun t ht => ⟨hpC t, hLle t, hanti ht⟩
    have hgc : Continuous (fun q : S → ℝ => ∑ s, pstar s * z q s) :=
      continuous_finsetSum _ (fun s _ => continuous_const.mul ((continuous_apply s).comp hz))
    obtain ⟨q0, hq0, hmin⟩ := hKc.exists_isMinOn ⟨p 0, hKmem 0 le_rfl⟩ hgc.continuousOn
    have hq0ne : q0 ≠ pstar := by
      intro h
      have h1 : (⨅ τ, dist2 pstar (p τ)) ≤ dist2 pstar q0 := hq0.2.1
      rw [h, dist2_self] at h1
      linarith
    have hm : 0 < ∑ s, pstar s * z q0 s := hpos q0 hq0.1 hq0ne
    have hgm : ∀ t, 0 ≤ t → ∑ s, pstar s * z q0 s ≤ ∑ s, pstar s * z (p t) s :=
      fun t ht => hmin (hKmem t ht)
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ∑ s, pstar s * z q0 s := ⟨_, rfl⟩
    rw [← hmdef] at hm hgm
    have hWd : ∀ t, HasDerivAt (fun τ => dist2 pstar (p τ) + 2 * m * τ)
        (-2 * ∑ s, pstar s * z (p t) s + 2 * m) t := by
      intro t
      have h := (hd t).add ((hasDerivAt_id t).const_mul (2 * m))
      have h' : HasDerivAt (fun τ => dist2 pstar (p τ) + 2 * m * τ)
          (-2 * ∑ s, pstar s * z (p t) s + 2 * m * 1) t := h
      rw [mul_one] at h'
      exact h'
    have hWanti : AntitoneOn (fun τ => dist2 pstar (p τ) + 2 * m * τ) (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · exact fun t _ => (hWd t).continuousAt.continuousWithinAt
      · exact fun t _ => (hWd t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hWd t).deriv]
        have := hgm t (le_of_lt ht)
        linarith
    have h2m : (0:ℝ) < 2 * m := by linarith
    have hT : (0:ℝ) ≤ dist2 pstar (p 0) / (2 * m) + 1 := by
      have := div_nonneg (dist2_nonneg pstar (p 0)) h2m.le
      linarith
    have h1 : dist2 pstar (p (dist2 pstar (p 0) / (2 * m) + 1))
          + 2 * m * (dist2 pstar (p 0) / (2 * m) + 1)
        ≤ dist2 pstar (p 0) + 2 * m * 0 :=
      hWanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT) hT
    have h2 : 2 * m * (dist2 pstar (p 0) / (2 * m) + 1) = dist2 pstar (p 0) + 2 * m := by
      have := h2m.ne'
      field_simp
    have h3 := hLle (dist2 pstar (p 0) / (2 * m) + 1)
    linarith
  rw [hLzero] at hlim
  rw [tendsto_pi_nhds]
  intro s
  have hsq : Tendsto (fun t => Real.sqrt (dist2 pstar (p t))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at h
    exact h
  have hb : ∀ t, |p t s - pstar s| ≤ Real.sqrt (dist2 pstar (p t)) :=
    fun t => Real.abs_le_sqrt (coord_le pstar (p t) s)
  have hlo : Tendsto (fun t => pstar s - Real.sqrt (dist2 pstar (p t))) atTop
      (𝓝 (pstar s)) := by
    have h := (tendsto_const_nhds (x := pstar s) (f := (atTop : Filter ℝ))).sub hsq
    rw [sub_zero] at h
    exact h
  have hhi : Tendsto (fun t => pstar s + Real.sqrt (dist2 pstar (p t))) atTop
      (𝓝 (pstar s)) := by
    have h := (tendsto_const_nhds (x := pstar s) (f := (atTop : Filter ℝ))).add hsq
    rw [add_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun t => by have := abs_le.1 (hb t); linarith [this.1])
    (fun t => by have := abs_le.1 (hb t); linarith [this.2])

/-- **Tâtonnement converges under the weak axiom.** -/
theorem tatonnement_converges_warp (z : (S → ℝ) → (S → ℝ)) (hz : Continuous z)
    (hwal : ∀ q, ∑ s, q s * z q s = 0)
    (hwarp : ∀ q q' : S → ℝ,
      (∑ s, q s * z q' s) ≤ 0 → z q' ≠ z q → 0 < ∑ s, q' s * z q s)
    (pstar : S → ℝ) (hstar : ∀ s, z pstar s = 0)
    (huniq : ∀ q : S → ℝ, ∑ s, q s ^ 2 = ∑ s, pstar s ^ 2 → (∀ s, z q s = 0) → q = pstar)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t)
    (h0 : ∑ s, p 0 s ^ 2 = ∑ s, pstar s ^ 2) :
    Tendsto p atTop (𝓝 pstar) := by
  have hC : IsClosed {q : S → ℝ | ∑ s, q s ^ 2 = ∑ s, pstar s ^ 2} :=
    isClosed_eq (continuous_finsetSum _ (fun s _ => (continuous_apply s).pow 2))
      continuous_const
  refine tatonnement_converges z hz hwal pstar _ hC (fun q hq hne => ?_) p hp
    (fun t => (norm_conserved z hwal p hp t).trans h0)
  apply warp_value_pos z hwarp pstar hstar q
  intro h
  exact hne (huniq q hq (fun s => by rw [h]; exact hstar s))

end TatonnementStability

end

#print axioms TatonnementStability.tatonnement_distance_antitone
#print axioms TatonnementStability.shell_compact
#print axioms TatonnementStability.norm_conserved
#print axioms TatonnementStability.tatonnement_converges
#print axioms TatonnementStability.tatonnement_converges_warp
