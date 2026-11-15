import Mathlib

/-!
# Stage 351: the benchmark ownership economy is globally stable

Households share Cobb–Douglas (log) weights `α s > 0` with `∑ α = 1` (the demand rule
derived in stage 252) and the aggregate endowment is `ω s > 0`. Aggregate excess demand is

  `z q s = α s * (∑ t, q t * ω t) / q s - ω s`.

Results:
* `cd_walras`: Walras' law at every price with nonzero coordinates.
* `cd_equilibrium`: `pstar s = κ * α s / ω s` clears every market, for every `κ > 0`.
* `lagrange`: the Lagrange identity behind Cauchy–Schwarz, in the form needed here.
* `cd_value_pos`: on the sphere through `pstar`, at positive prices other than `pstar`, the
  equilibrium price values excess demand strictly positively.
* `cd_unique`: `pstar` is the only equilibrium with positive coordinates on its sphere.
* `converges_on`: stage 259's convergence theorem, with continuity and Walras' law needed only
  on the closed set where the path stays (the same proof).
* `cd_stable`: every tâtonnement path that starts on the sphere through `pstar` and keeps
  prices at least `δ > 0` converges to `pstar`.

Limits: identical weights (heterogeneous weights fall under Sonnenschein–Mantel–Debreu, where
stability can fail); the path is assumed to exist and to keep prices above `δ`.
-/

open Finset Filter Topology

namespace OwnershipStability

variable {S : Type*} [Fintype S]

/-! ### Convergence on a closed region (stage 259, localised) -/

def dist2 (pstar q : S → ℝ) : ℝ := ∑ s, (q s - pstar s) ^ 2

theorem dist2_continuous (pstar : S → ℝ) : Continuous (fun q : S → ℝ => dist2 pstar q) := by
  unfold dist2
  fun_prop

theorem coord_le (pstar q : S → ℝ) (s : S) : (q s - pstar s) ^ 2 ≤ dist2 pstar q :=
  Finset.single_le_sum (f := fun s => (q s - pstar s) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ s)

theorem dist2_nonneg (pstar q : S → ℝ) : 0 ≤ dist2 pstar q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem dist2_self (pstar : S → ℝ) : dist2 pstar pstar = 0 := by
  simp [dist2]

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
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hterm s)

theorem lyapunov_value_at (z : (S → ℝ) → (S → ℝ)) (pstar q : S → ℝ)
    (hw : ∑ s, q s * z q s = 0) :
    ∑ s, 2 * (q s - pstar s) * z q s = -2 * ∑ s, pstar s * z q s := by
  have h : ∑ s, 2 * (q s - pstar s) * z q s
      = 2 * (∑ s, q s * z q s) - 2 * ∑ s, pstar s * z q s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h, hw]
  ring

/-- Walras' law along the path conserves the Euclidean norm. -/
theorem norm_conserved_on (z : (S → ℝ) → (S → ℝ)) (p : ℝ → S → ℝ)
    (hw : ∀ t, ∑ s, p t s * z (p t) s = 0)
    (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t) (t : ℝ) :
    ∑ s, p t s ^ 2 = ∑ s, p 0 s ^ 2 := by
  have hd := fun t => lyapunov_deriv z (fun _ => 0) p t (hp t)
  have hzero : ∀ t, deriv (fun τ => dist2 (fun _ => 0) (p τ)) t = 0 := by
    intro t
    rw [(hd t).deriv]
    have h2 : ∑ s, 2 * (p t s - 0) * z (p t) s = 2 * ∑ s, p t s * z (p t) s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [h2, hw t, mul_zero]
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) hzero t 0
  simpa [dist2] using h

/-- **Convergence on a closed region.** Stage 259's theorem, with continuity of `z` and
Walras' law required only on the closed set `C` in which the path stays. -/
theorem converges_on (z : (S → ℝ) → (S → ℝ)) (pstar : S → ℝ) (C : Set (S → ℝ))
    (hC : IsClosed C) (hz : ContinuousOn z C) (hwal : ∀ q ∈ C, ∑ s, q s * z q s = 0)
    (hpos : ∀ q ∈ C, q ≠ pstar → 0 < ∑ s, pstar s * z q s)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (z (p t) s) t)
    (hpC : ∀ t, p t ∈ C) :
    Tendsto p atTop (𝓝 pstar) := by
  have hd : ∀ t, HasDerivAt (fun τ => dist2 pstar (p τ))
      (-2 * ∑ s, pstar s * z (p t) s) t := by
    intro t
    have h := lyapunov_deriv z pstar p t (hp t)
    rw [lyapunov_value_at z pstar (p t) (hwal _ (hpC t))] at h
    exact h
  have hg0 : ∀ t, 0 ≤ ∑ s, pstar s * z (p t) s := by
    intro t
    by_cases h : p t = pstar
    · have hm : pstar ∈ C := h ▸ hpC t
      rw [h]
      exact (hwal pstar hm).ge
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
    have hgc : ContinuousOn (fun q : S → ℝ => ∑ s, pstar s * z q s) C :=
      continuousOn_finsetSum _ (fun s _ =>
        continuousOn_const.mul ((continuous_apply s).comp_continuousOn hz))
    obtain ⟨q0, hq0, hmin⟩ := hKc.exists_isMinOn ⟨p 0, hKmem 0 le_rfl⟩
      (hgc.mono fun q hq => hq.1)
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

/-! ### The Cobb–Douglas ownership economy -/

/-- Aggregate excess demand with common Cobb–Douglas weights `α`. -/
noncomputable def zcd (α ω : S → ℝ) (q : S → ℝ) (s : S) : ℝ :=
  α s * (∑ t, q t * ω t) / q s - ω s

/-- The equilibrium ray. -/
noncomputable def pstar (α ω : S → ℝ) (κ : ℝ) (s : S) : ℝ := κ * α s / ω s

theorem cd_walras (α ω : S → ℝ) (hα : ∑ s, α s = 1) (q : S → ℝ) (hq : ∀ s, q s ≠ 0) :
    ∑ s, q s * zcd α ω q s = 0 := by
  unfold zcd
  have h : ∀ s, q s * (α s * (∑ t, q t * ω t) / q s - ω s)
      = α s * (∑ t, q t * ω t) - q s * ω s := by
    intro s
    field_simp [hq s]
  simp only [h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hα]
  ring

theorem cd_equilibrium (α ω : S → ℝ) (hα0 : ∀ s, 0 < α s) (hα : ∑ s, α s = 1)
    (hω : ∀ s, 0 < ω s) (κ : ℝ) (hκ : 0 < κ) (s : S) : zcd α ω (pstar α ω κ) s = 0 := by
  have hW : ∑ t, pstar α ω κ t * ω t = κ := by
    have : ∀ t, pstar α ω κ t * ω t = κ * α t := fun t => by
      unfold pstar
      field_simp [(hω t).ne']
    simp only [this, ← Finset.mul_sum, hα, mul_one]
  unfold zcd
  rw [hW]
  unfold pstar
  have := (hω s).ne'
  have := (hα0 s).ne'
  have := hκ.ne'
  field_simp
  ring

/-- The Lagrange identity: for positive `x`,
`2 * ((∑ x) * (∑ α² / x) - (∑ α)²) = ∑ₛ ∑ₜ (xₛ αₜ - xₜ αₛ)² / (xₛ xₜ)`. -/
theorem lagrange (α x : S → ℝ) (hx : ∀ s, 0 < x s) :
    ∑ s, ∑ t, (x s * α t - x t * α s) ^ 2 / (x s * x t)
      = 2 * ((∑ s, x s) * (∑ t, α t ^ 2 / x t) - (∑ s, α s) * (∑ t, α t)) := by
  have hterm : ∀ s t, (x s * α t - x t * α s) ^ 2 / (x s * x t)
      = x s * (α t ^ 2 / x t) + x t * (α s ^ 2 / x s) - 2 * (α s * α t) := by
    intro s t
    have := (hx s).ne'
    have := (hx t).ne'
    field_simp
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hswap : ∑ s, ∑ t, x t * (α s ^ 2 / x s) = ∑ s, ∑ t, x s * (α t ^ 2 / x t) :=
    Finset.sum_comm
  rw [hswap]
  simp only [← Finset.mul_sum]
  ring

theorem value_formula (α ω : S → ℝ) (hω : ∀ s, 0 < ω s) (κ : ℝ) (q : S → ℝ)
    (hq : ∀ s, 0 < q s) :
    ∑ s, pstar α ω κ s * zcd α ω q s
      = κ * ((∑ s, q s * ω s) * (∑ t, α t ^ 2 / (q t * ω t)) - ∑ s, α s) := by
  have h : ∀ s, pstar α ω κ s * zcd α ω q s
      = κ * ((∑ t, q t * ω t) * (α s ^ 2 / (q s * ω s)) - α s) := by
    intro s
    unfold pstar zcd
    have := (hω s).ne'
    have := (hq s).ne'
    field_simp
  simp only [h, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- On the sphere through `pstar`, positive prices proportional to `α / ω` equal `pstar`. -/
theorem ray_eq (α ω : S → ℝ) (hα0 : ∀ s, 0 < α s) (hω : ∀ s, 0 < ω s) (κ : ℝ) (hκ : 0 < κ)
    (q : S → ℝ) (hq : ∀ s, 0 < q s)
    (hsph : ∑ s, q s ^ 2 = ∑ s, pstar α ω κ s ^ 2)
    (hprop : ∀ s t, (q s * ω s) * α t = (q t * ω t) * α s) : q = pstar α ω κ := by
  by_cases hS : IsEmpty S
  · funext s
    exact (hS.false s).elim
  rw [not_isEmpty_iff] at hS
  obtain ⟨s0⟩ := hS
  set l := q s0 * ω s0 / α s0 with hl
  have hlpos : 0 < l := div_pos (mul_pos (hq s0) (hω s0)) (hα0 s0)
  have hqt : ∀ t, q t = l * α t / ω t := by
    intro t
    have h := hprop s0 t
    have := (hω t).ne'
    have := (hα0 s0).ne'
    rw [hl]
    field_simp
    linarith
  have hA : 0 < ∑ s, (α s / ω s) ^ 2 :=
    Finset.sum_pos (fun s _ => pow_pos (div_pos (hα0 s) (hω s)) 2) ⟨s0, Finset.mem_univ _⟩
  have hsq : l ^ 2 * ∑ s, (α s / ω s) ^ 2 = κ ^ 2 * ∑ s, (α s / ω s) ^ 2 := by
    have e1 : ∑ s, q s ^ 2 = l ^ 2 * ∑ s, (α s / ω s) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [hqt s]; ring
    have e2 : ∑ s, pstar α ω κ s ^ 2 = κ ^ 2 * ∑ s, (α s / ω s) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by unfold pstar; ring
    rw [← e1, ← e2, hsph]
  have hl2 : l ^ 2 = κ ^ 2 := mul_right_cancel₀ hA.ne' hsq
  have hlk : l = κ := by nlinarith [sq_nonneg (l - κ), sq_nonneg (l + κ)]
  funext t
  rw [hqt t, hlk]
  rfl

theorem cd_value_pos (α ω : S → ℝ) (hα0 : ∀ s, 0 < α s) (hα : ∑ s, α s = 1)
    (hω : ∀ s, 0 < ω s) (κ : ℝ) (hκ : 0 < κ) (q : S → ℝ) (hq : ∀ s, 0 < q s)
    (hsph : ∑ s, q s ^ 2 = ∑ s, pstar α ω κ s ^ 2) (hne : q ≠ pstar α ω κ) :
    0 < ∑ s, pstar α ω κ s * zcd α ω q s := by
  rw [value_formula α ω hω κ q hq]
  set x : S → ℝ := fun s => q s * ω s with hx
  have hxpos : ∀ s, 0 < x s := fun s => mul_pos (hq s) (hω s)
  have hL := lagrange α x hxpos
  have hex : ∃ s t, (x s * α t - x t * α s) ^ 2 / (x s * x t) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    refine ray_eq α ω hα0 hω κ hκ q hq hsph (fun s t => ?_)
    have h := hall s t
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      simp only [hx] at this
      linarith
    · exact absurd h (mul_pos (hxpos s) (hxpos t)).ne'
  obtain ⟨s1, t1, h1⟩ := hex
  have hnn : ∀ s t, 0 ≤ (x s * α t - x t * α s) ^ 2 / (x s * x t) := fun s t =>
    div_nonneg (sq_nonneg _) (mul_pos (hxpos s) (hxpos t)).le
  have hpos : 0 < ∑ s, ∑ t, (x s * α t - x t * α s) ^ 2 / (x s * x t) := by
    refine Finset.sum_pos' (fun s _ => Finset.sum_nonneg fun t _ => hnn s t)
      ⟨s1, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun t _ => hnn s1 t)
      ⟨t1, Finset.mem_univ _, lt_of_le_of_ne (hnn s1 t1) (Ne.symm h1)⟩
  rw [hL, hα] at hpos
  have key : 1 < (∑ s, x s) * (∑ t, α t ^ 2 / x t) := by linarith
  simp only [hx] at key
  have : 0 < (∑ s, q s * ω s) * (∑ t, α t ^ 2 / (q t * ω t)) - 1 := by linarith
  rw [hα]
  exact mul_pos hκ this

/-- `pstar` is the only positive equilibrium on its sphere. -/
theorem cd_unique (α ω : S → ℝ) (hα0 : ∀ s, 0 < α s) (hα : ∑ s, α s = 1)
    (hω : ∀ s, 0 < ω s) (κ : ℝ) (hκ : 0 < κ) (q : S → ℝ) (hq : ∀ s, 0 < q s)
    (hsph : ∑ s, q s ^ 2 = ∑ s, pstar α ω κ s ^ 2) (heq : ∀ s, zcd α ω q s = 0) :
    q = pstar α ω κ := by
  by_contra hne
  have h := cd_value_pos α ω hα0 hα hω κ hκ q hq hsph hne
  simp [heq] at h

/-- **Global stability of the benchmark ownership economy.** -/
theorem cd_stable (α ω : S → ℝ) (hα0 : ∀ s, 0 < α s) (hα : ∑ s, α s = 1)
    (hω : ∀ s, 0 < ω s) (κ : ℝ) (hκ : 0 < κ) (δ : ℝ) (hδ : 0 < δ)
    (p : ℝ → S → ℝ) (hp : ∀ t s, HasDerivAt (fun τ => p τ s) (zcd α ω (p t) s) t)
    (hfloor : ∀ t s, δ ≤ p t s)
    (h0 : ∑ s, p 0 s ^ 2 = ∑ s, pstar α ω κ s ^ 2) :
    Tendsto p atTop (𝓝 (pstar α ω κ)) := by
  set C : Set (S → ℝ) :=
    {q | ∑ s, q s ^ 2 = ∑ s, pstar α ω κ s ^ 2} ∩ {q | ∀ s, δ ≤ q s} with hCdef
  have hCpos : ∀ q ∈ C, ∀ s, 0 < q s := fun q hq s => lt_of_lt_of_le hδ (hq.2 s)
  have hC : IsClosed C := by
    refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const) ?_
    have : {q : S → ℝ | ∀ s, δ ≤ q s} = ⋂ s, {q : S → ℝ | δ ≤ q s} := by
      ext q
      simp
    rw [this]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hz : ContinuousOn (zcd α ω) C := by
    refine continuousOn_pi.2 fun s => ?_
    unfold zcd
    refine ContinuousOn.sub (ContinuousOn.div ?_ (continuous_apply s).continuousOn
      fun q hq => (hCpos q hq s).ne') continuousOn_const
    exact (continuous_const.mul (by fun_prop)).continuousOn
  have hwal : ∀ q ∈ C, ∑ s, q s * zcd α ω q s = 0 :=
    fun q hq => cd_walras α ω hα q fun s => (hCpos q hq s).ne'
  have hpC : ∀ t, p t ∈ C := by
    intro t
    refine ⟨?_, fun s => hfloor t s⟩
    show ∑ s, p t s ^ 2 = ∑ s, pstar α ω κ s ^ 2
    rw [norm_conserved_on (zcd α ω) p
      (fun t => cd_walras α ω hα (p t) fun s => (lt_of_lt_of_le hδ (hfloor t s)).ne') hp t]
    exact h0
  exact converges_on (zcd α ω) (pstar α ω κ) C hC hz hwal
    (fun q hq hne => cd_value_pos α ω hα0 hα hω κ hκ q (hCpos q hq) hq.1 hne) p hp hpC

end OwnershipStability

#print axioms OwnershipStability.dist2_continuous
#print axioms OwnershipStability.coord_le
#print axioms OwnershipStability.shell_compact
#print axioms OwnershipStability.lyapunov_deriv
#print axioms OwnershipStability.lyapunov_value_at
#print axioms OwnershipStability.norm_conserved_on
#print axioms OwnershipStability.converges_on
#print axioms OwnershipStability.cd_walras
#print axioms OwnershipStability.cd_equilibrium
#print axioms OwnershipStability.lagrange
#print axioms OwnershipStability.value_formula
#print axioms OwnershipStability.ray_eq
#print axioms OwnershipStability.cd_value_pos
#print axioms OwnershipStability.cd_unique
#print axioms OwnershipStability.cd_stable
