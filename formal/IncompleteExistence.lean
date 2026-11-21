import Mathlib

/-!
# Stage 366: existence of the equity-and-bond equilibrium with heterogeneous CRRA

Stage 354 showed that in any equilibrium of the one-date economy with a share of output `Y` and
a bond paying one in every state, households with different CRRA coefficients trade the bond.
It did not prove that an equilibrium exists. This file proves it.

Setup: states `s` with probabilities `π s > 0` and output `Y s > 0`, not all equal (`lo` and `hi`
are a lowest and a highest state). Household `i` starts with `w i > 0` units of the equity (equity
price normalised to one), has marginal utility `c ^ (−γ i)` with `γ i > 0` (log and every power
utility), and chooses equity `θ` and bonds `b` at bond price `1 / R`, with `θ + b / R = w i`.
Consumption is `θ Y s + b = R w + θ (Y s − R)` (`cons`).

* `g_anti`: the Euler expression `g = Σ π c ^ (−γ) (Y − R)` is strictly decreasing in `θ` on the
  affordable set, for `Y lo < R < Y hi`.
* `exists_zero`: it has a zero, found by the intermediate value theorem between two explicit
  portfolios at which one state's consumption is pushed close to zero (`small_delta`).
* `optimal`: that zero maximises expected utility over every affordable portfolio (mean value
  theorem); so each household has a unique optimal portfolio `dem R`.
* `dem_continuous`: `dem` is continuous in `R` (sign persistence).
* `w_le_dem`, `dem_le_w`: at `R` below household `i`'s tilted mean
  `m i = E[Y ^ (1 − γ i)] / E[Y ^ (−γ i)]` it holds at least its endowment of equity, above it at
  most (`tilted_mem`: each `m i` lies strictly between `Y lo` and `Y hi`).
* **`exists_equilibrium`**: there are a bond return `R` with `Y lo < R < Y hi`, and portfolios
  `(θ i, b i)` such that each household's portfolio is affordable, gives positive consumption
  and is optimal among all affordable portfolios with positive consumption, and both markets
  clear: `Σ θ i = Σ w i` and `Σ b i = 0`. The aggregate excess demand for equity changes sign
  between the smallest and the largest tilted mean, and the intermediate value theorem gives
  the clearing return.

Reading: together with stage 354, the economy with equity and a fixed claim has an equilibrium,
and in it the fixed claim is traded whenever risk attitudes differ.

Limits: one date, two assets, common beliefs, utilities with marginal utility exactly
`c ^ (−γ)` (CRRA); positive endowments of equity only. Uniqueness of the equilibrium is not
proved. More assets, more dates, and general (non-CRRA) preferences are not covered.
-/

noncomputable section

open Finset Filter Topology Set
open scoped Classical

namespace IncompleteExistence

variable {S : Type*} [Fintype S]

/-- Consumption in state `s` with wealth `w`, equity `θ` and bond return `R`. -/
def cons (Y : S → ℝ) (w θ R : ℝ) (s : S) : ℝ := R * w + θ * (Y s - R)

/-- The Euler expression. -/
def g (π Y : S → ℝ) (γ w θ R : ℝ) : ℝ := ∑ s, π s * cons Y w θ R s ^ (-γ) * (Y s - R)

def Feas (Y : S → ℝ) (w θ R : ℝ) : Prop := ∀ s, 0 < cons Y w θ R s

/-- Expected utility. -/
def EU (π Y : S → ℝ) (u : ℝ → ℝ) (w θ R : ℝ) : ℝ := ∑ s, π s * u (cons Y w θ R s)

omit [Fintype S] in
theorem term_lt (π Y : S → ℝ) (γ w θ θ' R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ)
    (hθ : θ < θ') (hF : Feas Y w θ R) (hF' : Feas Y w θ' R) (s : S) (hs : Y s ≠ R) :
    π s * cons Y w θ' R s ^ (-γ) * (Y s - R) < π s * cons Y w θ R s ^ (-γ) * (Y s - R) := by
  have e : cons Y w θ' R s - cons Y w θ R s = (θ' - θ) * (Y s - R) := by unfold cons; ring
  rcases lt_or_gt_of_ne hs with h | h
  · have hc : cons Y w θ' R s < cons Y w θ R s := by nlinarith
    have := Real.rpow_lt_rpow_of_neg (hF' s) hc (by linarith : -γ < 0)
    exact mul_lt_mul_of_neg_right (mul_lt_mul_of_pos_left this (hπ s)) (by linarith)
  · have hc : cons Y w θ R s < cons Y w θ' R s := by nlinarith
    have := Real.rpow_lt_rpow_of_neg (hF s) hc (by linarith : -γ < 0)
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left this (hπ s)) (by linarith)

/-- **The Euler expression is strictly decreasing** in the equity position. -/
theorem g_anti (π Y : S → ℝ) (γ w θ θ' R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (hi : S)
    (hRhi : R < Y hi) (hθ : θ < θ') (hF : Feas Y w θ R) (hF' : Feas Y w θ' R) :
    g π Y γ w θ' R < g π Y γ w θ R := by
  refine Finset.sum_lt_sum (fun s _ => ?_)
    ⟨hi, Finset.mem_univ _, term_lt π Y γ w θ θ' R hπ hγ hθ hF hF' hi (by linarith)⟩
  by_cases hs : Y s = R
  · rw [hs, sub_self, mul_zero, mul_zero]
  · exact (term_lt π Y γ w θ θ' R hπ hγ hθ hF hF' s hs).le

omit [Fintype S] in
theorem feas_between (Y : S → ℝ) (w θ θ' t R : ℝ) (h1 : θ ≤ t) (h2 : t ≤ θ')
    (hF : Feas Y w θ R) (hF' : Feas Y w θ' R) : Feas Y w t R := by
  intro s
  have a := hF s
  have b := hF' s
  unfold cons at *
  rcases le_total R (Y s) with h | h
  · nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 h)]
  · nlinarith [mul_le_mul_of_nonpos_right h2 (sub_nonpos.2 h)]

theorem hasDeriv_EU (π Y : S → ℝ) (γ w R t : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hF : Feas Y w t R) :
    HasDerivAt (fun θ => EU π Y u w θ R) (g π Y γ w t R) t := by
  unfold EU g
  apply HasDerivAt.fun_sum
  intro s _
  have hin : HasDerivAt (fun θ => cons Y w θ R s) (Y s - R) t :=
    (((hasDerivAt_id' t).mul_const (Y s - R)).const_add (R * w)).congr_deriv (one_mul _)
  exact (((hu _ (hF s)).comp t hin).const_mul (π s)).congr_deriv (by ring)

/-- **A zero of the Euler expression is optimal** among all affordable portfolios. -/
theorem optimal (π Y : S → ℝ) (γ w R θs θ' : ℝ) (u : ℝ → ℝ)
    (hu : ∀ c, 0 < c → HasDerivAt u (c ^ (-γ)) c) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (hi : S)
    (hRhi : R < Y hi) (hFs : Feas Y w θs R) (hg0 : g π Y γ w θs R = 0)
    (hF' : Feas Y w θ' R) : EU π Y u w θ' R ≤ EU π Y u w θs R := by
  rcases lt_trichotomy θ' θs with h | h | h
  · have hd : ∀ x ∈ Icc θ' θs, HasDerivAt (fun θ => EU π Y u w θ R) (g π Y γ w x R) x :=
      fun x hx => hasDeriv_EU π Y γ w R x u hu (feas_between Y w θ' θs x R hx.1 hx.2 hF' hFs)
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun θ => EU π Y u w θ R)
      (fun x => g π Y γ w x R) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between Y w θ' θs c R hc.1.le hc.2.le hF' hFs
    have hgc : 0 < g π Y γ w c R := by
      have := g_anti π Y γ w c θs R hπ hγ hi hRhi hc.2 hcF hFs
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_pos hgc (sub_pos.2 h)]
  · rw [h]
  · have hd : ∀ x ∈ Icc θs θ', HasDerivAt (fun θ => EU π Y u w θ R) (g π Y γ w x R) x :=
      fun x hx => hasDeriv_EU π Y γ w R x u hu (feas_between Y w θs θ' x R hx.1 hx.2 hFs hF')
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun θ => EU π Y u w θ R)
      (fun x => g π Y γ w x R) h (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    have hcF := feas_between Y w θs θ' c R hc.1.le hc.2.le hFs hF'
    have hgc : g π Y γ w c R < 0 := by
      have := g_anti π Y γ w θs c R hπ hγ hi hRhi hc.1 hFs hcF
      linarith
    rw [eq_div_iff (by linarith)] at hcs
    nlinarith [mul_neg_of_neg_of_pos hgc (sub_pos.2 h)]

/-- A consumption level small enough that its marginal utility exceeds any bound. -/
theorem small_delta (A M γ : ℝ) (hA : 0 < A) (hM : 0 ≤ M) (hγ : 0 < γ) :
    ∃ δ, 0 < δ ∧ δ ≤ A ∧ M < δ ^ (-γ) := by
  set t := (1 / (M + 1)) ^ γ⁻¹ with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min A t, lt_min hA ht0, min_le_left _ _, ?_⟩
  have hd0 : 0 < min A t := lt_min hA ht0
  have hp : 0 < min A t ^ γ := Real.rpow_pos_of_pos hd0 _
  have h1 : min A t ^ γ ≤ 1 / (M + 1) := by
    calc min A t ^ γ ≤ t ^ γ := Real.rpow_le_rpow hd0.le (min_le_right _ _) hγ.le
      _ = 1 / (M + 1) := Real.rpow_inv_rpow (by positivity) hγ.ne'
  rw [le_div_iff₀ (by linarith)] at h1
  rw [Real.rpow_neg hd0.le, ← one_div, lt_div_iff₀ hp]
  nlinarith

/-- **A portfolio with a negative Euler expression**: hold so much equity that consumption in
the lowest state is tiny. -/
theorem exists_neg (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) : ∃ θ, Feas Y w θ R ∧ g π Y γ w θ R < 0 := by
  have hR0 : 0 < R * w := mul_pos (by linarith) hw
  set K := (R * w) ^ (-γ) * (Y hi - R) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hR0.le _) (by linarith)
  set P := ∑ s, π s with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun s _ => (hπ s).le
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta (R * w) (P * K / (π lo * (R - Y lo))) γ hR0
    (div_nonneg (mul_nonneg hP0 hK0) (mul_nonneg (hπ lo).le (by linarith))) hγ
  set θ := (R * w - δ) / (R - Y lo) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hclo : cons Y w θ R lo = δ := by
    unfold cons
    rw [hθ]
    field_simp
    ring
  have hF : Feas Y w θ R := fun s => by
    have : cons Y w θ R lo ≤ cons Y w θ R s := by
      unfold cons
      nlinarith [mul_le_mul_of_nonneg_left (hlo s) hθ0]
    linarith
  refine ⟨θ, hF, ?_⟩
  have hb : ∀ s, π s * cons Y w θ R s ^ (-γ) * (Y s - R) ≤ π s * K := by
    intro s
    rcases le_total (Y s) R with h | h
    · have : π s * cons Y w θ R s ^ (-γ) * (Y s - R) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (hπ s).le (Real.rpow_nonneg (hF s).le _)) (by linarith)
      linarith [mul_nonneg (hπ s).le hK0]
    · have hc : R * w ≤ cons Y w θ R s := by
        unfold cons
        nlinarith [mul_nonneg hθ0 (sub_nonneg.2 h)]
      have h1 : cons Y w θ R s ^ (-γ) ≤ (R * w) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos hR0 hc (by linarith)
      have h2 : cons Y w θ R s ^ (-γ) * (Y s - R) ≤ K :=
        mul_le_mul h1 (by linarith [hhi s]) (by linarith) (Real.rpow_nonneg hR0.le _)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (hπ s).le
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun s => π s * cons Y w θ R s ^ (-γ) * (Y s - R)) (Finset.mem_univ lo)
  have hrest : ∑ s ∈ Finset.univ.erase lo, π s * cons Y w θ R s ^ (-γ) * (Y s - R) ≤ P * K := by
    calc _ ≤ ∑ s ∈ Finset.univ.erase lo, π s * K := Finset.sum_le_sum fun s _ => hb s
      _ ≤ ∑ s, π s * K := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun s _ _ => mul_nonneg (hπ s).le hK0
      _ = P * K := by rw [hP, Finset.sum_mul]
  have hlot : π lo * cons Y w θ R lo ^ (-γ) * (Y lo - R) < -(P * K) := by
    rw [hclo]
    have hq : 0 < π lo * (R - Y lo) := mul_pos (hπ lo) (by linarith)
    rw [div_lt_iff₀ hq] at hδM
    nlinarith
  unfold g
  rw [← hsplit]
  linarith

/-- **A portfolio with a positive Euler expression**: short so much equity that consumption in
the highest state is tiny. -/
theorem exists_pos (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) : ∃ θ, Feas Y w θ R ∧ 0 < g π Y γ w θ R := by
  have hR0 : 0 < R * w := mul_pos (by linarith) hw
  set K := (R * w) ^ (-γ) * (R - Y lo) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hR0.le _) (by linarith)
  set P := ∑ s, π s with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun s _ => (hπ s).le
  obtain ⟨δ, hδ0, hδA, hδM⟩ := small_delta (R * w) (P * K / (π hi * (Y hi - R))) γ hR0
    (div_nonneg (mul_nonneg hP0 hK0) (mul_nonneg (hπ hi).le (by linarith))) hγ
  set θ := -((R * w - δ) / (Y hi - R)) with hθ
  have hθ0 : θ ≤ 0 := neg_nonpos.2 (div_nonneg (by linarith) (by linarith))
  have hchi : cons Y w θ R hi = δ := by
    unfold cons
    rw [hθ]
    field_simp
    ring
  have hF : Feas Y w θ R := fun s => by
    have : cons Y w θ R hi ≤ cons Y w θ R s := by
      unfold cons
      nlinarith [mul_le_mul_of_nonpos_left (hhi s) hθ0]
    linarith
  refine ⟨θ, hF, ?_⟩
  have hb : ∀ s, -(π s * K) ≤ π s * cons Y w θ R s ^ (-γ) * (Y s - R) := by
    intro s
    rcases le_total R (Y s) with h | h
    · have : 0 ≤ π s * cons Y w θ R s ^ (-γ) * (Y s - R) :=
        mul_nonneg (mul_nonneg (hπ s).le (Real.rpow_nonneg (hF s).le _)) (by linarith)
      linarith [mul_nonneg (hπ s).le hK0]
    · have hc : R * w ≤ cons Y w θ R s := by
        unfold cons
        nlinarith [mul_nonneg_of_nonpos_of_nonpos hθ0 (sub_nonpos.2 h)]
      have h1 : cons Y w θ R s ^ (-γ) ≤ (R * w) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos hR0 hc (by linarith)
      have h2 : cons Y w θ R s ^ (-γ) * (R - Y s) ≤ K :=
        mul_le_mul h1 (by linarith [hlo s]) (by linarith) (Real.rpow_nonneg hR0.le _)
      have h3 := mul_le_mul_of_nonneg_left h2 (hπ s).le
      nlinarith
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun s => π s * cons Y w θ R s ^ (-γ) * (Y s - R)) (Finset.mem_univ hi)
  have hrest : -(P * K) ≤ ∑ s ∈ Finset.univ.erase hi, π s * cons Y w θ R s ^ (-γ) * (Y s - R) := by
    have h1 : ∑ s ∈ Finset.univ.erase hi, π s * K ≤ P * K := by
      calc _ ≤ ∑ s, π s * K := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun s _ _ => mul_nonneg (hπ s).le hK0
        _ = P * K := by rw [hP, Finset.sum_mul]
    have h2 : ∑ s ∈ Finset.univ.erase hi, -(π s * K) ≤
        ∑ s ∈ Finset.univ.erase hi, π s * cons Y w θ R s ^ (-γ) * (Y s - R) :=
      Finset.sum_le_sum fun s _ => hb s
    rw [Finset.sum_neg_distrib] at h2
    linarith
  have hhit : P * K < π hi * cons Y w θ R hi ^ (-γ) * (Y hi - R) := by
    rw [hchi]
    have hq : 0 < π hi * (Y hi - R) := mul_pos (hπ hi) (by linarith)
    rw [div_lt_iff₀ hq] at hδM
    nlinarith
  unfold g
  rw [← hsplit]
  linarith

theorem g_contAt {X : Type*} [TopologicalSpace X] (π Y : S → ℝ) (γ w : ℝ) (θf Rf : X → ℝ)
    (x : X) (hθ : ContinuousAt θf x) (hR : ContinuousAt Rf x) (hF : Feas Y w (θf x) (Rf x)) :
    ContinuousAt (fun p => g π Y γ w (θf p) (Rf p)) x := by
  unfold g
  refine tendsto_finsetSum _ fun s _ => ?_
  have hc : ContinuousAt (fun p => cons Y w (θf p) (Rf p) s) x := by
    unfold cons
    exact (hR.mul continuousAt_const).add (hθ.mul (continuousAt_const.sub hR))
  exact (continuousAt_const.mul (hc.rpow_const (Or.inl (hF s).ne'))).mul
    (continuousAt_const.sub hR)

theorem feas_contAt {X : Type*} [TopologicalSpace X] (Y : S → ℝ) (w : ℝ) (θf Rf : X → ℝ)
    (x : X) (hθ : ContinuousAt θf x) (hR : ContinuousAt Rf x) (hF : Feas Y w (θf x) (Rf x)) :
    ∀ᶠ p in 𝓝 x, Feas Y w (θf p) (Rf p) := by
  refine Filter.eventually_all.2 fun s => ?_
  have hc : ContinuousAt (fun p => cons Y w (θf p) (Rf p) s) x := by
    unfold cons
    exact (hR.mul continuousAt_const).add (hθ.mul (continuousAt_const.sub hR))
  exact hc.eventually (lt_mem_nhds (hF s))

/-- **Each household has an optimal portfolio**: a zero of the Euler expression. -/
theorem exists_zero (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) : ∃ θ, Feas Y w θ R ∧ g π Y γ w θ R = 0 := by
  obtain ⟨θh, hFh, hgh⟩ := exists_neg π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  obtain ⟨θl, hFl, hgl⟩ := exists_pos π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  have hle : θl ≤ θh := by
    by_contra hlt
    push Not at hlt
    have := g_anti π Y γ w θh θl R hπ hγ hi hR' hlt hFh hFl
    linarith
  have hcont : ContinuousOn (fun θ => g π Y γ w θ R) (Icc θl θh) := fun x hx =>
    (g_contAt π Y γ w id (fun _ => R) x continuousAt_id continuousAt_const
      (feas_between Y w θl θh x R hx.1 hx.2 hFl hFh)).continuousWithinAt
  obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' hle hcont ⟨hgh.le, hgl.le⟩
  exact ⟨θ, feas_between Y w θl θh θ R hθ.1 hθ.2 hFl hFh, hθ0⟩

/-- The optimal equity position (the unique zero of the Euler expression). -/
def dem (π Y : S → ℝ) (γ w R : ℝ) : ℝ :=
  if h : ∃ θ, Feas Y w θ R ∧ g π Y γ w θ R = 0 then Classical.choose h else 0

theorem dem_spec (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) :
    Feas Y w (dem π Y γ w R) R ∧ g π Y γ w (dem π Y γ w R) R = 0 := by
  have h := exists_zero π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  unfold dem
  split_ifs
  exact Classical.choose_spec h

/-- If `θ` is affordable and the Euler expression is positive there, then `θ < dem`; if it is
negative, `dem < θ`. -/
theorem dem_side (π Y : S → ℝ) (γ w R θ : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) (hF : Feas Y w θ R) :
    (0 < g π Y γ w θ R → θ < dem π Y γ w R) ∧ (g π Y γ w θ R < 0 → dem π Y γ w R < θ) := by
  obtain ⟨hFd, hgd⟩ := dem_spec π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  constructor
  · intro hg
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := g_anti π Y γ w _ _ R hπ hγ hi hR' hlt hFd hF
      linarith
    · rw [heq] at hgd
      linarith
  · intro hg
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := g_anti π Y γ w _ _ R hπ hγ hi hR' hlt hF hFd
      linarith
    · rw [← heq] at hgd
      linarith

/-- **The optimal portfolio is continuous in the bond return.** -/
theorem dem_continuous (π Y : S → ℝ) (γ w R0 : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R0)
    (hR' : R0 < Y hi) (hY0 : 0 < Y lo) :
    ContinuousAt (fun R => dem π Y γ w R) R0 := by
  obtain ⟨hF0, hg0⟩ := dem_spec π Y γ w R0 hπ hγ lo hi hlo hhi hw hR hR' hY0
  set θ0 := dem π Y γ w R0 with hθ0
  have hev := feas_contAt Y w id (fun _ => R0) θ0 continuousAt_id continuousAt_const hF0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hIoo : ∀ᶠ R in 𝓝 R0, R ∈ Ioo (Y lo) (Y hi) := Ioo_mem_nhds hR hR'
  -- at a fixed affordable `p`, the sign of the Euler expression persists near `R0`
  have persist : ∀ p, Feas Y w p R0 →
      (0 < g π Y γ w p R0 → ∀ᶠ R in 𝓝 R0, p < dem π Y γ w R) ∧
      (g π Y γ w p R0 < 0 → ∀ᶠ R in 𝓝 R0, dem π Y γ w R < p) := by
    intro p hp
    have hF := feas_contAt Y w (fun _ => p) id R0 continuousAt_const continuousAt_id hp
    have hc := g_contAt π Y γ w (fun _ => p) id R0 continuousAt_const continuousAt_id hp
    constructor
    · intro hpos
      filter_upwards [hF, hc.eventually (lt_mem_nhds hpos), hIoo] with R h1 h2 h3
      exact (dem_side π Y γ w R p hπ hγ lo hi hlo hhi hw h3.1 h3.2 hY0 h1).1 h2
    · intro hneg
      filter_upwards [hF, hc.eventually (gt_mem_nhds hneg), hIoo] with R h1 h2 h3
      exact (dem_side π Y γ w R p hπ hγ lo hi hlo hhi hw h3.1 h3.2 hY0 h1).2 h2
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set p := max ((a + θ0) / 2) (θ0 - ε / 2) with hp
    have hpa : a < p := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hpθ : p < θ0 := max_lt (by linarith) (by linarith)
    have hpF : Feas Y w p R0 := hball (by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right ((a + θ0) / 2) (θ0 - ε / 2)
      linarith)
    have hgp : 0 < g π Y γ w p R0 := by
      have := g_anti π Y γ w p θ0 R0 hπ hγ hi hR' hpθ hpF hF0
      linarith
    filter_upwards [(persist p hpF).1 hgp] with R hR
    linarith
  · set p := min ((b + θ0) / 2) (θ0 + ε / 2) with hp
    have hpb : p < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hpθ : θ0 < p := lt_min (by linarith) (by linarith)
    have hpF : Feas Y w p R0 := hball (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_right ((b + θ0) / 2) (θ0 + ε / 2)
      linarith)
    have hgp : g π Y γ w p R0 < 0 := by
      have := g_anti π Y γ w θ0 p R0 hπ hγ hi hR' hpθ hF0 hpF
      linarith
    filter_upwards [(persist p hpF).2 hgp] with R hR
    linarith

/-! ## The tilted mean and the sign of excess demand -/

def num (π Y : S → ℝ) (γ : ℝ) : ℝ := ∑ s, π s * Y s ^ (-γ) * Y s

def den (π Y : S → ℝ) (γ : ℝ) : ℝ := ∑ s, π s * Y s ^ (-γ)

/-- The tilted mean `E[Y ^ (1 − γ)] / E[Y ^ (−γ)]`. -/
def tm (π Y : S → ℝ) (γ : ℝ) : ℝ := num π Y γ / den π Y γ

theorem den_pos (π Y : S → ℝ) (γ : ℝ) (hπ : ∀ s, 0 < π s) (lo : S) (hlo : ∀ s, Y lo ≤ Y s)
    (hY0 : 0 < Y lo) : 0 < den π Y γ :=
  Finset.sum_pos (fun s _ => mul_pos (hπ s) (Real.rpow_pos_of_pos (by linarith [hlo s]) _))
    ⟨lo, Finset.mem_univ _⟩

theorem tilted_mem (π Y : S → ℝ) (γ : ℝ) (hπ : ∀ s, 0 < π s) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hlh : Y lo < Y hi) (hY0 : 0 < Y lo) :
    Y lo < tm π Y γ ∧ tm π Y γ < Y hi := by
  have hD := den_pos π Y γ hπ lo hlo hY0
  have hw : ∀ s, 0 < π s * Y s ^ (-γ) := fun s =>
    mul_pos (hπ s) (Real.rpow_pos_of_pos (by linarith [hlo s]) _)
  unfold tm
  constructor
  · rw [lt_div_iff₀ hD, den, Finset.mul_sum]
    exact Finset.sum_lt_sum (fun s _ => by nlinarith [hw s, hlo s])
      ⟨hi, Finset.mem_univ _, by nlinarith [hw hi]⟩
  · rw [div_lt_iff₀ hD, den, Finset.mul_sum]
    exact Finset.sum_lt_sum (fun s _ => by nlinarith [hw s, hhi s])
      ⟨lo, Finset.mem_univ _, by nlinarith [hw lo]⟩

theorem g_at_w (π Y : S → ℝ) (γ w R : ℝ) (hw : 0 < w) (lo : S) (hlo : ∀ s, Y lo ≤ Y s)
    (hY0 : 0 < Y lo) :
    g π Y γ w w R = w ^ (-γ) * (num π Y γ - R * den π Y γ) := by
  unfold g num den
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : cons Y w w R s = w * Y s := by unfold cons; ring
  rw [e, Real.mul_rpow hw.le (by linarith [hlo s])]
  ring

omit [Fintype S] in
theorem feas_w (Y : S → ℝ) (w R : ℝ) (hw : 0 < w) (lo : S) (hlo : ∀ s, Y lo ≤ Y s)
    (hY0 : 0 < Y lo) : Feas Y w w R := fun s => by
  have e : cons Y w w R s = w * Y s := by unfold cons; ring
  rw [e]
  exact mul_pos hw (by linarith [hlo s])

/-- Below its tilted mean a household holds at least its endowment of equity. -/
theorem w_le_dem (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) (hm : R ≤ tm π Y γ) : w ≤ dem π Y γ w R := by
  obtain ⟨hFd, hgd⟩ := dem_spec π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  have hD := den_pos π Y γ hπ lo hlo hY0
  have hg : 0 ≤ g π Y γ w w R := by
    rw [g_at_w π Y γ w R hw lo hlo hY0]
    unfold tm at hm
    rw [le_div_iff₀ hD] at hm
    exact mul_nonneg (Real.rpow_nonneg hw.le _) (by linarith)
  by_contra hlt
  push Not at hlt
  have := g_anti π Y γ w _ _ R hπ hγ hi hR' hlt hFd (feas_w Y w R hw lo hlo hY0)
  linarith

/-- Above its tilted mean a household holds at most its endowment of equity. -/
theorem dem_le_w (π Y : S → ℝ) (γ w R : ℝ) (hπ : ∀ s, 0 < π s) (hγ : 0 < γ) (lo hi : S)
    (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi) (hw : 0 < w) (hR : Y lo < R)
    (hR' : R < Y hi) (hY0 : 0 < Y lo) (hm : tm π Y γ ≤ R) : dem π Y γ w R ≤ w := by
  obtain ⟨hFd, hgd⟩ := dem_spec π Y γ w R hπ hγ lo hi hlo hhi hw hR hR' hY0
  have hD := den_pos π Y γ hπ lo hlo hY0
  have hg : g π Y γ w w R ≤ 0 := by
    rw [g_at_w π Y γ w R hw lo hlo hY0]
    unfold tm at hm
    rw [div_le_iff₀ hD] at hm
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hw.le _) (by linarith)
  by_contra hlt
  push Not at hlt
  have := g_anti π Y γ w _ _ R hπ hγ hi hR' hlt (feas_w Y w R hw lo hlo hY0) hFd
  linarith

/-! ## Existence of equilibrium -/

/-- **Existence of the equity-and-bond equilibrium** with heterogeneous CRRA households. Equity
has price one and the bond price `1 / R`; household `i` holds `θ i` units of equity and `b i`
bonds. -/
theorem exists_equilibrium {I : Type*} [Fintype I] [Nonempty I] (π Y : S → ℝ)
    (hπ : ∀ s, 0 < π s) (lo hi : S) (hlo : ∀ s, Y lo ≤ Y s) (hhi : ∀ s, Y s ≤ Y hi)
    (hlh : Y lo < Y hi) (hY0 : 0 < Y lo) (w γ : I → ℝ) (hw : ∀ i, 0 < w i)
    (hγ : ∀ i, 0 < γ i) (u : I → ℝ → ℝ)
    (hu : ∀ i c, 0 < c → HasDerivAt (u i) (c ^ (-γ i)) c) :
    ∃ (R : ℝ) (θ b : I → ℝ), Y lo < R ∧ R < Y hi ∧
      (∀ i, θ i + R⁻¹ * b i = w i) ∧ (∀ i s, 0 < θ i * Y s + b i) ∧
      (∀ i θ' b', θ' + R⁻¹ * b' = w i → (∀ s, 0 < θ' * Y s + b') →
        ∑ s, π s * u i (θ' * Y s + b') ≤ ∑ s, π s * u i (θ i * Y s + b i)) ∧
      ∑ i, θ i = ∑ i, w i ∧ ∑ i, b i = 0 := by
  set m : I → ℝ := fun i => tm π Y (γ i) with hm
  set mlo := Finset.univ.inf' Finset.univ_nonempty m with hmlo
  set mhi := Finset.univ.sup' Finset.univ_nonempty m with hmhi
  obtain ⟨ilo, -, hilo⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty m
  obtain ⟨ihi, -, hihi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty m
  have hmem : ∀ i, Y lo < m i ∧ m i < Y hi := fun i =>
    tilted_mem π Y (γ i) hπ lo hi hlo hhi hlh hY0
  have hlo_le : ∀ i, mlo ≤ m i := fun i => Finset.inf'_le m (Finset.mem_univ i)
  have hhi_ge : ∀ i, m i ≤ mhi := fun i => Finset.le_sup' m (Finset.mem_univ i)
  have hle : mlo ≤ mhi := (hlo_le ilo).trans (hhi_ge ilo)
  have hin : ∀ R ∈ Icc mlo mhi, Y lo < R ∧ R < Y hi := fun R hR =>
    ⟨lt_of_lt_of_le (by rw [hmlo, hilo]; exact (hmem ilo).1) hR.1,
      lt_of_le_of_lt hR.2 (by rw [hmhi, hihi]; exact (hmem ihi).2)⟩
  set Z : ℝ → ℝ := fun R => ∑ i, (dem π Y (γ i) (w i) R - w i) with hZ
  have hZc : ContinuousOn Z (Icc mlo mhi) := by
    intro R hR
    have h : ContinuousAt Z R := by
      rw [hZ]
      exact tendsto_finsetSum _ fun i _ => (dem_continuous π Y (γ i) (w i) R hπ (hγ i) lo hi
        hlo hhi (hw i) (hin R hR).1 (hin R hR).2 hY0).sub continuousAt_const
    exact h.continuousWithinAt
  have hZlo : 0 ≤ Z mlo := Finset.sum_nonneg fun i _ => sub_nonneg.2
    (w_le_dem π Y (γ i) (w i) mlo hπ (hγ i) lo hi hlo hhi (hw i)
      (hin mlo ⟨le_rfl, hle⟩).1 (hin mlo ⟨le_rfl, hle⟩).2 hY0 (hlo_le i))
  have hZhi : Z mhi ≤ 0 := Finset.sum_nonpos fun i _ => sub_nonpos.2
    (dem_le_w π Y (γ i) (w i) mhi hπ (hγ i) lo hi hlo hhi (hw i)
      (hin mhi ⟨hle, le_rfl⟩).1 (hin mhi ⟨hle, le_rfl⟩).2 hY0 (hhi_ge i))
  obtain ⟨R, hRI, hZR⟩ := intermediate_value_Icc' hle hZc ⟨hZhi, hZlo⟩
  obtain ⟨hR1, hR2⟩ := hin R hRI
  have hR0 : 0 < R := by linarith
  set θ : I → ℝ := fun i => dem π Y (γ i) (w i) R with hθ
  have hspec := fun i => dem_spec π Y (γ i) (w i) R hπ (hγ i) lo hi hlo hhi (hw i) hR1 hR2 hY0
  have hcons : ∀ i (θ' b' : ℝ), θ' + R⁻¹ * b' = w i → ∀ s,
      θ' * Y s + b' = cons Y (w i) θ' R s := by
    intro i θ' b' hb s
    have : b' = R * (w i - θ') := by
      field_simp at hb
      linarith
    unfold cons
    rw [this]
    ring
  have hbud : ∀ i, θ i + R⁻¹ * (R * (w i - θ i)) = w i := fun i => by
    field_simp
    ring
  refine ⟨R, θ, fun i => R * (w i - θ i), hR1, hR2, hbud, fun i s => ?_, ?_, ?_, ?_⟩
  · rw [hcons i _ _ (hbud i) s]
    exact (hspec i).1 s
  · intro i θ' b' hb hpos
    have e1 : ∀ s, θ' * Y s + b' = cons Y (w i) θ' R s := hcons i θ' b' hb
    have e2 : ∀ s, θ i * Y s + R * (w i - θ i) = cons Y (w i) (θ i) R s :=
      hcons i _ _ (hbud i)
    simp only [e1, e2]
    exact optimal π Y (γ i) (w i) R (θ i) θ' (u i) (hu i) hπ (hγ i) hi hR2 (hspec i).1
      (hspec i).2 fun s => by rw [← e1 s]; exact hpos s
  · have : ∑ i, (θ i - w i) = 0 := hZR
    rw [Finset.sum_sub_distrib] at this
    linarith
  · have : ∑ i, (θ i - w i) = 0 := hZR
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib] at this
    rw [show ∑ i, w i - ∑ i, θ i = 0 by linarith, mul_zero]

end IncompleteExistence

end

#print axioms IncompleteExistence.g_anti
#print axioms IncompleteExistence.optimal
#print axioms IncompleteExistence.small_delta
#print axioms IncompleteExistence.exists_neg
#print axioms IncompleteExistence.exists_pos
#print axioms IncompleteExistence.exists_zero
#print axioms IncompleteExistence.dem_continuous
#print axioms IncompleteExistence.tilted_mem
#print axioms IncompleteExistence.w_le_dem
#print axioms IncompleteExistence.dem_le_w
#print axioms IncompleteExistence.exists_equilibrium
