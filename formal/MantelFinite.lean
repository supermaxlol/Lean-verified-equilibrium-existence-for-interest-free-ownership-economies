import Mathlib

/-!
Stage 296: Mantel with continuous preferences on any finite set of prices.

Given finitely many distinct, strictly positive, normalised price vectors and any excess
demands satisfying Walras' law at them, there are as many consumers as goods, each with a
continuous, concave, strictly monotone utility over net trades, whose optimal net trades at
those prices add up to the given excess demands.

* `afriat_*` — Afriat utilities `min_k (-T k + L * T k * p_k · y)`: continuous, concave,
  strictly monotone; they rationalise any data with a strict potential.
* `afriat_potential` — data whose revealed preference is ordered by a strict potential can
  be rationalised by such a utility.
* `mantel_finite` — the decomposition (Debreu's directions `e_i - p_i p`) plus a potential
  `p ↦ p_i` for each consumer.
-/

noncomputable section

open Finset Filter Topology

namespace MantelFinite

variable {S O : Type*} [Fintype S] [Fintype O]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- Afriat utility. -/
def afriat [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L : ℝ) (y : S → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun k => -T k + L * T k * dot (p k) y)

theorem dot_affine (p y z : S → ℝ) (a b : ℝ) :
    dot p (a • y + b • z) = a * dot p y + b * dot p z := by
  unfold dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem afriat_continuous [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L : ℝ) :
    Continuous (afriat p T L) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  unfold afriat
  refine ContinuousAt.finset_inf'_apply univ_nonempty fun k _ => ?_
  have : Continuous fun y : S → ℝ => -T k + L * T k * dot (p k) y := by
    unfold dot
    fun_prop
  exact this.continuousAt

theorem afriat_concave [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L : ℝ) :
    ConcaveOn ℝ Set.univ (afriat p T L) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => -T k + L * T k * dot (p k) (a • y + b • z))
  have h1 : afriat p T L y ≤ -T k + L * T k * dot (p k) y :=
    Finset.inf'_le (fun k => -T k + L * T k * dot (p k) y) (mem_univ k)
  have h2 : afriat p T L z ≤ -T k + L * T k * dot (p k) z :=
    Finset.inf'_le (fun k => -T k + L * T k * dot (p k) z) (mem_univ k)
  have e : afriat p T L (a • y + b • z) = -T k + L * T k * (a * dot (p k) y + b * dot (p k) z) := by
    unfold afriat
    rw [hk, dot_affine]
  rw [e, smul_eq_mul, smul_eq_mul]
  have h3 := mul_le_mul_of_nonneg_left h1 ha
  have h4 := mul_le_mul_of_nonneg_left h2 hb
  have e2 : a * (-T k + L * T k * dot (p k) y) + b * (-T k + L * T k * dot (p k) z) =
      -T k + L * T k * (a * dot (p k) y + b * dot (p k) z) := by
    linear_combination (-T k) * hab
  linarith

theorem afriat_strictMono [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L : ℝ)
    (hp : ∀ k s, 0 < p k s) (hTL : ∀ k, 0 < L * T k) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) : afriat p T L y < afriat p T L z := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => -T k + L * T k * dot (p k) z)
  have h1 : afriat p T L y ≤ -T k + L * T k * dot (p k) y :=
    Finset.inf'_le (fun k => -T k + L * T k * dot (p k) y) (mem_univ k)
  have hd : dot (p k) y < dot (p k) z := by
    unfold dot
    obtain ⟨s0, hs0⟩ := hlt
    exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hyz s) (hp k s).le)
      ⟨s0, mem_univ _, mul_lt_mul_of_pos_left hs0 (hp k s0)⟩
  have h2 := mul_lt_mul_of_pos_left hd (hTL k)
  have e : afriat p T L z = -T k + L * T k * dot (p k) z := by unfold afriat; rw [hk]
  rw [e]
  linarith

/-- **Afriat's construction with a strict potential.** -/
theorem afriat_potential [Nonempty O] (p : O → S → ℝ) (x : O → S → ℝ) (h : O → ℝ)
    (hp : ∀ k s, 0 < p k s) (hx : ∀ k, dot (p k) (x k) = 0)
    (hpot : ∀ k l, k ≠ l → dot (p k) (x l) ≤ 0 → h k < h l) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ k y, dot (p k) y ≤ 0 → u y ≤ u (x k) := by
  set a : O → O → ℝ := fun k l => dot (p k) (x l) with ha
  set g : O → O → ℝ := fun k l => if 0 < a k l then 1 / a k l else 0 with hg
  have hg0 : ∀ k l, 0 ≤ g k l := by
    intro k l
    simp only [hg]
    split_ifs with hh
    · exact (one_div_pos.2 hh).le
    · exact le_rfl
  set L : ℝ := 1 + ∑ k, ∑ l, g k l with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ∑ k, ∑ l, g k l :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hg0 k l
    linarith
  have hLa : ∀ k l, 0 < a k l → 1 ≤ L * a k l := by
    intro k l hpos
    have h1 : g k l ≤ ∑ l', g k l' :=
      Finset.single_le_sum (f := fun l' => g k l') (fun l' _ => hg0 k l') (mem_univ l)
    have h2 : ∑ l', g k l' ≤ ∑ k', ∑ l', g k' l' :=
      Finset.single_le_sum (f := fun k' => ∑ l', g k' l')
        (fun k' _ => Finset.sum_nonneg fun l' _ => hg0 k' l') (mem_univ k)
    have h3 : g k l = 1 / a k l := by simp only [hg]; rw [ite_eq_left_of_eq_true _ _ (eq_true hpos)]
    have h4 : 1 / a k l ≤ L := by linarith
    have := mul_le_mul_of_nonneg_right h4 hpos.le
    rwa [one_div_mul_cancel hpos.ne'] at this
  have hev : ∀ k l, ∀ᶠ θ in atTop,
      (k ≠ l → a k l ≤ 0 → 1 + L * (-a k l) ≤ Real.exp (θ * (h l - h k))) := by
    intro k l
    by_cases hc : k ≠ l ∧ a k l ≤ 0
    · have hlt : 0 < h l - h k := sub_pos.2 (hpot k l hc.1 hc.2)
      have ht : Tendsto (fun θ : ℝ => Real.exp (θ * (h l - h k))) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hlt)
      exact (ht.eventually_ge_atTop _).mono fun θ hθ _ _ => hθ
    · exact Filter.Eventually.of_forall fun θ h1 h2 => absurd ⟨h1, h2⟩ hc
  obtain ⟨θ, hθ⟩ := (Filter.eventually_all.2 fun k => Filter.eventually_all.2 (hev k)).exists
  set T : O → ℝ := fun k => Real.exp (θ * h k) with hT
  have hTpos : ∀ k, 0 < T k := fun k => Real.exp_pos _
  have hA : ∀ k l, -T l ≤ -T k + L * T k * a k l := by
    intro k l
    by_cases hpos : 0 < a k l
    · have h1 := hLa k l hpos
      have h2 : T k ≤ L * T k * a k l := by nlinarith [hTpos k]
      linarith [hTpos l]
    · replace hpos := not_lt.1 hpos
      by_cases hkl : k = l
      · subst hkl
        have : a k k = 0 := hx k
        rw [this, mul_zero, add_zero]
      · have h1 := hθ k l hkl hpos
        have h2 : T l = T k * Real.exp (θ * (h l - h k)) := by
          simp only [hT]
          rw [← Real.exp_add]
          congr 1
          ring
        have h3 := mul_le_mul_of_nonneg_left h1 (hTpos k).le
        rw [← h2] at h3
        have h4 : T k * (1 + L * -a k l) = T k - L * T k * a k l := by ring
        linarith
  refine ⟨afriat p T L, afriat_continuous p T L, afriat_concave p T L,
    afriat_strictMono p T L hp (fun k => mul_pos (by linarith) (hTpos k)), fun k y hy => ?_⟩
  have hxk : afriat p T L (x k) = -T k := by
    apply le_antisymm
    · have := Finset.inf'_le (fun j => -T j + L * T j * dot (p j) (x k)) (mem_univ k)
      rw [hx k, mul_zero, add_zero] at this
      exact this
    · exact Finset.le_inf' _ _ fun j _ => hA j k
  rw [hxk]
  have h1 : afriat p T L y ≤ -T k + L * T k * dot (p k) y :=
    Finset.inf'_le (fun j => -T j + L * T j * dot (p j) y) (mem_univ k)
  have h2 : L * T k * dot (p k) y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_pos (by linarith) (hTpos k)).le hy
  linarith

variable [DecidableEq S]

/-- Debreu's direction for consumer `i` at prices `p`. -/
def mdir (p : O → S → ℝ) (i : S) (k : O) (s : S) : ℝ := (if s = i then 1 else 0) - p k i * p k s

/-- Debreu's scale for consumer `i`. -/
def mcoef (p Z : O → S → ℝ) (c : ℝ) (i : S) (k : O) : ℝ := Z k i + c * p k i

omit [Fintype O] in
theorem dot_mdir (p : O → S → ℝ) (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (i : S) (k : O) :
    dot (p k) (mdir p i k) = 0 := by
  unfold dot mdir
  have e : ∀ s, p k s * ((if s = i then 1 else 0) - p k i * p k s) =
      (if s = i then p k s else 0) - p k i * p k s ^ 2 := by
    intro s
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, hunit k]
  ring

/-- **Mantel's theorem on finite price sets, with continuous preferences.** -/
theorem mantel_finite [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ (u : S → (S → ℝ) → ℝ) (x : S → O → S → ℝ),
      (∀ i, Continuous (u i)) ∧ (∀ i, ConcaveOn ℝ Set.univ (u i)) ∧
      (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u i y < u i z) ∧
      (∀ i k, dot (p k) (x i k) = 0) ∧
      (∀ i k y, dot (p k) y ≤ 0 → u i y ≤ u i (x i k)) ∧
      (∀ k s, ∑ i, x i k s = Z k s) := by
  set c : ℝ := 1 + ∑ k, ∑ i, |Z k i| / p k i with hc
  have hα : ∀ i k, 0 < mcoef p Z c i k := by
    intro i k
    have h1 : |Z k i| / p k i ≤ ∑ i', |Z k i'| / p k i' :=
      Finset.single_le_sum (f := fun i' => |Z k i'| / p k i')
        (fun i' _ => div_nonneg (abs_nonneg _) (hp k i').le) (mem_univ i)
    have h2 : ∑ i', |Z k i'| / p k i' ≤ ∑ k', ∑ i', |Z k' i'| / p k' i' :=
      Finset.single_le_sum (f := fun k' => ∑ i', |Z k' i'| / p k' i')
        (fun k' _ => Finset.sum_nonneg fun i' _ => div_nonneg (abs_nonneg _) (hp k' i').le)
        (mem_univ k)
    have h3 : |Z k i| / p k i ≤ c - 1 := by linarith
    have h4 : |Z k i| ≤ (c - 1) * p k i := (div_le_iff₀ (hp k i)).1 h3
    have h5 : (c - 1) * p k i = c * p k i - p k i := by ring
    have h6 := neg_abs_le (Z k i)
    unfold mcoef
    linarith [hp k i]
  set x : S → O → S → ℝ := fun i k s => mcoef p Z c i k * mdir p i k s with hx
  have hbud : ∀ i k, dot (p k) (x i k) = 0 := by
    intro i k
    have e : dot (p k) (x i k) = mcoef p Z c i k * dot (p k) (mdir p i k) := by
      simp only [hx, dot]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, dot_mdir p hunit, mul_zero]
  have hagg : ∀ k s, ∑ i, x i k s = Z k s := by
    intro k s
    have e1 : ∑ i, x i k s =
        ∑ i, (if s = i then mcoef p Z c i k else 0) - p k s * ∑ i, mcoef p Z c i k * p k i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hx, mdir]
      split_ifs <;> ring
    have e2 : ∑ i, mcoef p Z c i k * p k i = c := by
      unfold mcoef
      have a1 : ∑ i, (Z k i + c * p k i) * p k i =
          ∑ i, p k i * Z k i + c * ∑ i, p k i ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have := hW k
      unfold dot at this
      rw [a1, this, hunit k]
      ring
    rw [e1, e2, Finset.sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true (mem_univ s))]
    unfold mcoef
    ring
  have hpot : ∀ i k l, k ≠ l → dot (p k) (x i l) ≤ 0 → p k i < p l i := by
    intro i k l hkl hle
    set C := ∑ s, p k s * p l s with hC
    obtain ⟨s0, hs0⟩ : ∃ s, p k s ≠ p l s := by
      by_contra hcon
      exact hkl (hinj (funext fun s => not_not.1 fun hne => hcon ⟨s, hne⟩))
    have hpos : 0 < ∑ s, (p k s - p l s) ^ 2 :=
      Finset.sum_pos' (fun s _ => sq_nonneg _)
        ⟨s0, mem_univ _, lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hs0)))⟩
    have hexp : ∑ s, (p k s - p l s) ^ 2 = 2 - 2 * C := by
      have e : ∀ s, (p k s - p l s) ^ 2 = p k s ^ 2 + p l s ^ 2 - 2 * (p k s * p l s) :=
        fun s => by ring
      simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hunit]
      ring
    have hC1 : C < 1 := by linarith
    have hd : dot (p k) (x i l) = mcoef p Z c i l * (p k i - p l i * C) := by
      have e : ∀ s, p k s * (mcoef p Z c i l * ((if s = i then 1 else 0) - p l i * p l s)) =
          mcoef p Z c i l * ((if s = i then p k s else 0) - p l i * (p k s * p l s)) := by
        intro s
        split_ifs <;> ring
      simp only [dot, hx, mdir, e, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rw [← hC]
    rw [hd] at hle
    have h1 : p k i - p l i * C ≤ 0 := by
      by_contra hcon
      have := mul_pos (hα i l) (not_le.1 hcon)
      linarith
    have h2 : p l i * C < p l i := mul_lt_of_lt_one_right (hp l i) hC1
    linarith
  have hA := fun i => afriat_potential p (x i) (fun k => p k i) hp (hbud i) (hpot i)
  choose u hu using hA
  exact ⟨u, x, fun i => (hu i).1, fun i => (hu i).2.1, fun i => (hu i).2.2.1, hbud,
    fun i => (hu i).2.2.2, hagg⟩

end MantelFinite

end

#print axioms MantelFinite.dot_affine
#print axioms MantelFinite.afriat_continuous
#print axioms MantelFinite.afriat_concave
#print axioms MantelFinite.afriat_strictMono
#print axioms MantelFinite.afriat_potential
#print axioms MantelFinite.dot_mdir
#print axioms MantelFinite.mantel_finite
