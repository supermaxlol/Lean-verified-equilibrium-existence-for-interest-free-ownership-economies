import Mathlib

/-!
Stage 300: Mantel on finite price sets with strictly concave utilities and unique demand.

Stage 296 used Afriat utilities, which are concave but piecewise linear, so demand need not be
unique.  Here each Afriat piece gets a strictly concave correction
`δ * (ψ y - ψ (x k) - ∇ψ (x k) · (y - x k))` with `ψ y = ∑ s, -exp (-y s)`.  The correction
vanishes at `x k` and is negative elsewhere, so each data point stays optimal and becomes the
*unique* optimum; the minimum of strictly concave pieces is strictly concave.  `δ` is chosen
small (filter argument as `δ → 0⁺`) so monotonicity and the Afriat inequalities survive; this
needs a strict Afriat margin, which a larger exponent supplies.
-/

noncomputable section

open Finset Filter Topology

namespace MantelStrict

variable {S O : Type*} [Fintype S] [Fintype O]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

theorem dot_affine (p y z : S → ℝ) (a b : ℝ) :
    dot p (a • y + b • z) = a * dot p y + b * dot p z := by
  unfold dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Strictly concave, strictly increasing correction. -/
def psi (y : S → ℝ) : ℝ := ∑ s, -Real.exp (-y s)

/-- Its gradient. -/
def G (x : S → ℝ) (s : S) : ℝ := Real.exp (-x s)

/-- Bregman-type gap: `ψ y` minus its tangent at `x`. -/
def brk (x y : S → ℝ) : ℝ := psi y - psi x - (dot (G x) y - dot (G x) x)

theorem exp_sg (a b : ℝ) : -Real.exp (-b) ≤ -Real.exp (-a) + Real.exp (-a) * (b - a) := by
  have h1 := Real.add_one_le_exp (-(b - a))
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a)).le
  rw [h2]
  nlinarith [h3]

theorem exp_sg_strict (a b : ℝ) (h : a ≠ b) :
    -Real.exp (-b) < -Real.exp (-a) + Real.exp (-a) * (b - a) := by
  have h1 := Real.add_one_lt_exp (show -(b - a) ≠ 0 by intro hh; apply h; linarith)
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 := mul_lt_mul_of_pos_left h1 (Real.exp_pos (-a))
  rw [h2]
  nlinarith [h3]

omit [Fintype S] in
theorem brk_eq [Fintype S] (x y : S → ℝ) :
    brk x y = ∑ s, (-Real.exp (-y s) - (-Real.exp (-x s) + Real.exp (-x s) * (y s - x s))) := by
  unfold brk psi dot G
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem brk_le (x y : S → ℝ) : brk x y ≤ 0 := by
  rw [brk_eq]
  exact Finset.sum_nonpos fun s _ => by linarith [exp_sg (x s) (y s)]

theorem brk_lt (x y : S → ℝ) (hne : y ≠ x) : brk x y < 0 := by
  obtain ⟨s0, hs0⟩ := Function.ne_iff.1 hne
  rw [brk_eq]
  have := Finset.sum_lt_sum (s := univ)
    (f := fun s => -Real.exp (-y s) - (-Real.exp (-x s) + Real.exp (-x s) * (y s - x s)))
    (g := fun _ => (0 : ℝ)) (fun s _ => by linarith [exp_sg (x s) (y s)])
    ⟨s0, mem_univ _, by linarith [exp_sg_strict (x s0) (y s0) (Ne.symm hs0)]⟩
  rw [Finset.sum_const_zero] at this
  exact this

theorem brk_self (x : S → ℝ) : brk x x = 0 := by unfold brk; ring

theorem psi_mono (y z : S → ℝ) (hyz : ∀ s, y s ≤ z s) : psi y ≤ psi z := by
  unfold psi
  exact Finset.sum_le_sum fun s _ => by
    have := Real.exp_le_exp.2 (neg_le_neg (hyz s))
    linarith

theorem psi_strict (a b : S → ℝ) (hab : a ≠ b) (t r : ℝ) (ht : 0 < t) (hr : 0 < r)
    (htr : t + r = 1) : t * psi a + r * psi b < psi (t • a + r • b) := by
  obtain ⟨s0, hs0⟩ := Function.ne_iff.1 hab
  have e : ∀ s, -(t • a + r • b) s = t • -a s + r • -b s := fun s => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc : ∀ s, t * -Real.exp (-a s) + r * -Real.exp (-b s) ≤
      -Real.exp (-(t • a + r • b) s) := by
    intro s
    have := convexOn_exp.2 (Set.mem_univ (-a s)) (Set.mem_univ (-b s)) ht.le hr.le htr
    rw [e s]
    simp only [smul_eq_mul] at this ⊢
    linarith
  have hs : t * -Real.exp (-a s0) + r * -Real.exp (-b s0) <
      -Real.exp (-(t • a + r • b) s0) := by
    have := strictConvexOn_exp.2 (Set.mem_univ (-a s0)) (Set.mem_univ (-b s0))
      (by intro hh; apply hs0; linarith) ht hr htr
    rw [e s0]
    simp only [smul_eq_mul] at this ⊢
    linarith
  unfold psi
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_lt_sum (fun s _ => hc s) ⟨s0, mem_univ _, hs⟩

/-- One corrected Afriat piece. -/
def gp (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (k : O) (y : S → ℝ) : ℝ :=
  U k + lam k * (dot (p k) y - dot (p k) (x k)) + δ * brk (x k) y

/-- Corrected Afriat utility. -/
def su [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (y : S → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun k => gp U lam p x δ k y)

theorem su_continuous [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) :
    Continuous (su U lam p x δ) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  unfold su
  refine ContinuousAt.finset_inf'_apply univ_nonempty fun k _ => ?_
  have : Continuous fun y : S → ℝ => gp U lam p x δ k y := by
    unfold gp brk psi dot G
    fun_prop
  exact this.continuousAt

theorem su_strictConcave [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    StrictConcaveOn ℝ Set.univ (su U lam p x δ) := by
  refine ⟨convex_univ, fun a _ b _ hab t r ht hr htr => ?_⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => gp U lam p x δ k (t • a + r • b))
  have h1 : su U lam p x δ a ≤ gp U lam p x δ k a :=
    Finset.inf'_le (fun k => gp U lam p x δ k a) (mem_univ k)
  have h2 : su U lam p x δ b ≤ gp U lam p x δ k b :=
    Finset.inf'_le (fun k => gp U lam p x δ k b) (mem_univ k)
  have hm : su U lam p x δ (t • a + r • b) = gp U lam p x δ k (t • a + r • b) := by
    unfold su; exact hk
  have key : t * gp U lam p x δ k a + r * gp U lam p x δ k b +
      δ * (psi (t • a + r • b) - t * psi a - r * psi b) = gp U lam p x δ k (t • a + r • b) := by
    unfold gp brk
    rw [dot_affine, dot_affine]
    linear_combination (U k - lam k * dot (p k) (x k) - δ * psi (x k) +
      δ * dot (G (x k)) (x k)) * htr
  have hps := psi_strict a b hab t r ht hr htr
  have h3 := mul_le_mul_of_nonneg_left h1 ht.le
  have h4 := mul_le_mul_of_nonneg_left h2 hr.le
  have h5 := mul_pos hδ (by linarith : 0 < psi (t • a + r • b) - t * psi a - r * psi b)
  rw [smul_eq_mul, smul_eq_mul, hm]
  linarith

theorem su_strictMono [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlam : ∀ k s, δ * G (x k) s < lam k * p k s) (y z : S → ℝ)
    (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) : su U lam p x δ y < su U lam p x δ z := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => gp U lam p x δ k z)
  have h1 : su U lam p x δ y ≤ gp U lam p x δ k y :=
    Finset.inf'_le (fun k => gp U lam p x δ k y) (mem_univ k)
  have hm : su U lam p x δ z = gp U lam p x δ k z := by unfold su; exact hk
  have hlin : 0 < lam k * (dot (p k) z - dot (p k) y) - δ * (dot (G (x k)) z - dot (G (x k)) y) := by
    have e : lam k * (dot (p k) z - dot (p k) y) - δ * (dot (G (x k)) z - dot (G (x k)) y) =
        ∑ s, (lam k * p k s - δ * G (x k) s) * (z s - y s) := by
      unfold dot
      rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    obtain ⟨s0, hs0⟩ := hlt
    exact Finset.sum_pos' (fun s _ => mul_nonneg (by linarith [hlam k s]) (by linarith [hyz s]))
      ⟨s0, mem_univ _, mul_pos (by linarith [hlam k s0]) (by linarith)⟩
  have hps := mul_nonneg hδ (sub_nonneg.2 (psi_mono y z hyz))
  have e2 : gp U lam p x δ k z - gp U lam p x δ k y =
      (lam k * (dot (p k) z - dot (p k) y) - δ * (dot (G (x k)) z - dot (G (x k)) y)) +
        δ * (psi z - psi y) := by
    unfold gp brk; ring
  rw [hm]
  linarith

omit [Fintype O] in
theorem gp_self (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (k : O) :
    gp U lam p x δ k (x k) = U k := by
  unfold gp; rw [brk_self]; ring

theorem su_at [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ)
    (hA : ∀ k l, U k ≤ gp U lam p x δ l (x k)) (k : O) : su U lam p x δ (x k) = U k := by
  apply le_antisymm
  · have := Finset.inf'_le (fun j => gp U lam p x δ j (x k)) (mem_univ k)
    rw [gp_self] at this
    exact this
  · exact Finset.le_inf' _ _ fun l _ => hA k l

theorem su_unique_opt [Nonempty O] (U lam : O → ℝ) (p x : O → S → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (k : O) (hlam : 0 ≤ lam k) (hx : dot (p k) (x k) = 0) (y : S → ℝ) (hy : dot (p k) y ≤ 0) :
    su U lam p x δ y ≤ U k ∧ (y ≠ x k → su U lam p x δ y < U k) := by
  have h1 : su U lam p x δ y ≤ gp U lam p x δ k y :=
    Finset.inf'_le (fun j => gp U lam p x δ j y) (mem_univ k)
  have h2 : lam k * (dot (p k) y - dot (p k) (x k)) ≤ 0 := by
    rw [hx, sub_zero]; exact mul_nonpos_of_nonneg_of_nonpos hlam hy
  have e : gp U lam p x δ k y = U k + lam k * (dot (p k) y - dot (p k) (x k)) +
      δ * brk (x k) y := rfl
  refine ⟨?_, fun hne => ?_⟩
  · have := mul_nonpos_of_nonneg_of_nonpos hδ.le (brk_le (x k) y)
    linarith
  · have := mul_neg_of_pos_of_neg hδ (brk_lt (x k) y hne)
    linarith

omit [Fintype O] in
/-- **Strict Afriat construction with a strict potential.** -/
theorem afriat_strict [Fintype O] [Nonempty O] (p : O → S → ℝ) (x : O → S → ℝ) (h : O → ℝ)
    (hp : ∀ k s, 0 < p k s) (hx : ∀ k, dot (p k) (x k) = 0)
    (hpot : ∀ k l, k ≠ l → dot (p k) (x l) ≤ 0 → h k < h l) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ StrictConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      (∀ k y, dot (p k) y ≤ 0 → u y ≤ u (x k)) ∧
      (∀ k y, dot (p k) y ≤ 0 → y ≠ x k → u y < u (x k)) := by
  set a : O → O → ℝ := fun k l => dot (p k) (x l) with ha
  set g : O → O → ℝ := fun k l => if 0 < a k l then 1 / a k l else 0 with hg
  have hg0 : ∀ k l, 0 ≤ g k l := by
    intro k l
    simp only [hg]
    split_ifs with hh
    · exact (one_div_pos.2 hh).le
    · exact le_rfl
  set L : ℝ := 2 * (1 + ∑ k, ∑ l, g k l) with hL
  have hsum0 : 0 ≤ ∑ k, ∑ l, g k l :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hg0 k l
  have hL0 : 0 < L := by linarith
  have hLa : ∀ k l, 0 < a k l → 2 ≤ L * a k l := by
    intro k l hpos
    have h1 : g k l ≤ ∑ l', g k l' :=
      Finset.single_le_sum (f := fun l' => g k l') (fun l' _ => hg0 k l') (mem_univ l)
    have h2 : ∑ l', g k l' ≤ ∑ k', ∑ l', g k' l' :=
      Finset.single_le_sum (f := fun k' => ∑ l', g k' l')
        (fun k' _ => Finset.sum_nonneg fun l' _ => hg0 k' l') (mem_univ k)
    have h3 : g k l = 1 / a k l := by
      simp only [hg]; rw [ite_eq_left_of_eq_true _ _ (eq_true hpos)]
    have h4 : 1 / a k l ≤ L / 2 := by linarith
    have := mul_le_mul_of_nonneg_right h4 hpos.le
    rw [one_div_mul_cancel hpos.ne'] at this
    linarith
  have hev : ∀ k l, ∀ᶠ θ in atTop,
      (k ≠ l → a k l ≤ 0 → 2 + L * (-a k l) ≤ Real.exp (θ * (h l - h k))) := by
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
  -- strict Afriat margin: `-T l + T k ≤ -T k + L T k a k l` for `k ≠ l`
  have hA : ∀ k l, k ≠ l → -T l + T k ≤ -T k + L * T k * a k l := by
    intro k l hkl
    by_cases hpos : 0 < a k l
    · have h1 := hLa k l hpos
      have h2 : 2 * T k ≤ L * T k * a k l := by nlinarith [hTpos k]
      linarith [hTpos l]
    · replace hpos := not_lt.1 hpos
      have h1 := hθ k l hkl hpos
      have h2 : T l = T k * Real.exp (θ * (h l - h k)) := by
        simp only [hT]
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 := mul_le_mul_of_nonneg_left h1 (hTpos k).le
      rw [← h2] at h3
      have h4 : T k * (2 + L * -a k l) = 2 * T k - L * T k * a k l := by ring
      linarith
  -- choose `δ → 0⁺`
  have hδev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧
      (∀ k l, δ * |brk (x k) (x l)| < T k) ∧ (∀ k s, δ * G (x k) s < L * T k * p k s) := by
    have lim : ∀ c : ℝ, Tendsto (fun δ : ℝ => δ * c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro c
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const c
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have e1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k l : O, δ * |brk (x k) (x l)| < T k :=
      (Filter.eventually_all (ι := O)).2 fun k => (Filter.eventually_all (ι := O)).2 fun l =>
        (lim |brk (x k) (x l)|).eventually_lt_const (hTpos k)
    have e2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ (k : O) (s : S), δ * G (x k) s < L * T k * p k s :=
      (Filter.eventually_all (ι := O)).2 fun k => (Filter.eventually_all (ι := S)).2 fun s =>
        (lim (G (x k) s)).eventually_lt_const (mul_pos (mul_pos hL0 (hTpos k)) (hp k s))
    have e0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    exact e0.and (e1.and e2)
  obtain ⟨δ, hδ0, hδb, hδG⟩ := hδev.exists
  set U : O → ℝ := fun k => -T k with hU
  set lam : O → ℝ := fun k => L * T k with hlam
  have hAf : ∀ k l, U k ≤ gp U lam p x δ l (x k) := by
    intro k l
    by_cases hkl : l = k
    · subst hkl; rw [gp_self]
    · have h1 := hA l k hkl
      have h2 : -(δ * |brk (x l) (x k)|) ≤ δ * brk (x l) (x k) := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_abs_le _) hδ0.le
      have h3 := hδb l k
      have e : gp U lam p x δ l (x k) = -T l + L * T l * a l k + δ * brk (x l) (x k) := by
        simp only [gp, hU, hlam, ha, hx l, sub_zero]
      rw [e]
      show -T k ≤ _
      linarith
  have hsu := su_at U lam p x δ hAf
  refine ⟨su U lam p x δ, su_continuous U lam p x δ, su_strictConcave U lam p x δ hδ0,
    su_strictMono U lam p x δ hδ0.le hδG, fun k y hy => ?_, fun k y hy hne => ?_⟩
  · rw [hsu k]
    exact (su_unique_opt U lam p x δ hδ0 k (mul_pos hL0 (hTpos k)).le (hx k) y hy).1
  · rw [hsu k]
    exact (su_unique_opt U lam p x δ hδ0 k (mul_pos hL0 (hTpos k)).le (hx k) y hy).2 hne

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

/-- **Mantel on finite price sets: strictly concave utilities, unique optimal demand.** -/
theorem mantel_strict [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ (u : S → (S → ℝ) → ℝ) (x : S → O → S → ℝ),
      (∀ i, Continuous (u i)) ∧ (∀ i, StrictConcaveOn ℝ Set.univ (u i)) ∧
      (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u i y < u i z) ∧
      (∀ i k, dot (p k) (x i k) = 0) ∧
      (∀ i k y, dot (p k) y ≤ 0 → u i y ≤ u i (x i k)) ∧
      (∀ i k y, dot (p k) y ≤ 0 → y ≠ x i k → u i y < u i (x i k)) ∧
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
  have hA := fun i => afriat_strict p (x i) (fun k => p k i) hp (hbud i) (hpot i)
  choose u hu using hA
  exact ⟨u, x, fun i => (hu i).1, fun i => (hu i).2.1, fun i => (hu i).2.2.1, hbud,
    fun i => (hu i).2.2.2.1, fun i => (hu i).2.2.2.2, hagg⟩

end MantelStrict

end

#print axioms MantelStrict.psi_strict
#print axioms MantelStrict.brk_lt
#print axioms MantelStrict.su_continuous
#print axioms MantelStrict.su_strictConcave
#print axioms MantelStrict.su_strictMono
#print axioms MantelStrict.su_unique_opt
#print axioms MantelStrict.afriat_strict
#print axioms MantelStrict.mantel_strict
