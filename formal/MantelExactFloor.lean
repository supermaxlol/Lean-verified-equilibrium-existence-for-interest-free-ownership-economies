import Mathlib

/-!
Stage 337 (extends stages 332–333): consumer-specific endowment floors.

Stage 333 asked every endowment coordinate to be at least the uniform bound `Mbd p Z`. That is
more than the construction uses. Only nonnegative consumption is needed, so the floor that
matters is `e_i s ≥ −mx_i(p_k) s` for every price `k`.

* `mantel_exact_floor` — under the consumer-specific floors `−mx p Z i k s ≤ e i s`, the given `Z`
  (scale `1`) is the aggregate excess demand of unique maximisers of continuous, concave,
  strictly monotone utilities, with nonnegative consumption.
* `floor_of_Mbd` — the stage-333 floor implies these floors, so this strictly extends stage 333.
* `floor_sum_ge` — summed over consumers, the floors still dominate the necessary aggregate
  floor `−Z k s ≤ ∑_i e_i s` of `unscaled_impossible`.

Scope: what remains of the gap between the two conditions is the gap between
`∑_i max_k (−mx_i(p_k) s)` and `max_k (−Z k s)`. That gap is specific to Debreu's
one-consumer-per-good decomposition. Whether another decomposition reaches the aggregate floor
is not settled here.

Stage 332–333 description follows.

Stages 332–333 (extend stage 329): an explicit endowment bound, and when no rescaling is needed.

* `mx`, `cZ`, `Mbd` — the net trades of stage 326 written out, and the explicit number
  `Mbd p Z = 1 + ∑ₖ∑ᵢ |Z k i| / p k i + ∑ₖ∑ᵢ |Z k i|`, computed from `Z` and `p` alone.
* `mx_bound` (332) — every net-trade coordinate has absolute value at most `Mbd p Z`.
* `mantel_explicit_endow` (332) — stage 329 with `M := Mbd p Z` stated explicitly.
* `mantel_unscaled` (333) — if every endowment coordinate is at least `Mbd p Z`, the given
  excess demands `Z` themselves (scale `1`) are the aggregate of unique utility-maximising demands.
* `excess_lower`, `unscaled_impossible` (333) — conversely, if `Z k s < -∑ᵢ eᵢ s` for some
  price and good, no nonnegative allocation has aggregate excess demand `Z k` at all.
  The two conditions leave a gap: the sufficient one is a per-consumer floor `Mbd`, the
  necessary one an aggregate floor `-Z`; this file does not close that gap.

Stage 329 (extends stage 326): endowments.  Consumer `i` has endowment `e_i` (every
coordinate at least `λ M`) and consumption utility `c ↦ u_i((c − e_i)/λ)`, still continuous,
concave and strictly monotone; demand `e_i + λ x_i` is unique on `p·c ≤ p·e_i`, consumption is
nonnegative, and aggregate excess demand is `λ Z` (`mantel_finite_endow`).

Stage 326: stage 296 with unique demand.

Copy of stage 296 (`MantelFinite`) extended so that each consumer's assigned net trade is the
unique maximiser of a continuous, concave, strictly monotone utility on its budget set
(`afriat_unique`, `mantel_finite_unique`). The Afriat utility is built from strict
Afriat inequalities and perturbed by a small strictly concave Bregman-type penalty
`ε ∑ₛ bg (y s) (x k s)`, which vanishes exactly at the observed bundle.

Original stage-296 description:

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

namespace MantelExactFloor

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

/-! ### Unique demand: strict Afriat inequalities plus a Bregman penalty -/

/-- Bregman-type penalty: `0` at `t = a`, strictly negative elsewhere, concave in `t`. -/
def bg (t a : ℝ) : ℝ := Real.exp (-a) - Real.exp (-t) - Real.exp (-a) * (t - a)

theorem bg_self (a : ℝ) : bg a a = 0 := by unfold bg; ring

theorem bg_nonpos (t a : ℝ) : bg t a ≤ 0 := by
  have h1 := Real.add_one_le_exp (a - t)
  have h2 : Real.exp (-t) = Real.exp (-a) * Real.exp (a - t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a)).le
  unfold bg
  nlinarith [h2, h3]

theorem bg_neg (t a : ℝ) (h : t ≠ a) : bg t a < 0 := by
  have h1 := Real.add_one_lt_exp (sub_ne_zero.2 h.symm)
  have h2 : Real.exp (-t) = Real.exp (-a) * Real.exp (a - t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 := mul_lt_mul_of_pos_left h1 (Real.exp_pos (-a))
  unfold bg
  nlinarith [h2, h3]

theorem bg_concave (t t' c a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * bg t c + b * bg t' c ≤ bg (a * t + b * t') c := by
  have h := convexOn_exp.2 (Set.mem_univ (-t)) (Set.mem_univ (-t')) ha hb hab
  simp only [smul_eq_mul] at h
  have e : a * -t + b * -t' = -(a * t + b * t') := by ring
  rw [e] at h
  obtain rfl : b = 1 - a := by linarith
  unfold bg
  nlinarith [h]

theorem step_le (q a ε t t' : ℝ) (hε : 0 ≤ ε) (hq : ε * Real.exp (-a) ≤ q) (htt : t ≤ t') :
    q * t + ε * bg t a ≤ q * t' + ε * bg t' a := by
  have he : Real.exp (-t') ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have h1 := mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 htt)
  have h2 := mul_nonneg hε (sub_nonneg.2 he)
  unfold bg
  nlinarith [h1, h2]

theorem step_lt (q a ε t t' : ℝ) (hε : 0 ≤ ε) (hq : ε * Real.exp (-a) < q) (htt : t < t') :
    q * t + ε * bg t a < q * t' + ε * bg t' a := by
  have he : Real.exp (-t') ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
  have h1 := mul_pos (sub_pos.2 hq) (sub_pos.2 htt)
  have h2 := mul_nonneg hε (sub_nonneg.2 he)
  unfold bg
  nlinarith [h1, h2]

/-- Perturbed Afriat piece for observation `k`. -/
def pc (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (x : O → S → ℝ) (k : O) (y : S → ℝ) : ℝ :=
  -T k + L * T k * dot (p k) y + ε * ∑ s, bg (y s) (x k s)

omit [Fintype O] in
theorem pc_sum (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (x : O → S → ℝ) (k : O) (y : S → ℝ) :
    pc p T L ε x k y = -T k + ∑ s, (L * T k * p k s * y s + ε * bg (y s) (x k s)) := by
  unfold pc dot
  rw [Finset.mul_sum, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype O] in
theorem pc_continuous (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (x : O → S → ℝ) (k : O) :
    Continuous fun y => pc p T L ε x k y := by
  unfold pc dot bg
  fun_prop

omit [Fintype O] in
theorem pc_concave (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (hε : 0 ≤ ε) (x : O → S → ℝ)
    (k : O) (y z : S → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * pc p T L ε x k y + b * pc p T L ε x k z ≤ pc p T L ε x k (a • y + b • z) := by
  have hs : a * ∑ s, bg (y s) (x k s) + b * ∑ s, bg (z s) (x k s) ≤
      ∑ s, bg ((a • y + b • z) s) (x k s) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact bg_concave _ _ _ a b ha hb hab
  have hε' := mul_le_mul_of_nonneg_left hs hε
  unfold pc
  rw [dot_affine]
  have e2 : a * (-T k + L * T k * dot (p k) y) + b * (-T k + L * T k * dot (p k) z) =
      -T k + L * T k * (a * dot (p k) y + b * dot (p k) z) := by
    linear_combination (-T k) * hab
  nlinarith [hε', e2]

omit [Fintype O] in
theorem pc_strictMono (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (hε : 0 ≤ ε)
    (x : O → S → ℝ) (k : O) (hsmall : ∀ s, ε * Real.exp (-x k s) < L * T k * p k s)
    (y z : S → ℝ) (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) :
    pc p T L ε x k y < pc p T L ε x k z := by
  rw [pc_sum, pc_sum]
  obtain ⟨s0, hs0⟩ := hlt
  have := Finset.sum_lt_sum (s := univ)
    (f := fun s => L * T k * p k s * y s + ε * bg (y s) (x k s))
    (g := fun s => L * T k * p k s * z s + ε * bg (z s) (x k s))
    (fun s _ => step_le (L * T k * p k s) (x k s) ε (y s) (z s) hε (hsmall s).le (hyz s))
    ⟨s0, mem_univ _, step_lt _ _ ε _ _ hε (hsmall s0) hs0⟩
  linarith

/-- Perturbed Afriat utility. -/
def au [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (x : O → S → ℝ) (y : S → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun k => pc p T L ε x k y)

theorem au_continuous [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (x : O → S → ℝ) :
    Continuous (au p T L ε x) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  unfold au
  refine ContinuousAt.finset_inf'_apply univ_nonempty fun k _ => ?_
  exact (pc_continuous p T L ε x k).continuousAt

theorem au_concave [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (hε : 0 ≤ ε)
    (x : O → S → ℝ) : ConcaveOn ℝ Set.univ (au p T L ε x) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => pc p T L ε x k (a • y + b • z))
  have h1 : au p T L ε x y ≤ pc p T L ε x k y :=
    Finset.inf'_le (fun k => pc p T L ε x k y) (mem_univ k)
  have h2 : au p T L ε x z ≤ pc p T L ε x k z :=
    Finset.inf'_le (fun k => pc p T L ε x k z) (mem_univ k)
  have e : au p T L ε x (a • y + b • z) = pc p T L ε x k (a • y + b • z) := by
    unfold au; rw [hk]
  rw [e, smul_eq_mul, smul_eq_mul]
  have h3 := mul_le_mul_of_nonneg_left h1 ha
  have h4 := mul_le_mul_of_nonneg_left h2 hb
  have := pc_concave p T L ε hε x k y z a b ha hb hab
  linarith

theorem au_strictMono [Nonempty O] (p : O → S → ℝ) (T : O → ℝ) (L ε : ℝ) (hε : 0 ≤ ε)
    (x : O → S → ℝ) (hsmall : ∀ k s, ε * Real.exp (-x k s) < L * T k * p k s)
    (y z : S → ℝ) (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) :
    au p T L ε x y < au p T L ε x z := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := O))
    (fun k => pc p T L ε x k z)
  have h1 : au p T L ε x y ≤ pc p T L ε x k y :=
    Finset.inf'_le (fun k => pc p T L ε x k y) (mem_univ k)
  have h2 := pc_strictMono p T L ε hε x k (hsmall k) y z hyz hlt
  have e : au p T L ε x z = pc p T L ε x k z := by unfold au; rw [hk]
  rw [e]
  linarith

/-- **Strict Afriat inequalities** from a strict potential. -/
theorem strict_afriat (p : O → S → ℝ) (x : O → S → ℝ) (h : O → ℝ)
    (hpot : ∀ k l, k ≠ l → dot (p k) (x l) ≤ 0 → h k < h l) :
    ∃ (L : ℝ) (T : O → ℝ), 0 < L ∧ (∀ k, 0 < T k) ∧
      ∀ k l, k ≠ l → -T l < -T k + L * T k * dot (p k) (x l) := by
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
      (k ≠ l → a k l ≤ 0 → 1 + L * (-a k l) < Real.exp (θ * (h l - h k))) := by
    intro k l
    by_cases hc : k ≠ l ∧ a k l ≤ 0
    · have hlt : 0 < h l - h k := sub_pos.2 (hpot k l hc.1 hc.2)
      have ht : Tendsto (fun θ : ℝ => Real.exp (θ * (h l - h k))) atTop atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hlt)
      exact (ht.eventually_gt_atTop _).mono fun θ hθ _ _ => hθ
    · exact Filter.Eventually.of_forall fun θ h1 h2 => absurd ⟨h1, h2⟩ hc
  obtain ⟨θ, hθ⟩ := (Filter.eventually_all.2 fun k => Filter.eventually_all.2 (hev k)).exists
  set T : O → ℝ := fun k => Real.exp (θ * h k) with hT
  have hTpos : ∀ k, 0 < T k := fun k => Real.exp_pos _
  refine ⟨L, T, by linarith, hTpos, fun k l hkl => ?_⟩
  show -T l < -T k + L * T k * a k l
  by_cases hpos : 0 < a k l
  · have h1 := hLa k l hpos
    have h2 : T k ≤ L * T k * a k l := by nlinarith [hTpos k]
    linarith [hTpos l]
  · replace hpos := not_lt.1 hpos
    have h1 := hθ k l hkl hpos
    have h2 : T l = T k * Real.exp (θ * (h l - h k)) := by
      simp only [hT]
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 := mul_lt_mul_of_pos_left h1 (hTpos k)
    rw [← h2] at h3
    have h4 : T k * (1 + L * -a k l) = T k - L * T k * a k l := by ring
    linarith

theorem ev_small (c d : ℝ) (hd : 0 < d) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * c < d := by
  have ht : Tendsto (fun ε : ℝ => ε * c) (𝓝 0) (𝓝 (0 * c)) :=
    (continuous_id.mul continuous_const).tendsto 0
  rw [zero_mul] at ht
  exact (ht.eventually (gt_mem_nhds hd)).filter_mono nhdsWithin_le_nhds

/-- **Afriat with unique demand.** Data with a strict potential is rationalised by a
continuous, concave, strictly monotone utility for which each observed bundle is the
*unique* optimum on its budget set. -/
theorem afriat_unique [Nonempty O] (p x : O → S → ℝ) (h : O → ℝ)
    (hp : ∀ k s, 0 < p k s) (hx : ∀ k, dot (p k) (x k) = 0)
    (hpot : ∀ k l, k ≠ l → dot (p k) (x l) ≤ 0 → h k < h l) :
    ∃ u : (S → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ Set.univ u ∧
      (∀ y z : S → ℝ, (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z) ∧
      ∀ k y, dot (p k) y ≤ 0 → y ≠ x k → u y < u (x k) := by
  obtain ⟨L, T, hL, hT, hA⟩ := strict_afriat p x h hpot
  have hC1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k s, ε * Real.exp (-x k s) < L * T k * p k s :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun s =>
      ev_small _ _ (mul_pos (mul_pos hL (hT k)) (hp k s))
  have hC2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k l, k ≠ l →
      ε * (-∑ s, bg (x l s) (x k s)) < -T k + L * T k * dot (p k) (x l) + T l := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ?_
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall fun ε hne => absurd hkl hne
    · exact (ev_small _ _ (by linarith [hA k l hkl])).mono fun ε hε _ => hε
  obtain ⟨ε, ⟨hεpos, hs1⟩, hs2⟩ := ((eventually_mem_nhdsWithin.and hC1).and hC2).exists
  have hε : 0 < ε := hεpos
  have hself : ∀ k, pc p T L ε x k (x k) = -T k := by
    intro k
    unfold pc
    rw [hx k]
    simp only [bg_self, Finset.sum_const_zero, mul_zero, add_zero]
  have hxk : ∀ k, au p T L ε x (x k) = -T k := by
    intro k
    apply le_antisymm
    · exact (Finset.inf'_le (fun j => pc p T L ε x j (x k)) (mem_univ k)).trans_eq (hself k)
    · refine Finset.le_inf' _ _ fun j _ => ?_
      by_cases hjk : j = k
      · rw [hjk, hself k]
      · have h1 := hs2 j k hjk
        unfold pc
        linarith
  refine ⟨au p T L ε x, au_continuous p T L ε x, au_concave p T L ε hε.le x,
    au_strictMono p T L ε hε.le x hs1, fun k y hy hne => ?_⟩
  rw [hxk k]
  have h1 : au p T L ε x y ≤ pc p T L ε x k y :=
    Finset.inf'_le (fun j => pc p T L ε x j y) (mem_univ k)
  obtain ⟨s0, hs0⟩ : ∃ s, y s ≠ x k s := by
    by_contra hcon
    exact hne (funext fun s => not_not.1 fun h' => hcon ⟨s, h'⟩)
  have hlt := Finset.sum_lt_sum (s := univ) (f := fun s => bg (y s) (x k s))
    (g := fun _ => (0 : ℝ)) (fun s _ => bg_nonpos _ _) ⟨s0, mem_univ _, bg_neg _ _ hs0⟩
  have hneg : ∑ s, bg (y s) (x k s) < 0 := lt_of_lt_of_eq hlt Finset.sum_const_zero
  have h2 : L * T k * dot (p k) y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_pos hL (hT k)).le hy
  have h3 : ε * ∑ s, bg (y s) (x k s) < 0 := mul_neg_of_pos_of_neg hε hneg
  unfold pc at h1
  linarith

variable [DecidableEq S]

/-- Debreu's direction for consumer `i` at prices `p`. -/
def mdir (p : O → S → ℝ) (i : S) (k : O) (s : S) : ℝ := (if s = i then 1 else 0) - p k i * p k s

/-- Debreu's scale for consumer `i`. -/
def mcoef (p Z : O → S → ℝ) (c : ℝ) (i : S) (k : O) : ℝ := Z k i + c * p k i

/-- The constant of stage 326. -/
def cZ (p Z : O → S → ℝ) : ℝ := 1 + ∑ k, ∑ i, |Z k i| / p k i

/-- The net trades of stage 326, written out. -/
def mx (p Z : O → S → ℝ) (i : S) (k : O) (s : S) : ℝ := mcoef p Z (cZ p Z) i k * mdir p i k s

/-- **The explicit bound**, a function of `Z` and `p` only. -/
def Mbd (p Z : O → S → ℝ) : ℝ := cZ p Z + ∑ k, ∑ i, |Z k i|

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


/-- **Mantel on finite price sets with unique demand.** As stage 296, and in addition each
consumer's assigned net trade is the *unique* utility maximiser on its budget set. -/
theorem mantel_finite_unique [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ (u : S → (S → ℝ) → ℝ) (x : S → O → S → ℝ), x = mx p Z ∧
      (∀ i, Continuous (u i)) ∧ (∀ i, ConcaveOn ℝ Set.univ (u i)) ∧
      (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u i y < u i z) ∧
      (∀ i k, dot (p k) (x i k) = 0) ∧
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
  have hA := fun i => afriat_unique p (x i) (fun k => p k i) hp (hbud i) (hpot i)
  choose u hu using hA
  exact ⟨u, x, rfl, fun i => (hu i).1, fun i => (hu i).2.1, fun i => (hu i).2.2.1, hbud,
    fun i => (hu i).2.2.2, hagg⟩


/-! ### Stage 329: endowments -/

/-- Utility over consumption bundles: the trade utility of `(c − e)/λ`. -/
def eu (u : (S → ℝ) → ℝ) (e : S → ℝ) (lam : ℝ) (c : S → ℝ) : ℝ :=
  u (fun s => (c s - e s) / lam)

omit [Fintype S] [Fintype O] [DecidableEq S] in
theorem eu_continuous (u : (S → ℝ) → ℝ) (e : S → ℝ) (lam : ℝ) (hu : Continuous u) :
    Continuous (eu u e lam) :=
  hu.comp (by fun_prop)

omit [Fintype S] [Fintype O] [DecidableEq S] in
theorem eu_concave (u : (S → ℝ) → ℝ) (e : S → ℝ) (lam : ℝ) (hu : ConcaveOn ℝ Set.univ u) :
    ConcaveOn ℝ Set.univ (eu u e lam) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  have key : (fun s => ((a • y + b • z) s - e s) / lam) =
      a • (fun s => (y s - e s) / lam) + b • (fun s => (z s - e s) / lam) := by
    funext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h : a * y s + b * z s - e s = a * (y s - e s) + b * (z s - e s) := by
      linear_combination (e s) * hab
    rw [h]
    ring
  show a • u (fun s => (y s - e s) / lam) + b • u (fun s => (z s - e s) / lam) ≤
    u (fun s => ((a • y + b • z) s - e s) / lam)
  rw [key]
  exact hu.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

omit [Fintype S] [Fintype O] [DecidableEq S] in
theorem eu_strictMono (u : (S → ℝ) → ℝ) (e : S → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hu : ∀ (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) → u y < u z)
    (y z : S → ℝ) (hyz : ∀ s, y s ≤ z s) (hlt : ∃ s, y s < z s) : eu u e lam y < eu u e lam z := by
  obtain ⟨s0, hs0⟩ := hlt
  exact hu _ _ (fun s => div_le_div_of_nonneg_right (sub_le_sub_right (hyz s) _) hlam.le)
    ⟨s0, div_lt_div_of_pos_right (sub_lt_sub_right hs0 _) hlam⟩

omit [Fintype O] [DecidableEq S] in
theorem dot_shift (p e x : S → ℝ) (lam : ℝ) :
    dot p (fun s => e s + lam * x s) = dot p e + lam * dot p x := by
  unfold dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype O] [DecidableEq S] in
theorem dot_scale (p c e : S → ℝ) (lam : ℝ) :
    dot p (fun s => (c s - e s) / lam) = (dot p c - dot p e) / lam := by
  unfold dot
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype O] [DecidableEq S] in
/-- **Transfer to consumption.**  A trade utility with unique optimal trades `x` gives a
consumption utility with unique optimal consumption `e + λ x` on the budget `p·c ≤ p·e`. -/
theorem endow_transfer (p : O → S → ℝ) (u : (S → ℝ) → ℝ) (x : O → S → ℝ) (e : S → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (hb : ∀ k, dot (p k) (x k) = 0)
    (hopt : ∀ k y, dot (p k) y ≤ 0 → y ≠ x k → u y < u (x k)) (k : O) :
    dot (p k) (fun s => e s + lam * x k s) = dot (p k) e ∧
      ∀ c, dot (p k) c ≤ dot (p k) e → c ≠ (fun s => e s + lam * x k s) →
        eu u e lam c < eu u e lam (fun s => e s + lam * x k s) := by
  refine ⟨by rw [dot_shift, hb k, mul_zero, add_zero], fun c hc hne => ?_⟩
  have hback : (fun s => ((e s + lam * x k s) - e s) / lam) = x k := by
    funext s
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hlam.ne']
  have hy : dot (p k) (fun s => (c s - e s) / lam) ≤ 0 := by
    rw [dot_scale]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
  have hne' : (fun s => (c s - e s) / lam) ≠ x k := by
    intro h
    apply hne
    funext s
    have h1 := congrFun h s
    rw [div_eq_iff hlam.ne'] at h1
    linarith [mul_comm (x k s) lam]
  unfold eu
  rw [hback]
  exact hopt k _ hy hne'

omit [Fintype O] [DecidableEq S] in
theorem p_le_one (p : O → S → ℝ) (_hp : ∀ k s, 0 < p k s) (hunit : ∀ k, ∑ s, p k s ^ 2 = 1)
    (k : O) (s : S) : p k s ≤ 1 := by
  have h : p k s ^ 2 ≤ 1 := by
    rw [← hunit k]
    exact Finset.single_le_sum (f := fun s' => p k s' ^ 2) (fun _ _ => sq_nonneg _) (mem_univ s)
  nlinarith

omit [Fintype O] in
theorem mdir_abs (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s) (hunit : ∀ k, ∑ s, p k s ^ 2 = 1)
    (i : S) (k : O) (s : S) : |mdir p i k s| ≤ 1 := by
  have h1 := p_le_one p hp hunit k i
  have h2 := p_le_one p hp hunit k s
  have h3 : 0 < p k i * p k s := mul_pos (hp k i) (hp k s)
  have h4 : p k i * p k s ≤ 1 := by nlinarith [hp k i, hp k s]
  unfold mdir
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

omit [DecidableEq S] in
theorem cZ_ge (p Z : O → S → ℝ) (hp : ∀ k s, 0 < p k s) : 1 ≤ cZ p Z := by
  unfold cZ
  have : 0 ≤ ∑ k, ∑ i, |Z k i| / p k i :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hp k i).le
  linarith

omit [DecidableEq S] in
theorem Z_le_sum (Z : O → S → ℝ) (k : O) (i : S) : |Z k i| ≤ ∑ k', ∑ i', |Z k' i'| :=
  (Finset.single_le_sum (f := fun i' => |Z k i'|) (fun _ _ => abs_nonneg _) (mem_univ i)).trans
    (Finset.single_le_sum (f := fun k' => ∑ i', |Z k' i'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ k))

omit [DecidableEq S] in
theorem mcoef_abs (p Z : O → S → ℝ) (hp : ∀ k s, 0 < p k s) (hunit : ∀ k, ∑ s, p k s ^ 2 = 1)
    (i : S) (k : O) : |mcoef p Z (cZ p Z) i k| ≤ |Z k i| + cZ p Z := by
  have hc := cZ_ge p Z hp
  have h1 := p_le_one p hp hunit k i
  have hz1 := neg_abs_le (Z k i)
  have hz2 := le_abs_self (Z k i)
  have hcp : cZ p Z * p k i ≤ cZ p Z := mul_le_of_le_one_right (by linarith) h1
  have hcp0 : 0 < cZ p Z * p k i := mul_pos (by linarith) (hp k i)
  unfold mcoef
  rw [abs_le]
  constructor <;> linarith

/-- **Stage 332: explicit bound.** Every coordinate of every net trade of stage 326 has
absolute value at most `Mbd p Z`. -/
theorem mx_bound (p Z : O → S → ℝ) (hp : ∀ k s, 0 < p k s) (hunit : ∀ k, ∑ s, p k s ^ 2 = 1)
    (i : S) (k : O) (s : S) : |mx p Z i k s| ≤ Mbd p Z := by
  have hZ := Z_le_sum Z k i
  unfold mx
  rw [abs_mul]
  calc |mcoef p Z (cZ p Z) i k| * |mdir p i k s| ≤ |mcoef p Z (cZ p Z) i k| * 1 :=
        mul_le_mul_of_nonneg_left (mdir_abs p hp hunit i k s) (abs_nonneg _)
    _ = |mcoef p Z (cZ p Z) i k| := mul_one _
    _ ≤ |Z k i| + cZ p Z := mcoef_abs p Z hp hunit i k
    _ ≤ Mbd p Z := by unfold Mbd; linarith

omit [DecidableEq S] in
theorem Mbd_pos (p Z : O → S → ℝ) (hp : ∀ k s, 0 < p k s) : 0 < Mbd p Z := by
  have hc := cZ_ge p Z hp
  have : 0 ≤ ∑ k, ∑ i, |Z k i| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold Mbd
  linarith

/-- **Stage 332: Mantel on finite price sets with endowments, explicit bound.** As stage 329,
with the net trades `mx p Z` and the bound `M = Mbd p Z` written out: for every scale `λ > 0` and
every endowment profile with all coordinates at least `λ · Mbd p Z`, consumer `i`'s
continuous, concave, strictly monotone consumption utility `c ↦ u_i((c − e_i)/λ)` has the
unique maximiser `e_i + λ mx_i(p_k)` on `p_k · c ≤ p_k · e_i`, consumption is nonnegative, and
aggregate excess demand is `λ Z`. -/
theorem mantel_explicit_endow [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ u : S → (S → ℝ) → ℝ,
      ∀ (lam : ℝ) (e : S → S → ℝ), 0 < lam → (∀ i s, lam * Mbd p Z ≤ e i s) →
        (∀ i, Continuous (eu (u i) (e i) lam)) ∧
        (∀ i, ConcaveOn ℝ Set.univ (eu (u i) (e i) lam)) ∧
        (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) →
          eu (u i) (e i) lam y < eu (u i) (e i) lam z) ∧
        (∀ k s, ∑ i, ((e i s + lam * mx p Z i k s) - e i s) = lam * Z k s) ∧
        (∀ i k s, 0 ≤ e i s + lam * mx p Z i k s) ∧
        (∀ i k, dot (p k) (fun s => e i s + lam * mx p Z i k s) = dot (p k) (e i)) ∧
        (∀ i k c, dot (p k) c ≤ dot (p k) (e i) → c ≠ (fun s => e i s + lam * mx p Z i k s) →
          eu (u i) (e i) lam c < eu (u i) (e i) lam (fun s => e i s + lam * mx p Z i k s)) := by
  obtain ⟨u, x, hxe, hc, hcc, hm, hb, hopt, hagg⟩ := mantel_finite_unique p hp hunit hinj Z hW
  subst hxe
  refine ⟨u, fun lam e hlam he => ⟨fun i => eu_continuous _ _ _ (hc i),
    fun i => eu_concave _ _ _ (hcc i), fun i => eu_strictMono _ _ _ hlam (hm i),
    fun k s => ?_, fun i k s => ?_, fun i k => (endow_transfer p (u i) (mx p Z i) (e i) lam hlam
      (hb i) (hopt i) k).1, fun i k => (endow_transfer p (u i) (mx p Z i) (e i) lam hlam
      (hb i) (hopt i) k).2⟩⟩
  · simp only [add_sub_cancel_left]
    rw [← Finset.mul_sum, hagg k s]
  · have h1 := (abs_le.1 (mx_bound p Z hp hunit i k s)).1
    have h2 : lam * (-Mbd p Z) ≤ lam * mx p Z i k s := mul_le_mul_of_nonneg_left h1 hlam.le
    have h3 := he i s
    linarith

/-- **Stage 333: no rescaling needed above the explicit floor.** If every endowment
coordinate is at least `Mbd p Z`, then at each price `p_k` consumer `i`'s continuous, concave,
strictly monotone consumption utility `c ↦ u_i(c − e_i)` has the unique maximiser
`e_i + mx_i(p_k)` on `p_k · c ≤ p_k · e_i`, consumption is nonnegative, and the aggregate excess
demand is exactly `Z k` (scale `1`). -/
theorem mantel_unscaled [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ u : S → (S → ℝ) → ℝ,
      ∀ e : S → S → ℝ, (∀ i s, Mbd p Z ≤ e i s) →
        (∀ i, Continuous (eu (u i) (e i) 1)) ∧
        (∀ i, ConcaveOn ℝ Set.univ (eu (u i) (e i) 1)) ∧
        (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) →
          eu (u i) (e i) 1 y < eu (u i) (e i) 1 z) ∧
        (∀ k s, ∑ i, mx p Z i k s = Z k s) ∧
        (∀ i k s, 0 ≤ e i s + mx p Z i k s) ∧
        (∀ i k, dot (p k) (fun s => e i s + mx p Z i k s) = dot (p k) (e i)) ∧
        (∀ i k c, dot (p k) c ≤ dot (p k) (e i) → c ≠ (fun s => e i s + mx p Z i k s) →
          eu (u i) (e i) 1 c < eu (u i) (e i) 1 (fun s => e i s + mx p Z i k s)) := by
  obtain ⟨u, hu⟩ := mantel_explicit_endow p hp hunit hinj Z hW
  refine ⟨u, fun e he => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu 1 e one_pos (fun i s => by rw [one_mul]; exact he i s)
  have hfun : ∀ i k, (fun s => e i s + 1 * mx p Z i k s) = (fun s => e i s + mx p Z i k s) :=
    fun i k => funext fun s => by rw [one_mul]
  refine ⟨h1, h2, h3, fun k s => ?_, fun i k s => ?_, fun i k => ?_, fun i k c hc hne => ?_⟩
  · have h := h4 k s
    simp only [one_mul, add_sub_cancel_left] at h
    exact h
  · have h := h5 i k s
    rwa [one_mul] at h
  · rw [← hfun]
    exact h6 i k
  · rw [← hfun] at hne ⊢
    exact h7 i k c hc hne

omit [Fintype O] [DecidableEq S] in
/-- Nonnegative consumption bounds aggregate excess demand below by minus total endowment. -/
theorem excess_lower (c e : S → S → ℝ) (hc : ∀ i s, 0 ≤ c i s) (s : S) :
    -(∑ i, e i s) ≤ ∑ i, (c i s - e i s) := by
  rw [Finset.sum_sub_distrib]
  have : 0 ≤ ∑ i, c i s := Finset.sum_nonneg fun i _ => hc i s
  linarith

omit [Fintype O] [DecidableEq S] in
/-- **Stage 333: the necessary side.** If some coordinate of `Z k` is below minus the total
endowment of that good, no nonnegative allocation has aggregate excess demand `Z k`, so
scale `1` is impossible at that price whatever the utilities. -/
theorem unscaled_impossible (Z : O → S → ℝ) (e : S → S → ℝ) (k : O) (s : S)
    (hs : Z k s < -(∑ i, e i s)) :
    ¬ ∃ c : S → S → ℝ, (∀ i s, 0 ≤ c i s) ∧ ∀ s, ∑ i, (c i s - e i s) = Z k s := by
  rintro ⟨c, hc, hsum⟩
  have := excess_lower c e hc s
  rw [hsum s] at this
  linarith

/-! ### Stage 337: consumer-specific floors -/

/-- **Stage 337: exact consumer-specific floors.** -/
theorem mantel_exact_floor [Nonempty O] (p : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (hinj : Function.Injective p) (Z : O → S → ℝ)
    (hW : ∀ k, dot (p k) (Z k) = 0) :
    ∃ u : S → (S → ℝ) → ℝ,
      ∀ e : S → S → ℝ, (∀ i k s, -mx p Z i k s ≤ e i s) →
        (∀ i, Continuous (eu (u i) (e i) 1)) ∧
        (∀ i, ConcaveOn ℝ Set.univ (eu (u i) (e i) 1)) ∧
        (∀ i (y z : S → ℝ), (∀ s, y s ≤ z s) → (∃ s, y s < z s) →
          eu (u i) (e i) 1 y < eu (u i) (e i) 1 z) ∧
        (∀ k s, ∑ i, mx p Z i k s = Z k s) ∧
        (∀ i k s, 0 ≤ e i s + mx p Z i k s) ∧
        (∀ i k, dot (p k) (fun s => e i s + mx p Z i k s) = dot (p k) (e i)) ∧
        (∀ i k c, dot (p k) c ≤ dot (p k) (e i) → c ≠ (fun s => e i s + mx p Z i k s) →
          eu (u i) (e i) 1 c < eu (u i) (e i) 1 (fun s => e i s + mx p Z i k s)) := by
  obtain ⟨u, x, hxe, hc, hcc, hm, hb, hopt, hagg⟩ := mantel_finite_unique p hp hunit hinj Z hW
  subst hxe
  have hfun : ∀ (e : S → S → ℝ) i k,
      (fun s => e i s + 1 * mx p Z i k s) = (fun s => e i s + mx p Z i k s) :=
    fun e i k => funext fun s => by rw [one_mul]
  refine ⟨u, fun e he => ⟨fun i => eu_continuous _ _ _ (hc i),
    fun i => eu_concave _ _ _ (hcc i), fun i => eu_strictMono _ _ _ one_pos (hm i),
    hagg, fun i k s => by linarith [he i k s], fun i k => ?_, fun i k c hc' hne => ?_⟩⟩
  · rw [← hfun]
    exact (endow_transfer p (u i) (mx p Z i) (e i) 1 one_pos (hb i) (hopt i) k).1
  · rw [← hfun] at hne ⊢
    exact (endow_transfer p (u i) (mx p Z i) (e i) 1 one_pos (hb i) (hopt i) k).2 c hc' hne

/-- The uniform stage-333 floor implies the consumer-specific floors. -/
theorem floor_of_Mbd (p Z : O → S → ℝ) (hp : ∀ k s, 0 < p k s)
    (hunit : ∀ k, ∑ s, p k s ^ 2 = 1) (e : S → S → ℝ) (he : ∀ i s, Mbd p Z ≤ e i s)
    (i : S) (k : O) (s : S) : -mx p Z i k s ≤ e i s := by
  have h1 := (abs_le.1 (mx_bound p Z hp hunit i k s)).1
  linarith [he i s]

/-- Summed over consumers, the consumer-specific floors dominate the aggregate necessary floor. -/
theorem floor_sum_ge (p Z : O → S → ℝ) (e : S → S → ℝ)
    (he : ∀ i k s, -mx p Z i k s ≤ e i s) (hagg : ∀ k s, ∑ i, mx p Z i k s = Z k s)
    (k : O) (s : S) : -Z k s ≤ ∑ i, e i s := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset S)) => he i k s
  rw [Finset.sum_neg_distrib, hagg k s] at h
  exact h

end MantelExactFloor

end

#print axioms MantelExactFloor.dot_affine
#print axioms MantelExactFloor.afriat_continuous
#print axioms MantelExactFloor.afriat_concave
#print axioms MantelExactFloor.afriat_strictMono
#print axioms MantelExactFloor.afriat_potential
#print axioms MantelExactFloor.dot_mdir
#print axioms MantelExactFloor.mantel_finite
#print axioms MantelExactFloor.bg_self
#print axioms MantelExactFloor.bg_nonpos
#print axioms MantelExactFloor.bg_neg
#print axioms MantelExactFloor.bg_concave
#print axioms MantelExactFloor.step_le
#print axioms MantelExactFloor.step_lt
#print axioms MantelExactFloor.pc_sum
#print axioms MantelExactFloor.pc_continuous
#print axioms MantelExactFloor.pc_concave
#print axioms MantelExactFloor.pc_strictMono
#print axioms MantelExactFloor.au_continuous
#print axioms MantelExactFloor.au_concave
#print axioms MantelExactFloor.au_strictMono
#print axioms MantelExactFloor.strict_afriat
#print axioms MantelExactFloor.ev_small
#print axioms MantelExactFloor.afriat_unique
#print axioms MantelExactFloor.mantel_finite_unique
#print axioms MantelExactFloor.eu_continuous
#print axioms MantelExactFloor.eu_concave
#print axioms MantelExactFloor.eu_strictMono
#print axioms MantelExactFloor.dot_shift
#print axioms MantelExactFloor.dot_scale
#print axioms MantelExactFloor.endow_transfer
#print axioms MantelExactFloor.p_le_one
#print axioms MantelExactFloor.mdir_abs
#print axioms MantelExactFloor.cZ_ge
#print axioms MantelExactFloor.Z_le_sum
#print axioms MantelExactFloor.mcoef_abs
#print axioms MantelExactFloor.mx_bound
#print axioms MantelExactFloor.Mbd_pos
#print axioms MantelExactFloor.mantel_explicit_endow
#print axioms MantelExactFloor.mantel_unscaled
#print axioms MantelExactFloor.excess_lower
#print axioms MantelExactFloor.unscaled_impossible
#print axioms MantelExactFloor.mantel_exact_floor
#print axioms MantelExactFloor.floor_of_Mbd
#print axioms MantelExactFloor.floor_sum_ge
