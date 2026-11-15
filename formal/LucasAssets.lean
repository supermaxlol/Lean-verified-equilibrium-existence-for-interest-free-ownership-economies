import Mathlib

/-!
Stage 293: Lucas tree with many assets, short sales and zero consumption.

Any finite set of assets with dividends `d j s`, priced by the representative household's
Euler equation.  Households may short any asset and may consume zero.  Holding one share of
the tree forever is optimal against every history-dependent plan, up to the transversality
term; with transversality it is optimal.  Prices for every asset exist (contraction).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace LucasAssets

theorem bernoulli_neg (p t : ℝ) (hp : p < 0) (ht : 0 < t) : 1 + p * (t - 1) ≤ t ^ p := by
  rw [Real.rpow_def_of_pos ht]
  have h1 := Real.add_one_le_exp (Real.log t * p)
  have h2 := Real.log_le_sub_one_of_pos ht
  have h3 : p * (t - 1) ≤ p * Real.log t := mul_le_mul_of_nonpos_left h2 hp.le
  linarith


/-- Bernoulli from above, exponent between zero and one. -/
theorem bernoulli_pos (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) :
    t ^ p ≤ 1 + p * (t - 1) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hp.le (by linarith : (0 : ℝ) ≤ 1 - p)
    ht.le zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- **Supergradient inequality for CRRA utility.** -/
theorem crra_supergradient (p a b : ℝ) (hp1 : p < 1) (hp0 : p ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    1 / p * a ^ p ≤ 1 / p * b ^ p + b ^ (p - 1) * (a - b) := by
  have ht : 0 < a / b := div_pos ha hb
  have hB : 0 < b ^ p := Real.rpow_pos_of_pos hb p
  have hA : a ^ p = (a / b) ^ p * b ^ p := by
    rw [← Real.mul_rpow ht.le hb.le, div_mul_cancel₀ a hb.ne']
  have hm : b ^ (p - 1) * (a - b) = b ^ p * (a / b - 1) := by
    rw [Real.rpow_sub_one hb.ne']
    field_simp
  have hpc : p * (1 / p) = 1 := mul_one_div_cancel hp0
  have hkey : (a / b) ^ p * (1 / p) ≤ 1 / p + (a / b - 1) := by
    rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · have hk := bernoulli_neg p (a / b) hneg ht
      have hc : 1 / p < 0 := one_div_neg.2 hneg
      have h := mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
    · have hk := bernoulli_pos p (a / b) hpos hp1 ht
      have hc : 0 < 1 / p := one_div_pos.2 hpos
      have h := mul_nonneg hc.le (sub_nonneg.2 hk)
      have e : 1 / p * (1 + p * (a / b - 1) - (a / b) ^ p)
          = 1 / p + (p * (1 / p)) * (a / b - 1) - (a / b) ^ p * (1 / p) := by ring
      rw [e, hpc, one_mul] at h
      linarith
  have h2 := mul_le_mul_of_nonneg_left hkey hB.le
  rw [hA, hm]
  linarith

variable {X : Type*} [Fintype X]

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

variable {S : Type*} [Fintype S]

/-- The operator `w ↦ f + β Π w`. -/
def linOp (π : S → S → ℝ) (β : ℝ) (f w : S → ℝ) : S → ℝ :=
  fun s => f s + β * ∑ s', π s s' * w s'

/-- **The linear value equation has exactly one solution.** -/
theorem lin_fixed (π : S → S → ℝ) (β : ℝ) (f : S → ℝ) (hπ : ∀ s s', 0 ≤ π s s')
    (hπ1 : ∀ s, ∑ s', π s s' = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) :
    ∃ w : S → ℝ, linOp π β f w = w ∧ ∀ w', linOp π β f w' = w' → w' = w := by
  have hmono : ∀ v w : S → ℝ, (∀ x, v x ≤ w x) → ∀ x, linOp π β f v x ≤ linOp π β f w x := by
    intro v w hvw s
    have h1 := Finset.sum_le_sum
      (fun s' (_ : s' ∈ (univ : Finset S)) => mul_le_mul_of_nonneg_left (hvw s') (hπ s s'))
    have h2 := mul_le_mul_of_nonneg_left h1 hβ
    simp only [linOp]
    linarith
  have hdisc : ∀ (v : S → ℝ) (c : ℝ), 0 ≤ c →
      ∀ x, linOp π β f (fun y => v y + c) x ≤ linOp π β f v x + β * c := by
    intro v c _ s
    have e : ∑ s', π s s' * (v s' + c) = ∑ s', π s s' * v s' + c := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ1 s, one_mul]
    simp only [linOp]
    rw [e]
    apply le_of_eq
    ring
  obtain ⟨V, hV, hu, -⟩ := blackwell_fixed_point (linOp π β f) β hβ hβ1 hmono hdisc
  exact ⟨V, hV, hu⟩

/-! ### Supergradients for the instances -/

theorem power_sg_nonneg (p c d : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hc : 0 ≤ c) (hd : 0 < d) :
    1 / p * c ^ p ≤ 1 / p * d ^ p + d ^ (p - 1) * (c - d) := by
  rcases hc.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow hp0.ne', mul_zero, zero_sub, Real.rpow_sub_one hd.ne']
    have hD : 0 < d ^ p := Real.rpow_pos_of_pos hd p
    have e : d ^ p / d * -d = - d ^ p := by field_simp
    rw [e]
    have h1 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    nlinarith
  · exact crra_supergradient p c d hp1 hp0.ne' h hd

theorem log_sg (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    Real.log c ≤ Real.log d + 1 / d * (c - d) := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hc hd)
  rw [Real.log_div hc.ne' hd.ne'] at h1
  have e : 1 / d * (c - d) = c / d - 1 := by field_simp
  rw [e]
  linarith

/-! ### Prices exist for every asset -/

theorem asset_price_exists (π : S → S → ℝ) (β : ℝ) (mu dv : S → ℝ) (hπ : ∀ s s', 0 ≤ π s s')
    (hπ1 : ∀ s, ∑ s', π s s' = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (hmu : ∀ s, 0 < mu s) :
    ∃ P : S → ℝ, ∀ s, mu s * P s = β * ∑ s', π s s' * (mu s' * (P s' + dv s')) := by
  obtain ⟨z, hz, -⟩ := lin_fixed π β (fun s => β * ∑ s', π s s' * (mu s' * dv s')) hπ hπ1 hβ hβ1
  refine ⟨fun s => z s / mu s, fun s => ?_⟩
  have hzs := congrFun hz s
  simp only [linOp] at hzs
  have key : ∀ s', mu s' * (z s' / mu s' + dv s') = z s' + mu s' * dv s' := fun s' => by
    rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ (hmu s').ne']
  simp_rw [key]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (hmu s).ne']
  have e : ∑ s', π s s' * (z s' + mu s' * dv s') =
      ∑ s', π s s' * z s' + ∑ s', π s s' * (mu s' * dv s') := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [e]
  linarith

/-! ### Plans over histories -/

variable {J : Type*} [Fintype J]

/-- Holdings carried into a node: the initial portfolio at the root, otherwise the portfolio
chosen at the parent node. -/
def inc (x : S → List S → J → ℝ) (x0 : J → ℝ) : S → List S → J → ℝ
  | _, [] => x0
  | _, s :: h => x s h

/-- Marginal value of holdings `y` in excess of the reference portfolio `e`. -/
def Fv (mu : S → ℝ) (P d : J → S → ℝ) (e : J → ℝ) (s : S) (y : J → ℝ) : ℝ :=
  mu s * ∑ j, (y j - e j) * (P j s + d j s)

/-- Discounted marginal-utility-weighted consumption gap over `n` periods. -/
def gap (π : S → S → ℝ) (β : ℝ) (mu Y : S → ℝ) (c : S → List S → ℝ) :
    ℕ → S → List S → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => mu s * (c s h - Y s) + β * ∑ s', π s s' * gap π β mu Y c n s' (s :: h)

/-- Plan utility minus hold utility over `n` periods. -/
def ugap (π : S → S → ℝ) (β : ℝ) (u : ℝ → ℝ) (Y : S → ℝ) (c : S → List S → ℝ) :
    ℕ → S → List S → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => (u (c s h) - u (Y s)) + β * ∑ s', π s s' * ugap π β u Y c n s' (s :: h)

/-- The transversality term. -/
def term (π : S → S → ℝ) (β : ℝ) (mu : S → ℝ) (P d : J → S → ℝ) (e : J → ℝ)
    (x : S → List S → J → ℝ) (x0 : J → ℝ) : ℕ → S → List S → ℝ
  | 0, s, h => Fv mu P d e s (inc x x0 s h)
  | n + 1, s, h => β * ∑ s', π s s' * term π β mu P d e x x0 n s' (s :: h)

theorem node_step (π : S → S → ℝ) (β : ℝ) (mu Y : S → ℝ) (P d : J → S → ℝ) (e : J → ℝ)
    (c : S → List S → ℝ) (x : S → List S → J → ℝ) (x0 : J → ℝ) (hmu : ∀ s, 0 ≤ mu s)
    (hE : ∀ j s, mu s * P j s = β * ∑ s', π s s' * (mu s' * (P j s' + d j s')))
    (hhold : ∀ s, Y s + ∑ j, P j s * e j = ∑ j, e j * (P j s + d j s))
    (hbud : ∀ s h, c s h + ∑ j, P j s * x s h j ≤ ∑ j, inc x x0 s h j * (P j s + d j s))
    (s : S) (h : List S) :
    mu s * (c s h - Y s) ≤
      Fv mu P d e s (inc x x0 s h) - β * ∑ s', π s s' * Fv mu P d e s' (x s h) := by
  have h1 : c s h - Y s + ∑ j, P j s * (x s h j - e j) ≤
      ∑ j, (inc x x0 s h j - e j) * (P j s + d j s) := by
    have a1 : ∑ j, P j s * (x s h j - e j) = ∑ j, P j s * x s h j - ∑ j, P j s * e j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have a2 : ∑ j, (inc x x0 s h j - e j) * (P j s + d j s) =
        ∑ j, inc x x0 s h j * (P j s + d j s) - ∑ j, e j * (P j s + d j s) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [a1, a2]
    linarith [hbud s h, hhold s]
  have h2 := mul_le_mul_of_nonneg_left h1 (hmu s)
  have e1 : mu s * ∑ j, P j s * (x s h j - e j) =
      β * ∑ s', π s s' * Fv mu P d e s' (x s h) := by
    unfold Fv
    calc mu s * ∑ j, P j s * (x s h j - e j)
        = ∑ j, (x s h j - e j) * (mu s * P j s) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, (x s h j - e j) * (β * ∑ s', π s s' * (mu s' * (P j s' + d j s'))) :=
          Finset.sum_congr rfl fun j _ => by rw [hE j s]
      _ = β * ∑ s', π s s' * (mu s' * ∑ j, (x s h j - e j) * (P j s' + d j s')) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : mu s * (c s h - Y s + ∑ j, P j s * (x s h j - e j)) =
      mu s * (c s h - Y s) + mu s * ∑ j, P j s * (x s h j - e j) := by ring
  rw [e2, e1] at h2
  show _ ≤ mu s * ∑ j, (inc x x0 s h j - e j) * (P j s + d j s) - _
  linarith

theorem gap_le (π : S → S → ℝ) (β : ℝ) (mu Y : S → ℝ) (P d : J → S → ℝ) (e : J → ℝ)
    (c : S → List S → ℝ) (x : S → List S → J → ℝ) (x0 : J → ℝ)
    (hπ : ∀ s s', 0 ≤ π s s') (hβ : 0 ≤ β) (hmu : ∀ s, 0 ≤ mu s)
    (hE : ∀ j s, mu s * P j s = β * ∑ s', π s s' * (mu s' * (P j s' + d j s')))
    (hhold : ∀ s, Y s + ∑ j, P j s * e j = ∑ j, e j * (P j s + d j s))
    (hbud : ∀ s h, c s h + ∑ j, P j s * x s h j ≤ ∑ j, inc x x0 s h j * (P j s + d j s)) :
    ∀ n s h, gap π β mu Y c n s h ≤
      Fv mu P d e s (inc x x0 s h) - term π β mu P d e x x0 n s h := by
  intro n
  induction n with
  | zero => intro s h; simp [gap, term]
  | succ n ih =>
    intro s h
    have hs := node_step π β mu Y P d e c x x0 hmu hE hhold hbud s h
    have h2 : β * ∑ s', π s s' * gap π β mu Y c n s' (s :: h) ≤
        β * ∑ s', π s s' * (Fv mu P d e s' (x s h) - term π β mu P d e x x0 n s' (s :: h)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (ih s' (s :: h)) (hπ s s')) hβ
    have h3 : β * ∑ s', π s s' * (Fv mu P d e s' (x s h) - term π β mu P d e x x0 n s' (s :: h))
        = β * ∑ s', π s s' * Fv mu P d e s' (x s h) - term π β mu P d e x x0 (n + 1) s h := by
      simp only [term, mul_sub, Finset.sum_sub_distrib]
    simp only [gap]
    linarith

theorem ugap_le (π : S → S → ℝ) (β : ℝ) (u : ℝ → ℝ) (mu Y : S → ℝ) (c : S → List S → ℝ)
    (hπ : ∀ s s', 0 ≤ π s s') (hβ : 0 ≤ β)
    (hsg : ∀ s h, u (c s h) ≤ u (Y s) + mu s * (c s h - Y s)) :
    ∀ n s h, ugap π β u Y c n s h ≤ gap π β mu Y c n s h := by
  intro n
  induction n with
  | zero => intro s h; simp [ugap, gap]
  | succ n ih =>
    intro s h
    have h2 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun s' _ =>
      mul_le_mul_of_nonneg_left (ih s' (s :: h)) (hπ s s')) hβ
    simp only [ugap, gap]
    linarith [hsg s h]

/-- **Holding the tree beats every plan.**  Any finite set of assets priced by the Euler
equation, any portfolios (short sales allowed), any consumption in the supergradient domain.
Over `n` periods the plan's utility is at most the hold utility minus the transversality
term; if that term vanishes, the plan is no better than holding the tree. -/
theorem hold_beats_every_plan [DecidableEq J] (π : S → S → ℝ) (β : ℝ) (u : ℝ → ℝ)
    (mu Y : S → ℝ) (P d : J → S → ℝ) (j0 : J) (c : S → List S → ℝ)
    (x : S → List S → J → ℝ) (s0 : S)
    (hπ : ∀ s s', 0 ≤ π s s') (hβ : 0 ≤ β) (hmu : ∀ s, 0 ≤ mu s)
    (hE : ∀ j s, mu s * P j s = β * ∑ s', π s s' * (mu s' * (P j s' + d j s')))
    (hd0 : ∀ s, d j0 s = Y s)
    (hbud : ∀ s h, c s h + ∑ j, P j s * x s h j ≤
      ∑ j, inc x (fun j => if j = j0 then 1 else 0) s h j * (P j s + d j s))
    (hsg : ∀ s h, u (c s h) ≤ u (Y s) + mu s * (c s h - Y s)) :
    (∀ n, ugap π β u Y c n s0 [] ≤
        - term π β mu P d (fun j => if j = j0 then 1 else 0) x
          (fun j => if j = j0 then 1 else 0) n s0 []) ∧
    (∀ G, Tendsto (fun n => ugap π β u Y c n s0 []) atTop (𝓝 G) →
      Tendsto (fun n => term π β mu P d (fun j => if j = j0 then 1 else 0) x
        (fun j => if j = j0 then 1 else 0) n s0 []) atTop (𝓝 0) → G ≤ 0) := by
  set e : J → ℝ := fun j => if j = j0 then 1 else 0 with he
  have hhold : ∀ s, Y s + ∑ j, P j s * e j = ∑ j, e j * (P j s + d j s) := by
    intro s
    have a1 : ∑ j, P j s * e j = P j0 s := by simp [he]
    have a2 : ∑ j, e j * (P j s + d j s) = P j0 s + d j0 s := by simp [he]
    rw [a1, a2, hd0 s]
    ring
  have hF : Fv mu P d e s0 (inc x e s0 []) = 0 := by simp [Fv, inc]
  have part1 : ∀ n, ugap π β u Y c n s0 [] ≤ - term π β mu P d e x e n s0 [] := by
    intro n
    have a := ugap_le π β u mu Y c hπ hβ hsg n s0 []
    have b := gap_le π β mu Y P d e c x e hπ hβ hmu hE hhold hbud n s0 []
    rw [hF] at b
    linarith
  refine ⟨part1, fun G hG hT => ?_⟩
  have := le_of_tendsto_of_tendsto' hG hT.neg part1
  simpa using this

/-- Power felicity `c ^ p / p`, `0 < p < 1`: zero consumption and any short positions allowed. -/
theorem power_plans [DecidableEq J] (π : S → S → ℝ) (β p : ℝ) (Y : S → ℝ) (P d : J → S → ℝ)
    (j0 : J) (c : S → List S → ℝ) (x : S → List S → J → ℝ) (s0 : S)
    (hπ : ∀ s s', 0 ≤ π s s') (hβ : 0 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) (hY : ∀ s, 0 < Y s)
    (hc : ∀ s h, 0 ≤ c s h)
    (hE : ∀ j s, Y s ^ (p - 1) * P j s =
      β * ∑ s', π s s' * (Y s' ^ (p - 1) * (P j s' + d j s')))
    (hd0 : ∀ s, d j0 s = Y s)
    (hbud : ∀ s h, c s h + ∑ j, P j s * x s h j ≤
      ∑ j, inc x (fun j => if j = j0 then 1 else 0) s h j * (P j s + d j s)) :
    ∀ n, ugap π β (fun c => 1 / p * c ^ p) Y c n s0 [] ≤
        - term π β (fun s => Y s ^ (p - 1)) P d (fun j => if j = j0 then 1 else 0) x
          (fun j => if j = j0 then 1 else 0) n s0 [] :=
  (hold_beats_every_plan π β (fun c => 1 / p * c ^ p) (fun s => Y s ^ (p - 1)) Y P d j0 c x s0
    hπ hβ (fun s => (Real.rpow_pos_of_pos (hY s) _).le) hE hd0 hbud
    (fun s h => power_sg_nonneg p (c s h) (Y s) hp0 hp1 (hc s h) (hY s))).1

end LucasAssets

end

#print axioms LucasAssets.power_sg_nonneg
#print axioms LucasAssets.log_sg
#print axioms LucasAssets.asset_price_exists
#print axioms LucasAssets.node_step
#print axioms LucasAssets.gap_le
#print axioms LucasAssets.ugap_le
#print axioms LucasAssets.hold_beats_every_plan
#print axioms LucasAssets.power_plans
