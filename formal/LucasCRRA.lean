import Mathlib

/-!
Stage 289: the Lucas tree with general CRRA utility, the price derived by contraction,
and optimality of holding the tree against every history-dependent plan.

Felicity `u c = c ^ p / p` with `p < 1`, `p ≠ 0` (relative risk aversion `1 - p`).
Markov output `Y s > 0`, transition weights `π s s'`, discount `0 < β < 1`.

* `lin_fixed` — the equation `w = Y ^ p + β Π w` has exactly one solution (contraction);
  `lin_fixed_pos` — it is strictly positive.
* `price` — the tree price `P s = Y s * (w s / Y s ^ p - 1)`; `price_euler` — it satisfies
  the Euler equation; `price_unique` — it is the only price that does.
* `crra_bellman` — `V θ s = θ ^ p * w s / p` satisfies the Bellman inequality against every
  affordable choice, with equality at hold-forever (`crra_bellman_eq`).
* `plan_le`, `plan_optimal` — against every history-dependent plan, utility over `n` periods
  plus discounted continuation value is at most `V`; with transversality, total utility
  is at most `V`.
* `hold_attains` — holding the share forever attains `V`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace LucasCRRA

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

/-- The solution is strictly positive when `f` is. -/
theorem lin_fixed_pos (π : S → S → ℝ) (β : ℝ) (f w : S → ℝ) (hπ : ∀ s s', 0 ≤ π s s')
    (hπ1 : ∀ s, ∑ s', π s s' = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (hf : ∀ s, 0 < f s)
    (hw : linOp π β f w = w) : ∀ s, 0 < w s := by
  intro s
  obtain ⟨s0, -, hs0⟩ := Finset.exists_min_image univ w ⟨s, mem_univ s⟩
  have h1 : ∑ s', π s0 s' * w s0 ≤ ∑ s', π s0 s' * w s' :=
    Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hs0 s' (mem_univ _)) (hπ s0 s'))
  rw [← Finset.sum_mul, hπ1 s0, one_mul] at h1
  have h2 : w s0 = f s0 + β * ∑ s', π s0 s' * w s' := (congrFun hw s0).symm
  have h3 := mul_le_mul_of_nonneg_left h1 hβ
  have h4 := hf s0
  have h5 : 0 < (1 - β) * w s0 := by nlinarith
  have h6 : 0 < w s0 := pos_of_mul_pos_right h5 (by linarith)
  linarith [hs0 s (mem_univ s)]

/-- The tree price built from `w`. -/
def price (Y w : S → ℝ) (p : ℝ) (s : S) : ℝ := Y s * (w s / Y s ^ p - 1)

/-- Marginal utility times the payoff of the tree is `w`. -/
theorem marg (Y w : S → ℝ) (p : ℝ) (s : S) (hY : 0 < Y s) :
    Y s ^ (p - 1) * (Y s + price Y w p s) = w s := by
  have hYp : 0 < Y s ^ p := Real.rpow_pos_of_pos hY p
  unfold price
  calc Y s ^ (p - 1) * (Y s + Y s * (w s / Y s ^ p - 1))
      = (Y s ^ p / Y s * Y s) * (w s / Y s ^ p) := by rw [Real.rpow_sub_one hY.ne']; ring
    _ = w s / Y s ^ p * Y s ^ p := by rw [div_mul_cancel₀ _ hY.ne']; ring
    _ = w s := div_mul_cancel₀ _ hYp.ne'

theorem marg_out (Y : S → ℝ) (p : ℝ) (s : S) (hY : 0 < Y s) :
    Y s ^ (p - 1) * Y s = Y s ^ p := by
  rw [Real.rpow_sub_one hY.ne']
  exact div_mul_cancel₀ _ hY.ne'

/-- **Euler equation for the tree price.** -/
theorem price_euler (π : S → S → ℝ) (Y w : S → ℝ) (p β : ℝ) (hY : ∀ s, 0 < Y s)
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (s : S) :
    Y s ^ (p - 1) * price Y w p s
      = β * ∑ s', π s s' * (Y s' ^ (p - 1) * (Y s' + price Y w p s')) := by
  have h1 := marg Y w p s (hY s)
  have h2 := marg_out Y p s (hY s)
  simp only [fun s' => marg Y w p s' (hY s')]
  have e : Y s ^ (p - 1) * price Y w p s
      = Y s ^ (p - 1) * (Y s + price Y w p s) - Y s ^ (p - 1) * Y s := by ring
  rw [e, h1, h2, hw s]
  ring

/-- **The tree price is the only one satisfying the Euler equation.** -/
theorem price_unique (π : S → S → ℝ) (Y w P : S → ℝ) (p β : ℝ) (hY : ∀ s, 0 < Y s)
    (hπ : ∀ s s', 0 ≤ π s s') (hπ1 : ∀ s, ∑ s', π s s' = 1) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s')
    (hP : ∀ s, Y s ^ (p - 1) * P s = β * ∑ s', π s s' * (Y s' ^ (p - 1) * (Y s' + P s'))) :
    ∀ s, P s = price Y w p s := by
  obtain ⟨w0, -, hu⟩ := lin_fixed π β (fun s => Y s ^ p) hπ hπ1 hβ hβ1
  have hw' : linOp π β (fun s => Y s ^ p) w = w := funext fun s => (hw s).symm
  have hv : linOp π β (fun s => Y s ^ p) (fun s => Y s ^ (p - 1) * (Y s + P s))
      = fun s => Y s ^ (p - 1) * (Y s + P s) := by
    funext s
    simp only [linOp]
    rw [← hP s, mul_add, marg_out Y p s (hY s)]
  have e : (fun s => Y s ^ (p - 1) * (Y s + P s)) = w := (hu _ hv).trans (hu _ hw').symm
  intro s
  have h1 : Y s ^ (p - 1) * (Y s + P s) = w s := congrFun e s
  have h2 := marg Y w p s (hY s)
  have hB : 0 < Y s ^ (p - 1) := Real.rpow_pos_of_pos (hY s) _
  have h3 : Y s ^ (p - 1) * (Y s + P s) = Y s ^ (p - 1) * (Y s + price Y w p s) := by
    rw [h1, h2]
  have h4 := mul_left_cancel₀ hB.ne' h3
  linarith

/-- **Bellman inequality for CRRA.**  From share `θ`, any consumption `c` and next share `θ'`
affordable at the tree price give no more than `V θ s = θ ^ p * w s / p`. -/
theorem crra_bellman (π : S → S → ℝ) (Y w : S → ℝ) (p β θ θ' c : ℝ) (s : S)
    (hp1 : p < 1) (hp0 : p ≠ 0) (hβ : 0 ≤ β) (hY : ∀ s, 0 < Y s) (hπ : ∀ s s', 0 ≤ π s s')
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (hw0 : ∀ s, 0 < w s)
    (hθ : 0 < θ) (hθ' : 0 < θ') (hc : 0 < c)
    (hbud : c + price Y w p s * θ' ≤ θ * (price Y w p s + Y s)) :
    1 / p * c ^ p + β * ∑ s', π s s' * (1 / p * θ' ^ p * w s') ≤ 1 / p * θ ^ p * w s := by
  have hYs := hY s
  have hsg := crra_supergradient p c (θ * Y s) hp1 hp0 hc (mul_pos hθ hYs)
  simp only [Real.mul_rpow hθ.le hYs.le] at hsg
  have hterm : ∀ s', π s s' * (1 / p * θ' ^ p * w s')
      ≤ 1 / p * θ ^ p * (π s s' * w s') + θ ^ (p - 1) * (θ' - θ) * (π s s' * w s') := by
    intro s'
    have hg := crra_supergradient p θ' θ hp1 hp0 hθ' hθ
    have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg (hπ s s') (hw0 s').le)
    calc π s s' * (1 / p * θ' ^ p * w s') = (π s s' * w s') * (1 / p * θ' ^ p) := by ring
      _ ≤ (π s s' * w s') * (1 / p * θ ^ p + θ ^ (p - 1) * (θ' - θ)) := hm
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun s' (_ : s' ∈ (univ : Finset S)) => hterm s')
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hsb := mul_le_mul_of_nonneg_left hsum hβ
  have hE := price_euler π Y w p β hY hw s
  simp only [fun s' => marg Y w p s' (hY s')] at hE
  have e1 : β * (θ ^ (p - 1) * (θ' - θ) * ∑ s', π s s' * w s')
      = θ ^ (p - 1) * Y s ^ (p - 1) * ((θ' - θ) * price Y w p s) := by
    calc β * (θ ^ (p - 1) * (θ' - θ) * ∑ s', π s s' * w s')
        = θ ^ (p - 1) * (θ' - θ) * (β * ∑ s', π s s' * w s') := by ring
      _ = θ ^ (p - 1) * (θ' - θ) * (Y s ^ (p - 1) * price Y w p s) := by rw [hE]
      _ = _ := by ring
  have hK : 0 < θ ^ (p - 1) * Y s ^ (p - 1) :=
    mul_pos (Real.rpow_pos_of_pos hθ _) (Real.rpow_pos_of_pos hYs _)
  have hneg := mul_nonpos_of_nonneg_of_nonpos hK.le
    (by linarith : c - θ * Y s + (θ' - θ) * price Y w p s ≤ 0)
  have e2 : 1 / p * θ ^ p * w s
      = 1 / p * (θ ^ p * Y s ^ p) + β * (1 / p * θ ^ p * ∑ s', π s s' * w s') := by
    rw [hw s]
    ring
  rw [e2]
  nlinarith [hsg, hsb, e1, hneg]

/-- **Equality at hold-forever.** -/
theorem crra_bellman_eq (π : S → S → ℝ) (Y w : S → ℝ) (p β θ : ℝ) (s : S)
    (hY : ∀ s, 0 < Y s) (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (hθ : 0 < θ) :
    1 / p * (θ * Y s) ^ p + β * ∑ s', π s s' * (1 / p * θ ^ p * w s')
      = 1 / p * θ ^ p * w s := by
  have e : ∑ s', π s s' * (1 / p * θ ^ p * w s') = 1 / p * θ ^ p * ∑ s', π s s' * w s' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [e, Real.mul_rpow hθ.le (hY s).le, hw s]
  ring

/-- Utility over `n` periods of a history-dependent plan plus discounted continuation value.
A node is the current state `s` and the past `h`; `c s h` is consumption and `a s h` the
share held on entering the node. -/
def planW (π : S → S → ℝ) (β p : ℝ) (w : S → ℝ) (c a : S → List S → ℝ) :
    ℕ → S → List S → ℝ
  | 0, s, h => 1 / p * a s h ^ p * w s
  | n + 1, s, h => 1 / p * c s h ^ p + β * ∑ s', π s s' * planW π β p w c a n s' (s :: h)

/-- Utility only. -/
def planU (π : S → S → ℝ) (β p : ℝ) (c : S → List S → ℝ) : ℕ → S → List S → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => 1 / p * c s h ^ p + β * ∑ s', π s s' * planU π β p c n s' (s :: h)

/-- Discounted continuation value only. -/
def planT (π : S → S → ℝ) (β p : ℝ) (w : S → ℝ) (a : S → List S → ℝ) :
    ℕ → S → List S → ℝ
  | 0, s, h => 1 / p * a s h ^ p * w s
  | n + 1, s, h => β * ∑ s', π s s' * planT π β p w a n s' (s :: h)

theorem planW_split (π : S → S → ℝ) (β p : ℝ) (w : S → ℝ) (c a : S → List S → ℝ) (n : ℕ) :
    ∀ s h, planW π β p w c a n s h = planU π β p c n s h + planT π β p w a n s h := by
  induction n with
  | zero => intro s h; simp only [planW, planU, planT, zero_add]
  | succ n ih =>
    intro s h
    simp only [planW, planU, planT, ih, mul_add, Finset.sum_add_distrib]
    ring

/-- **No history-dependent plan beats holding.**  For any affordable plan (consumption and
shares positive, the next share not contingent on next period's state), utility over `n`
periods plus the discounted continuation value is at most `V`. -/
theorem plan_le (π : S → S → ℝ) (Y w : S → ℝ) (p β : ℝ) (c a : S → List S → ℝ)
    (hp1 : p < 1) (hp0 : p ≠ 0) (hβ : 0 ≤ β) (hY : ∀ s, 0 < Y s) (hπ : ∀ s s', 0 ≤ π s s')
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (hw0 : ∀ s, 0 < w s)
    (hc : ∀ s h, 0 < c s h) (ha : ∀ s h, 0 < a s h)
    (hsame : ∀ s h s', a s' (s :: h) = a s (s :: h))
    (hbud : ∀ s h, c s h + price Y w p s * a s (s :: h) ≤ a s h * (price Y w p s + Y s))
    (n : ℕ) : ∀ s h, planW π β p w c a n s h ≤ 1 / p * a s h ^ p * w s := by
  induction n with
  | zero => intro s h; exact le_of_eq rfl
  | succ n ih =>
    intro s h
    simp only [planW]
    have h1 : ∑ s', π s s' * planW π β p w c a n s' (s :: h)
        ≤ ∑ s', π s s' * (1 / p * a s (s :: h) ^ p * w s') := by
      apply Finset.sum_le_sum
      intro s' _
      have := ih s' (s :: h)
      rw [hsame s h s'] at this
      exact mul_le_mul_of_nonneg_left this (hπ s s')
    have h2 := mul_le_mul_of_nonneg_left h1 hβ
    have h3 := crra_bellman π Y w p β (a s h) (a s (s :: h)) (c s h) s hp1 hp0 hβ hY hπ hw hw0
      (ha s h) (ha s (s :: h)) (hc s h) (hbud s h)
    linarith

/-- **Optimality with transversality.**  If the discounted continuation value of a plan
vanishes and its utility converges, the total is at most `V`. -/
theorem plan_optimal (π : S → S → ℝ) (Y w : S → ℝ) (p β L : ℝ) (c a : S → List S → ℝ)
    (hp1 : p < 1) (hp0 : p ≠ 0) (hβ : 0 ≤ β) (hY : ∀ s, 0 < Y s) (hπ : ∀ s s', 0 ≤ π s s')
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (hw0 : ∀ s, 0 < w s)
    (hc : ∀ s h, 0 < c s h) (ha : ∀ s h, 0 < a s h)
    (hsame : ∀ s h s', a s' (s :: h) = a s (s :: h))
    (hbud : ∀ s h, c s h + price Y w p s * a s (s :: h) ≤ a s h * (price Y w p s + Y s))
    (s : S) (h : List S)
    (hT : Tendsto (fun n => planT π β p w a n s h) atTop (𝓝 0))
    (hU : Tendsto (fun n => planU π β p c n s h) atTop (𝓝 L)) :
    L ≤ 1 / p * a s h ^ p * w s := by
  have hb : ∀ n, planU π β p c n s h ≤ 1 / p * a s h ^ p * w s - planT π β p w a n s h := by
    intro n
    have := plan_le π Y w p β c a hp1 hp0 hβ hY hπ hw hw0 hc ha hsame hbud n s h
    rw [planW_split] at this
    linarith
  have hR : Tendsto (fun n => 1 / p * a s h ^ p * w s - planT π β p w a n s h) atTop
      (𝓝 (1 / p * a s h ^ p * w s)) := by
    simpa using hT.const_sub (1 / p * a s h ^ p * w s)
  exact le_of_tendsto_of_tendsto' hU hR hb

/-- **Holding forever attains `V`.**  Consuming `θ Y` every period and keeping share `θ`. -/
theorem hold_attains (π : S → S → ℝ) (Y w : S → ℝ) (p β θ : ℝ)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hY : ∀ s, 0 < Y s) (hπ : ∀ s s', 0 ≤ π s s')
    (hπ1 : ∀ s, ∑ s', π s s' = 1)
    (hw : ∀ s, w s = Y s ^ p + β * ∑ s', π s s' * w s') (hθ : 0 < θ) (s : S) (h : List S) :
    Tendsto (fun n => planU π β p (fun s _ => θ * Y s) n s h) atTop
      (𝓝 (1 / p * θ ^ p * w s)) := by
  have hW : ∀ n s h, planW π β p w (fun s _ => θ * Y s) (fun _ _ => θ) n s h
      = 1 / p * θ ^ p * w s := by
    intro n
    induction n with
    | zero => intro s h; rfl
    | succ n ih =>
      intro s h
      simp only [planW, ih]
      exact crra_bellman_eq π Y w p β θ s hY hw hθ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ r, |1 / p * θ ^ p * w r| := ⟨_, rfl⟩
  have hTb : ∀ n s h, |planT π β p w (fun _ _ => θ) n s h| ≤ β ^ n * M := by
    intro n
    induction n with
    | zero =>
      intro s h
      simp only [planT, pow_zero, one_mul, hM]
      exact Finset.single_le_sum (f := fun r => |1 / p * θ ^ p * w r|)
        (fun r _ => abs_nonneg _) (mem_univ s)
    | succ n ih =>
      intro s h
      simp only [planT]
      rw [abs_mul, abs_of_nonneg hβ]
      have h1 := Finset.abs_sum_le_sum_abs
        (fun s' => π s s' * planT π β p w (fun _ _ => θ) n s' (s :: h)) univ
      have h2 : ∑ s', |π s s' * planT π β p w (fun _ _ => θ) n s' (s :: h)|
          ≤ ∑ s', π s s' * (β ^ n * M) := by
        apply Finset.sum_le_sum
        intro s' _
        rw [abs_mul, abs_of_nonneg (hπ s s')]
        exact mul_le_mul_of_nonneg_left (ih s' _) (hπ s s')
      rw [← Finset.sum_mul, hπ1 s, one_mul] at h2
      calc β * |∑ s', π s s' * planT π β p w (fun _ _ => θ) n s' (s :: h)|
          ≤ β * (β ^ n * M) := mul_le_mul_of_nonneg_left (h1.trans h2) hβ
        _ = β ^ (n + 1) * M := by ring
  have hg : Tendsto (fun n => β ^ n * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const M
  have hT : Tendsto (fun n => planT π β p w (fun _ _ => θ) n s h) atTop (𝓝 0) := by
    have hg' : Tendsto (fun n => -(β ^ n * M)) atTop (𝓝 0) := by simpa using hg.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg' hg
      (fun n => neg_le_of_abs_le (hTb n s h)) (fun n => le_of_abs_le (hTb n s h))
  have e : ∀ n, planU π β p (fun s _ => θ * Y s) n s h
      = 1 / p * θ ^ p * w s - planT π β p w (fun _ _ => θ) n s h := by
    intro n
    have := hW n s h
    rw [planW_split] at this
    linarith
  simp only [e]
  simpa using hT.const_sub (1 / p * θ ^ p * w s)

end LucasCRRA

end

#print axioms LucasCRRA.lin_fixed
#print axioms LucasCRRA.lin_fixed_pos
#print axioms LucasCRRA.price_euler
#print axioms LucasCRRA.price_unique
#print axioms LucasCRRA.crra_bellman
#print axioms LucasCRRA.crra_bellman_eq
#print axioms LucasCRRA.plan_le
#print axioms LucasCRRA.plan_optimal
#print axioms LucasCRRA.hold_attains
