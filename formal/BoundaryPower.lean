import Mathlib

/-!
Stage 291: boundary allocations for power utility, and a corner that the Inada condition
excludes.

Includes stage 288 (`boundary_improvable`, `optimum_interior`, square-root instance) and adds:
* `power_inada`, `power_lip` — `u c = c ^ p` with `0 < p < 1` satisfies both hypotheses;
* `power_optimum_interior` — for every such power, an optimum over non-negative bundles is
  strictly positive;
* `cara_not_inada` — exponential utility fails the Inada condition;
* `cara_corner_optimal` — with exponential utility a bundle with zero consumption in one
  state is optimal over non-negative bundles: without the Inada condition, corners occur.
-/

noncomputable section

open Finset BigOperators

namespace BoundaryPower

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem boundary_improvable (π p x : S → ℝ) (u : ℝ → ℝ) (s0 t : S)
    (hπ : ∀ s, 0 < π s) (hp : ∀ s, 0 < p s)
    (h0 : x s0 = 0) (ht : 0 < x t) (hx : ∀ s, 0 ≤ x s)
    (hlip : ∀ a : ℝ, 0 < a → ∃ M : ℝ, ∀ c d : ℝ, a ≤ d → d ≤ c → u c - u d ≤ M * (c - d))
    (hinada : ∀ K : ℝ, ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → K * δ ≤ u δ - u 0) :
    ∃ x' : S → ℝ, (∀ r, 0 ≤ x' r) ∧ ∑ r, p r * x' r = ∑ r, p r * x r ∧
      ∑ r, π r * u (x r) < ∑ r, π r * u (x' r) := by
  have hst : s0 ≠ t := by
    intro h
    rw [h] at h0
    linarith
  have hps := hp s0
  have hpt := hp t
  have hπs := hπ s0
  have hπt := hπ t
  obtain ⟨M, hM⟩ := hlip (x t / 2) (by linarith)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (π t * M + 1) * p s0 / (π s0 * p t) := ⟨_, rfl⟩
  obtain ⟨δ0, hδ0, hK⟩ := hinada K
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (x t / 2) (δ0 * p s0 / p t) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (div_pos (mul_pos hδ0 hps) hpt)
  have hε1 : ε ≤ x t / 2 := by
    rw [hεdef]
    exact min_le_left _ _
  have hε2 : ε ≤ δ0 * p s0 / p t := by
    rw [hεdef]
    exact min_le_right _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * p t / p s0 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (mul_pos hε0 hpt) hps
  have hδle : δ ≤ δ0 := by
    rw [hδdef, div_le_iff₀ hps]
    exact (le_div_iff₀ hpt).1 hε2
  have hgain := hK δ hδpos hδle
  have hloss := hM (x t) (x t - ε) (by linarith) (by linarith)
  have hpδ : δ * p s0 = ε * p t := by
    rw [hδdef]
    exact div_mul_cancel₀ _ hps.ne'
  have hKp : K * (π s0 * p t) = (π t * M + 1) * p s0 := by
    rw [hKdef]
    exact div_mul_cancel₀ _ (mul_pos hπs hpt).ne'
  have hKδ : π s0 * (K * δ) = (π t * M + 1) * ε := by
    have e1 : π s0 * (K * δ) * p t = (π t * M + 1) * ε * p t := by
      calc π s0 * (K * δ) * p t = K * (π s0 * p t) * δ := by ring
        _ = (π t * M + 1) * (δ * p s0) := by rw [hKp]; ring
        _ = (π t * M + 1) * ε * p t := by rw [hpδ]; ring
    exact mul_right_cancel₀ hpt.ne' e1
  obtain ⟨x', hx'⟩ : ∃ x' : S → ℝ,
      ∀ r, x' r = x r + (if r = s0 then δ else 0) - (if r = t then ε else 0) := ⟨_, fun _ => rfl⟩
  have hA : x' s0 = δ := by
    rw [hx', h0]
    simp [hst]
  have hB : x' t = x t - ε := by
    rw [hx']
    simp [hst.symm]
  have hC : ∀ r, r ≠ s0 → r ≠ t → x' r = x r := by
    intro r h1 h2
    rw [hx']
    simp [h1, h2]
  refine ⟨x', ?_, ?_, ?_⟩
  · intro r
    by_cases h1 : r = s0
    · rw [h1, hA]
      exact hδpos.le
    · by_cases h2 : r = t
      · rw [h2, hB]
        linarith
      · rw [hC r h1 h2]
        exact hx r
  · have eb : ∀ r, p r * x' r
        = p r * x r + (if r = s0 then p r * δ else 0) - (if r = t then p r * ε else 0) := by
      intro r
      rw [hx']
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun r _ => eb r), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    linarith
  · have eu : ∀ r, π r * u (x r) + (if r = s0 then π r * (K * δ) else 0)
        - (if r = t then π r * (M * ε) else 0) ≤ π r * u (x' r) := by
      intro r
      by_cases h1 : r = s0
      · have e1 : (if r = s0 then π r * (K * δ) else 0) = π s0 * (K * δ) := by simp [h1]
        have e2 : (if r = t then π r * (M * ε) else 0) = 0 := by simp [h1, hst]
        rw [e1, e2, h1, hA, h0]
        have := mul_le_mul_of_nonneg_left hgain hπs.le
        linarith
      · by_cases h2 : r = t
        · have e1 : (if r = s0 then π r * (K * δ) else 0) = 0 := by simp [h1]
          have e2 : (if r = t then π r * (M * ε) else 0) = π t * (M * ε) := by simp [h2]
          rw [e1, e2, h2, hB]
          have := mul_le_mul_of_nonneg_left hloss hπt.le
          have e3 : x t - (x t - ε) = ε := by ring
          rw [e3] at this
          linarith
        · have e1 : (if r = s0 then π r * (K * δ) else 0) = 0 := by simp [h1]
          have e2 : (if r = t then π r * (M * ε) else 0) = 0 := by simp [h2]
          rw [e1, e2, hC r h1 h2]
          linarith
    have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => eu r)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq'] at hs
    simp only [Finset.mem_univ, ite_true] at hs
    linarith

/-- **An optimum over non-negative bundles is interior.** -/
theorem optimum_interior (π p x : S → ℝ) (u : ℝ → ℝ) (t : S)
    (hπ : ∀ s, 0 < π s) (hp : ∀ s, 0 < p s) (ht : 0 < x t) (hx : ∀ s, 0 ≤ x s)
    (hlip : ∀ a : ℝ, 0 < a → ∃ M : ℝ, ∀ c d : ℝ, a ≤ d → d ≤ c → u c - u d ≤ M * (c - d))
    (hinada : ∀ K : ℝ, ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → K * δ ≤ u δ - u 0)
    (hopt : ∀ x' : S → ℝ, (∀ r, 0 ≤ x' r) → ∑ r, p r * x' r ≤ ∑ r, p r * x r →
      ∑ r, π r * u (x' r) ≤ ∑ r, π r * u (x r)) :
    ∀ s, 0 < x s := by
  intro s
  by_contra h
  have h0 : x s = 0 := le_antisymm (not_lt.1 h) (hx s)
  obtain ⟨x', h1, h2, h3⟩ := boundary_improvable π p x u s t hπ hp h0 ht hx hlip hinada
  have := hopt x' h1 h2.le
  linarith

theorem sqrt_inada (K : ℝ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → K * δ ≤ Real.sqrt δ - Real.sqrt 0 := by
  have ha : 0 < |K| + 1 := by positivity
  refine ⟨1 / (|K| + 1) ^ 2, by positivity, fun δ hδ hle => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt δ := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact Real.sqrt_pos.2 hδ
  have hδr : δ = r ^ 2 := by
    rw [hr]
    exact (Real.sq_sqrt hδ.le).symm
  have h1 : δ * (|K| + 1) ^ 2 ≤ 1 := (le_div_iff₀ (by positivity)).1 hle
  have har : (|K| + 1) * r ≤ 1 := by
    by_contra hc
    push Not at hc
    have h2 := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1) hc
    rw [hδr] at h1
    linarith
  have h3 : K * r ^ 2 ≤ (|K| + 1) * r ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (sq_nonneg r)
  have h4 : (|K| + 1) * r * r ≤ 1 * r := mul_le_mul_of_nonneg_right har hr0.le
  rw [Real.sqrt_zero, sub_zero, ← hr, hδr]
  linarith

theorem sqrt_lip (a : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, ∀ c d : ℝ, a ≤ d → d ≤ c → Real.sqrt c - Real.sqrt d ≤ M * (c - d) := by
  refine ⟨1 / Real.sqrt a, fun c d had hdc => ?_⟩
  have hra : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have h1 : Real.sqrt a ≤ Real.sqrt d := Real.sqrt_le_sqrt had
  have h2 : Real.sqrt d ≤ Real.sqrt c := Real.sqrt_le_sqrt hdc
  have hc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt (by linarith)
  have hd2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by linarith)
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hra]
  have h3 := mul_nonneg (sub_nonneg.2 h2)
    (by linarith : 0 ≤ Real.sqrt c + Real.sqrt d - Real.sqrt a)
  nlinarith [h3, hc2, hd2]

/-- The square-root felicity: a non-negative optimum is strictly positive. -/
theorem sqrt_optimum_interior (π p x : S → ℝ) (t : S)
    (hπ : ∀ s, 0 < π s) (hp : ∀ s, 0 < p s) (ht : 0 < x t) (hx : ∀ s, 0 ≤ x s)
    (hopt : ∀ x' : S → ℝ, (∀ r, 0 ≤ x' r) → ∑ r, p r * x' r ≤ ∑ r, p r * x r →
      ∑ r, π r * Real.sqrt (x' r) ≤ ∑ r, π r * Real.sqrt (x r)) :
    ∀ s, 0 < x s :=
  optimum_interior π p x Real.sqrt t hπ hp ht hx sqrt_lip sqrt_inada hopt


theorem power_inada (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (K : ℝ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → K * δ ≤ δ ^ p - (0 : ℝ) ^ p := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max K 1 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by rw [hm]; exact le_max_right _ _
  have hmK : K ≤ m := by rw [hm]; exact le_max_left _ _
  have hm0 : 0 < m := by linarith
  have hq : p - 1 ≠ 0 := by linarith
  refine ⟨m ^ (1 / (p - 1)), Real.rpow_pos_of_pos hm0 _, fun δ hδ hle => ?_⟩
  have h1 : (m ^ (1 / (p - 1))) ^ (p - 1) = m := by
    rw [← Real.rpow_mul hm0.le, one_div_mul_cancel hq, Real.rpow_one]
  have h2 : (m ^ (1 / (p - 1))) ^ (p - 1) ≤ δ ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos hδ hle (by linarith)
  rw [h1] at h2
  have h3 : δ ^ p = δ ^ (p - 1) * δ := by
    rw [Real.rpow_sub_one hδ.ne']
    exact (div_mul_cancel₀ _ hδ.ne').symm
  rw [Real.zero_rpow hp.ne', sub_zero, h3]
  have := mul_le_mul_of_nonneg_right (hmK.trans h2) hδ.le
  linarith

/-- Concavity of `c ^ p` for `0 < p < 1`: `c ^ p ≤ d ^ p + p d ^ (p - 1) (c - d)`. -/
theorem crra_sg (p c d : ℝ) (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c) (hd : 0 < d) :
    c ^ p ≤ d ^ p + p * d ^ (p - 1) * (c - d) := by
  have ht : 0 < c / d := div_pos hc hd
  have hB : 0 < d ^ p := Real.rpow_pos_of_pos hd p
  have hA : c ^ p = (c / d) ^ p * d ^ p := by
    rw [← Real.mul_rpow ht.le hd.le, div_mul_cancel₀ c hd.ne']
  have hm : d ^ (p - 1) * (c - d) = d ^ p * (c / d - 1) := by
    rw [Real.rpow_sub_one hd.ne']
    field_simp
  have hk : (c / d) ^ p ≤ 1 + p * (c / d - 1) := by
    have h := Real.geom_mean_le_arith_mean2_weighted hp.le (by linarith : (0 : ℝ) ≤ 1 - p)
      ht.le zero_le_one (by ring : p + (1 - p) = 1)
    rw [Real.one_rpow, mul_one] at h
    linarith
  have h2 := mul_le_mul_of_nonneg_right hk hB.le
  have e : p * d ^ (p - 1) * (c - d) = p * (d ^ (p - 1) * (c - d)) := by ring
  rw [hA, e, hm]
  linarith

theorem power_lip (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, ∀ c d : ℝ, a ≤ d → d ≤ c → c ^ p - d ^ p ≤ M * (c - d) := by
  refine ⟨p * a ^ (p - 1), fun c d had hdc => ?_⟩
  have hd : 0 < d := by linarith
  have hc : 0 < c := by linarith
  have hsg := crra_sg p c d hp hp1 hc hd
  have h2 : d ^ (p - 1) ≤ a ^ (p - 1) := Real.rpow_le_rpow_of_nonpos ha had (by linarith)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hp.le)
    (by linarith : (0 : ℝ) ≤ c - d)
  linarith

/-- **Every power utility `c ^ p`, `0 < p < 1`: a non-negative optimum is interior.** -/
theorem power_optimum_interior (π q x : S → ℝ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : S)
    (hπ : ∀ s, 0 < π s) (hq : ∀ s, 0 < q s) (ht : 0 < x t) (hx : ∀ s, 0 ≤ x s)
    (hopt : ∀ x' : S → ℝ, (∀ r, 0 ≤ x' r) → ∑ r, q r * x' r ≤ ∑ r, q r * x r →
      ∑ r, π r * x' r ^ p ≤ ∑ r, π r * x r ^ p) :
    ∀ s, 0 < x s :=
  optimum_interior π q x (fun c => c ^ p) t hπ hq ht hx (power_lip p hp hp1)
    (power_inada p hp hp1) hopt

/-- **Exponential utility fails the Inada condition.** -/
theorem cara_not_inada :
    ¬ ∀ K : ℝ, ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      K * δ ≤ -Real.exp (-δ) - -Real.exp (-0) := by
  intro h
  obtain ⟨δ0, hδ0, hK⟩ := h 2
  have h1 := hK δ0 hδ0 le_rfl
  have h2 := Real.add_one_le_exp (-δ0)
  rw [neg_zero, Real.exp_zero] at h1
  linarith

/-- Supergradient of exponential utility. -/
theorem cara_sg (x a : ℝ) : -Real.exp (-x) ≤ -Real.exp (-a) + Real.exp (-a) * (x - a) := by
  have e : Real.exp (-x) = Real.exp (-a) * Real.exp (a - x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - x)) (Real.exp_pos (-a)).le
  rw [e]
  linarith

/-- **A corner optimum without the Inada condition.**  Two equally likely states, prices
`1` and `2e`, wealth `1`, utility `-exp (-c)`.  The bundle `(1, 0)`, with nothing in the
second state, is optimal over non-negative bundles. -/
theorem cara_corner_optimal (c1 c2 : ℝ) (h2 : 0 ≤ c2)
    (hb : c1 + 2 * Real.exp 1 * c2 ≤ 1) :
    -Real.exp (-c1) - Real.exp (-c2) ≤ -Real.exp (-1) - Real.exp (-0) := by
  have s1 := cara_sg c1 1
  have s2 := cara_sg c2 0
  have hee : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have h3 : Real.exp (-1) * (c1 - 1) ≤ Real.exp (-1) * (-(2 * Real.exp 1 * c2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have h4 : Real.exp (-1) * (-(2 * Real.exp 1 * c2)) = -(2 * c2) := by
    linear_combination (-(2 * c2)) * hee
  rw [neg_zero, Real.exp_zero] at s2 ⊢
  linarith

end BoundaryPower

end
#print axioms BoundaryPower.power_inada
#print axioms BoundaryPower.crra_sg
#print axioms BoundaryPower.power_lip
#print axioms BoundaryPower.power_optimum_interior
#print axioms BoundaryPower.cara_not_inada
#print axioms BoundaryPower.cara_sg
#print axioms BoundaryPower.cara_corner_optimal
