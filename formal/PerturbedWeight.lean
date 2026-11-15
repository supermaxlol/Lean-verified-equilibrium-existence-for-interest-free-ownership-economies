import Mathlib

/-!
# Stage 342: perturbing a weight that has Afriat numbers with a margin

Debreu's consumer `k` trades `x p = w p · (e_k − p_k p)`, so with any Afriat numbers `V, λ` the
continuum Afriat inequalities read

    V p − V q ≤ λ q · w p · c p q,      c p q = q_k − p_k (q·p).

Suppose a base weight `w₀` has Afriat numbers `V, λ₀` with a *margin*: the inequality holds with
`m p q` to spare.  Then the perturbed weight `w = w₀ (1 + δ)` has the Afriat numbers
`V, λ₀ / (1 + δ)` as soon as the change in `δ` is paid for by the margin
(`perturb_afriat`).  With a margin proportional to `d(p,q) · λ₀ w₀ |c|`, a Lipschitz bound on
`δ` suffices (`perturb_afriat_lip`).  The new `λ` keeps uniform bounds (`lam_bounds`).

Debreu's weight `Z_k + A p_k = A p_k (1 + Z_k / (A p_k))` has this shape, with `δ` of size and
Lipschitz constant `O(1/A)` on `S_ε` when `Z` is Lipschitz.  So a uniform margin for the pure
weight `p_k` would settle Debreu's weights for large `A`.  **That margin is not proved here.**
-/

noncomputable section

namespace PerturbedWeight

/-- **Perturbation with a margin.** -/
theorem perturb_afriat {X : Type*} (P : Set X) (V lam0 w0 δ : X → ℝ) (c m : X → X → ℝ)
    (hδ : ∀ q ∈ P, -1 < δ q) (hlam0 : ∀ q ∈ P, 0 ≤ lam0 q) (hw0 : ∀ p ∈ P, 0 ≤ w0 p)
    (hmargin : ∀ p ∈ P, ∀ q ∈ P, V p - V q + m p q ≤ lam0 q * w0 p * c p q)
    (hsmall : ∀ p ∈ P, ∀ q ∈ P,
      |δ p - δ q| * lam0 q * w0 p * |c p q| ≤ m p q * (1 + δ q)) :
    ∀ p ∈ P, ∀ q ∈ P,
      V p - V q ≤ lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q := by
  intro p hp q hq
  have h1 := hmargin p hp q hq
  have h2 := hsmall p hp q hq
  have hq1 : 0 < 1 + δ q := by linarith [hδ q hq]
  have hl := hlam0 q hq
  have hw := hw0 p hp
  have e : lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q =
      lam0 q * w0 p * c p q + (δ p - δ q) * (lam0 q * w0 p * c p q) / (1 + δ q) := by
    field_simp
    ring
  have h3 : -(m p q * (1 + δ q)) ≤ (δ p - δ q) * (lam0 q * w0 p * c p q) := by
    have h4 := neg_abs_le ((δ p - δ q) * (lam0 q * w0 p * c p q))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg hw] at h4
    linarith
  have h5 : -m p q ≤ (δ p - δ q) * (lam0 q * w0 p * c p q) / (1 + δ q) := by
    rw [le_div_iff₀ hq1]
    linarith
  rw [e]
  linarith

/-- **Lipschitz perturbations.**  If the margin is `μ · d(p,q) · λ₀ w₀ |c|`, the
perturbation satisfies `|δ| ≤ δ₀ < 1` and `|δ p − δ q| ≤ κ d(p,q)`, and `κ ≤ μ (1 − δ₀)`,
then the perturbed weight has Afriat numbers. -/
theorem perturb_afriat_lip {X : Type*} (P : Set X) (V lam0 w0 δ : X → ℝ) (c d : X → X → ℝ)
    (μ κ δ0 : ℝ) (hδ0 : δ0 < 1) (hμ : 0 ≤ μ)
    (hδ : ∀ q ∈ P, |δ q| ≤ δ0) (hlam0 : ∀ q ∈ P, 0 ≤ lam0 q) (hw0 : ∀ p ∈ P, 0 ≤ w0 p)
    (hd : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ d p q)
    (hmargin : ∀ p ∈ P, ∀ q ∈ P,
      V p - V q + μ * d p q * (lam0 q * w0 p * |c p q|) ≤ lam0 q * w0 p * c p q)
    (hlip : ∀ p ∈ P, ∀ q ∈ P, |δ p - δ q| ≤ κ * d p q) (hκ : κ ≤ μ * (1 - δ0)) :
    ∀ p ∈ P, ∀ q ∈ P,
      V p - V q ≤ lam0 q / (1 + δ q) * (w0 p * (1 + δ p)) * c p q := by
  refine perturb_afriat P V lam0 w0 δ c (fun p q => μ * d p q * (lam0 q * w0 p * |c p q|))
    (fun q hq => ?_) hlam0 hw0 hmargin fun p hp q hq => ?_
  · have := neg_abs_le (δ q)
    linarith [hδ q hq]
  · have hA : 0 ≤ lam0 q * w0 p * |c p q| :=
      mul_nonneg (mul_nonneg (hlam0 q hq) (hw0 p hp)) (abs_nonneg _)
    have hq1 : 1 - δ0 ≤ 1 + δ q := by
      have := neg_abs_le (δ q)
      linarith [hδ q hq]
    have h1 : |δ p - δ q| * (lam0 q * w0 p * |c p q|) ≤ κ * d p q * (lam0 q * w0 p * |c p q|) :=
      mul_le_mul_of_nonneg_right (hlip p hp q hq) hA
    have h2 : κ * d p q * (lam0 q * w0 p * |c p q|) ≤
        μ * (1 - δ0) * d p q * (lam0 q * w0 p * |c p q|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (hd p hp q hq)) hA
    have h3 : μ * (1 - δ0) * d p q * (lam0 q * w0 p * |c p q|) ≤
        μ * d p q * (lam0 q * w0 p * |c p q|) * (1 + δ q) := by
      have h4 : 0 ≤ μ * d p q * (lam0 q * w0 p * |c p q|) :=
        mul_nonneg (mul_nonneg hμ (hd p hp q hq)) hA
      have h5 := mul_le_mul_of_nonneg_left hq1 h4
      linarith
    have e : |δ p - δ q| * lam0 q * w0 p * |c p q| =
        |δ p - δ q| * (lam0 q * w0 p * |c p q|) := by ring
    rw [e]
    linarith

/-- **The new multipliers stay uniformly bounded.** -/
theorem lam_bounds (l Λ δ0 lam0 δq : ℝ) (hl : 0 ≤ l) (hδ0 : δ0 < 1) (h1 : l ≤ lam0)
    (h2 : lam0 ≤ Λ) (hδ : |δq| ≤ δ0) :
    l / (1 + δ0) ≤ lam0 / (1 + δq) ∧ lam0 / (1 + δq) ≤ Λ / (1 - δ0) := by
  have ha := neg_abs_le δq
  have hb := le_abs_self δq
  have hq1 : 0 < 1 + δq := by linarith
  have hd1 : 0 < 1 - δ0 := by linarith
  have hd2 : 0 < 1 + δ0 := by linarith
  have hlam0 : 0 ≤ lam0 := hl.trans h1
  constructor
  · rw [div_le_div_iff₀ hd2 hq1]
    have : l * (1 + δq) ≤ lam0 * (1 + δ0) := by
      have h3 : l * (1 + δq) ≤ lam0 * (1 + δq) := mul_le_mul_of_nonneg_right h1 hq1.le
      have h4 : lam0 * (1 + δq) ≤ lam0 * (1 + δ0) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0
      linarith
    exact this
  · rw [div_le_div_iff₀ hq1 hd1]
    have h3 : lam0 * (1 - δ0) ≤ Λ * (1 - δ0) := mul_le_mul_of_nonneg_right h2 hd1.le
    have h4 : Λ * (1 - δ0) ≤ Λ * (1 + δq) := by
      have : 0 ≤ Λ := hlam0.trans h2
      exact mul_le_mul_of_nonneg_left (by linarith) this
    linarith

/-- **Debreu's weight is a small perturbation of `A p_k`.**  On `S_ε`, if `|Z_k| ≤ M` and
`Z_k` is `Lz`-Lipschitz (against a distance `d` that dominates the change in the coordinate
`k`), then `δ = Z_k / (A p_k)` has `|δ| ≤ M / (A ε)` and
`|δ p − δ q| ≤ (Lz / (A ε) + M / (A ε²)) d(p,q)`. -/
theorem debreu_delta {X : Type*} (P : Set X) (pk Zk : X → ℝ) (d : X → X → ℝ)
    (A ε M Lz : ℝ) (hA : 0 < A) (hε : 0 < ε) (hpk : ∀ q ∈ P, ε ≤ pk q)
    (hZ : ∀ q ∈ P, |Zk q| ≤ M) (hZl : ∀ p ∈ P, ∀ q ∈ P, |Zk p - Zk q| ≤ Lz * d p q)
    (hpl : ∀ p ∈ P, ∀ q ∈ P, |pk p - pk q| ≤ d p q) (hLz : 0 ≤ Lz) :
    (∀ q ∈ P, |Zk q / (A * pk q)| ≤ M / (A * ε)) ∧
      ∀ p ∈ P, ∀ q ∈ P, |Zk p / (A * pk p) - Zk q / (A * pk q)| ≤
        (Lz / (A * ε) + M / (A * ε ^ 2)) * d p q := by
  have hpos : ∀ q ∈ P, 0 < A * pk q := fun q hq => mul_pos hA (hε.trans_le (hpk q hq))
  have hAe : 0 < A * ε := mul_pos hA hε
  constructor
  · intro q hq
    rw [abs_div, abs_of_pos (hpos q hq), div_le_div_iff₀ (hpos q hq) hAe]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hZ q hq)
    have h1 : |Zk q| * (A * ε) ≤ M * (A * ε) := mul_le_mul_of_nonneg_right (hZ q hq) hAe.le
    have h2 : M * (A * ε) ≤ M * (A * pk q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpk q hq) hA.le) hM
    linarith
  · intro p hp q hq
    have hp0 := hpos p hp
    have hq0 := hpos q hq
    have e : Zk p / (A * pk p) - Zk q / (A * pk q) =
        (Zk p - Zk q) / (A * pk p) + Zk q * (pk q - pk p) / (A * pk p * pk q) := by
      have : pk q ≠ 0 := (hε.trans_le (hpk q hq)).ne'
      have : pk p ≠ 0 := (hε.trans_le (hpk p hp)).ne'
      field_simp
      ring
    rw [e]
    have hdpq : 0 ≤ d p q := (abs_nonneg _).trans (hpl p hp q hq)
    have hM : 0 ≤ M := (abs_nonneg _).trans (hZ q hq)
    have t1 : |(Zk p - Zk q) / (A * pk p)| ≤ Lz / (A * ε) * d p q := by
      rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
      have h1 : Lz * d p q ≤ Lz / (A * ε) * d p q * (A * pk p) := by
        have : Lz / (A * ε) * d p q * (A * pk p) = Lz * d p q * (pk p / ε) := by
          field_simp
        rw [this]
        have h2 : 1 ≤ pk p / ε := (one_le_div hε).2 (hpk p hp)
        nlinarith [mul_nonneg hLz hdpq]
      linarith [hZl p hp q hq]
    have hpp : 0 < pk p := hε.trans_le (hpk p hp)
    have hpq : 0 < pk q := hε.trans_le (hpk q hq)
    have t2 : |Zk q * (pk q - pk p) / (A * pk p * pk q)| ≤ M / (A * ε ^ 2) * d p q := by
      have hD : 0 < A * pk p * pk q := by positivity
      rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_mul]
      have h1 : |Zk q| * |pk q - pk p| ≤ M * d p q := by
        rw [abs_sub_comm]
        exact mul_le_mul (hZ q hq) (hpl p hp q hq) (abs_nonneg _) hM
      have h2 : M * d p q ≤ M / (A * ε ^ 2) * d p q * (A * pk p * pk q) := by
        have : M / (A * ε ^ 2) * d p q * (A * pk p * pk q) =
            M * d p q * ((pk p / ε) * (pk q / ε)) := by
          field_simp
        rw [this]
        have h3 : 1 ≤ pk p / ε := (one_le_div hε).2 (hpk p hp)
        have h4 : 1 ≤ pk q / ε := (one_le_div hε).2 (hpk q hq)
        have h5 : 1 ≤ (pk p / ε) * (pk q / ε) := by nlinarith
        nlinarith [mul_nonneg hM hdpq]
      linarith
    calc |(Zk p - Zk q) / (A * pk p) + Zk q * (pk q - pk p) / (A * pk p * pk q)|
        ≤ |(Zk p - Zk q) / (A * pk p)| + |Zk q * (pk q - pk p) / (A * pk p * pk q)| :=
          abs_add_le _ _
      _ ≤ Lz / (A * ε) * d p q + M / (A * ε ^ 2) * d p q := add_le_add t1 t2
      _ = (Lz / (A * ε) + M / (A * ε ^ 2)) * d p q := by ring

end PerturbedWeight

end

#print axioms PerturbedWeight.perturb_afriat
#print axioms PerturbedWeight.perturb_afriat_lip
#print axioms PerturbedWeight.lam_bounds
#print axioms PerturbedWeight.debreu_delta
