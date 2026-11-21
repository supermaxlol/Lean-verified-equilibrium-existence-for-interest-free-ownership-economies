import Mathlib

/-!
# Stage 373: a unique two-period path with heterogeneous patience and `γ ≠ 1`

Stage 370 proved uniqueness of the finite-horizon equilibrium path of stage 364 for log utility,
for common patience, and for horizon one. It left open heterogeneous patience with `γ ≠ 1` and
horizon above one, where the distribution path depends on returns and returns on the future
distribution. This file closes that case for horizon two under a band condition on `γ`. The
stage 364 definitions are restated unchanged (`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`).

* `I γ D q = 1 / q + 1 / (D q ^ (1 / γ))`: with stage 370's identity `qs_eq`, a household's
  saving rate times the return is `1 / I`. `I_lower`, `I_upper` compare `I` at two returns and
  two coefficients using only bounds on the powers `t` and `t ^ (1 / γ)` of the return ratio.
* `reduce`: a two-period equilibrium satisfies two clearing equations in the two returns
  `Q 0`, `Q 1` alone (`R1`: date 0; `R2`: date 1 with the date-1 distribution substituted).
* `reduced_unique`: the two equations have at most one positive solution whenever there are
  `lo, hi` with `0 < lo ≤ 1 ≤ hi`, `lo ≤ 1 / γ ≤ hi` and `(hi − lo)(hi + lo) < lo²`. Proof: if
  `Q 1 < Q' 1`, the date-0 equation bounds how far `Q 0` can fall; with that bound every date-1
  term at the primed returns exceeds the unprimed one by a factor above one, which contradicts
  date-1 clearing. Equal date-1 returns give equal date-0 returns by monotonicity.
* **`unique_two_period`**: for heterogeneous patience and horizon two, two equilibria with
  positive returns have the same returns and the same distributions at every date, under the
  band condition above, `g ≥ 0`, `amp ≥ 0` and `g σ c ≥ 0`.
* **`unique_two_period_band`**: the band condition holds whenever `1 / 2 < γ ^ 2 < 2`, so the
  two-period path is unique for `γ` between `1 / √2` and `√2` (log utility `γ = 1` included).

Limits: horizon two only. For horizon above two the same comparison has to be carried through
a chain of dates and is not done here; neither a contraction bound nor an induction on the
horizon is given. The band `1 / 2 < γ ^ 2 < 2` is a sufficient condition from crude bounds, not
a sharp one: for `γ` outside it uniqueness is neither proved nor refuted, and no example of two
distinct equilibrium paths is given. Uniqueness is among equilibria with positive returns at
dates 0 and 1. The infinite-horizon path is not covered.
-/

noncomputable section

open Finset BigOperators

namespace PathUniquenessHetero

variable {H : Type*} [Fintype H]

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def amp (g σ : ℝ) : ℝ := 1 + g * (1 - σ)

def T (g σ c : ℝ) (s x : H → ℝ) (h : H) : ℝ :=
  (amp g σ * (s h * x h / B s x) + g * σ * c) / (1 + g)

def F (b : ℝ) (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k + 1, t => b * r t * (1 + F b r k (t + 1))

def ex (γ : ℝ) : ℝ := (1 - γ) / γ

def rr (γ : ℝ) (Q : ℕ → ℝ) (t : ℕ) : ℝ := Q t ^ ex γ

def savN (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (t : ℕ) (h : H) : ℝ :=
  F (b h) (rr γ Q) (N - t) t / (1 + F (b h) (rr γ Q) (N - t) t)

def IsEqN (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t < N, x (t + 1) = T g σ c (savN γ b N Q t) (x t) ∧
    Q t = 1 / B (savN γ b N Q t) (x t)

/-- Stage 370's identity: saving rate times return. -/
theorem qs_eq (γ b G q : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hG : 0 ≤ G) (hq : 0 < q) :
    q * (b * q ^ ex γ * (1 + G) / (1 + b * q ^ ex γ * (1 + G))) =
      (q⁻¹ + (b * (1 + G) * q ^ (1 / γ))⁻¹)⁻¹ := by
  have e : q ^ (1 / γ) = q * q ^ ex γ := by
    have : 1 / γ = 1 + ex γ := by unfold ex; field_simp; ring
    rw [this, Real.rpow_add hq, Real.rpow_one]
  rw [e]
  have hp : 0 < q ^ ex γ := Real.rpow_pos_of_pos hq _
  have h1 : 0 < 1 + G := by linarith
  have h2 : 0 < b * q ^ ex γ * (1 + G) := by positivity
  field_simp
  ring

/-- The reciprocal of saving rate times return. -/
def I (γ D q : ℝ) : ℝ := q⁻¹ + (D * q ^ (1 / γ))⁻¹

theorem I_pos (γ D q : ℝ) (hD : 0 < D) (hq : 0 < q) : 0 < I γ D q := by
  unfold I
  have : 0 < q ^ (1 / γ) := Real.rpow_pos_of_pos hq _
  positivity

/-- `I` is strictly decreasing in the return. -/
theorem I_anti (γ D q q' : ℝ) (hγ : 0 < γ) (hD : 0 < D) (hq : 0 < q) (hqq : q < q') :
    I γ D q' < I γ D q := by
  have hq' : 0 < q' := by linarith
  have h1 : q'⁻¹ < q⁻¹ := (inv_lt_inv₀ hq' hq).2 hqq
  have h2 : q ^ (1 / γ) < q' ^ (1 / γ) := Real.rpow_lt_rpow hq.le hqq (by positivity)
  have h3 : (D * q' ^ (1 / γ))⁻¹ < (D * q ^ (1 / γ))⁻¹ := by
    have : 0 < q ^ (1 / γ) := Real.rpow_pos_of_pos hq _
    exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (mul_lt_mul_of_pos_left h2 hD)
  unfold I
  linarith

/-- `I` at return `q'` and coefficient `D'`, written with the ratio `t = q / q'`. -/
theorem I_rel (γ D' q q' t : ℝ) (ht : 0 < t) (hq' : 0 < q') (hq : q = t * q') :
    I γ D' q' = t * q⁻¹ + t ^ (1 / γ) * (D' * q ^ (1 / γ))⁻¹ := by
  have e : q ^ (1 / γ) = t ^ (1 / γ) * q' ^ (1 / γ) := by
    rw [hq, Real.mul_rpow ht.le hq'.le]
  have a : 0 < t ^ (1 / γ) := Real.rpow_pos_of_pos ht _
  have b : 0 < q' ^ (1 / γ) := Real.rpow_pos_of_pos hq' _
  unfold I
  rw [e, hq]
  by_cases hD : D' = 0
  · subst hD
    simp only [zero_mul, inv_zero, mul_zero, add_zero]
    field_simp
  · field_simp

theorem I_lower (γ D D' q q' t a M : ℝ) (ht : 0 < t) (hq' : 0 < q') (hq : q = t * q')
    (hD : 0 < D) (hD' : 0 < D') (ha : a ≤ t) (ha' : a ≤ t ^ (1 / γ)) (hDD : D' ≤ M * D)
    (hM : 1 ≤ M) : a * I γ D q ≤ M * I γ D' q' := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have hX : 0 < q ^ (1 / γ) := Real.rpow_pos_of_pos hq0 _
  have htg : 0 < t ^ (1 / γ) := Real.rpow_pos_of_pos ht _
  rw [I_rel γ D' q q' t ht hq' hq]
  unfold I
  have k1 : a * q⁻¹ ≤ M * (t * q⁻¹) := by
    have : 0 < q⁻¹ := inv_pos.2 hq0
    have u1 := mul_le_mul_of_nonneg_right ha this.le
    have u2 := mul_le_mul_of_nonneg_right hM (mul_pos ht this).le
    linarith
  have k2 : (D * q ^ (1 / γ))⁻¹ ≤ M * (D' * q ^ (1 / γ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    nlinarith
  have k3 : a * (D * q ^ (1 / γ))⁻¹ ≤ M * (t ^ (1 / γ) * (D' * q ^ (1 / γ))⁻¹) := by
    have h0 : 0 < (D * q ^ (1 / γ))⁻¹ := by positivity
    have h1 : 0 < (D' * q ^ (1 / γ))⁻¹ := by positivity
    calc a * (D * q ^ (1 / γ))⁻¹ ≤ t ^ (1 / γ) * (D * q ^ (1 / γ))⁻¹ :=
          mul_le_mul_of_nonneg_right ha' h0.le
      _ ≤ t ^ (1 / γ) * (M * (D' * q ^ (1 / γ))⁻¹) := mul_le_mul_of_nonneg_left k2 htg.le
      _ = M * (t ^ (1 / γ) * (D' * q ^ (1 / γ))⁻¹) := by ring
  nlinarith

theorem I_upper (γ D D' q q' t A M : ℝ) (ht : 0 < t) (hq' : 0 < q') (hq : q = t * q')
    (hD : 0 < D) (hD' : 0 < D') (hA : t ≤ A) (hA' : t ^ (1 / γ) ≤ A) (hDD : D ≤ M * D')
    (hM : 1 ≤ M) : I γ D' q' ≤ A * M * I γ D q := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have hX : 0 < q ^ (1 / γ) := Real.rpow_pos_of_pos hq0 _
  have htg : 0 < t ^ (1 / γ) := Real.rpow_pos_of_pos ht _
  have hA0 : 0 < A := lt_of_lt_of_le ht hA
  rw [I_rel γ D' q q' t ht hq' hq]
  unfold I
  have k1 : t * q⁻¹ ≤ A * M * q⁻¹ := by
    have : 0 < q⁻¹ := inv_pos.2 hq0
    have u1 := mul_le_mul_of_nonneg_right hA this.le
    have u2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hA0.le) this.le
    linarith
  have k2 : (D' * q ^ (1 / γ))⁻¹ ≤ M * (D * q ^ (1 / γ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    nlinarith
  have k3 : t ^ (1 / γ) * (D' * q ^ (1 / γ))⁻¹ ≤ A * M * (D * q ^ (1 / γ))⁻¹ := by
    have h0 : 0 < (D' * q ^ (1 / γ))⁻¹ := by positivity
    calc t ^ (1 / γ) * (D' * q ^ (1 / γ))⁻¹ ≤ A * (D' * q ^ (1 / γ))⁻¹ :=
          mul_le_mul_of_nonneg_right hA' h0.le
      _ ≤ A * (M * (D * q ^ (1 / γ))⁻¹) := mul_le_mul_of_nonneg_left k2 hA0.le
      _ = A * M * (D * q ^ (1 / γ))⁻¹ := by ring
  nlinarith

omit [Fintype H] in
theorem inv_cmp (a M X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (h : a * X ≤ M * Y) :
    a * Y⁻¹ ≤ M * X⁻¹ := by
  have hp : 0 ≤ X⁻¹ * Y⁻¹ := by positivity
  calc a * Y⁻¹ = (a * X) * (X⁻¹ * Y⁻¹) := by field_simp
    _ ≤ (M * Y) * (X⁻¹ * Y⁻¹) := mul_le_mul_of_nonneg_right h hp
    _ = M * X⁻¹ := by field_simp

/-! ## The two clearing equations -/

/-- The date-0 coefficient of household `h` given the date-1 return. -/
def Dφ (γ : ℝ) (b : H → ℝ) (Q1 : ℝ) (h : H) : ℝ := b h * (1 + b h * Q1 ^ ex γ)

omit [Fintype H] in
theorem Dφ_pos (γ : ℝ) (b : H → ℝ) (Q1 : ℝ) (hb : ∀ h, 0 < b h) (hQ : 0 < Q1) (h : H) :
    0 < Dφ γ b Q1 h := by
  unfold Dφ
  have := hb h
  have : 0 < Q1 ^ ex γ := Real.rpow_pos_of_pos hQ _
  positivity

def R1 (γ : ℝ) (b x0 : H → ℝ) (Q0 Q1 : ℝ) : Prop :=
  ∑ h, (I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h = 1

def R2 (γ : ℝ) (b x0 : H → ℝ) (A K C Q0 Q1 : ℝ) : Prop :=
  ∑ h, (I γ (b h) Q1)⁻¹ * (A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K) = C

omit [Fintype H] in
theorem savN0 (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (h : H) :
    savN γ b 2 Q 0 h = b h * Q 0 ^ ex γ * (1 + b h * Q 1 ^ ex γ * (1 + 0)) /
      (1 + b h * Q 0 ^ ex γ * (1 + b h * Q 1 ^ ex γ * (1 + 0))) := rfl

omit [Fintype H] in
theorem savN1 (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (h : H) :
    savN γ b 2 Q 1 h = b h * Q 1 ^ ex γ * (1 + 0) / (1 + b h * Q 1 ^ ex γ * (1 + 0)) := rfl

omit [Fintype H] in
theorem qs0 (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 < b h)
    (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) (h : H) :
    Q 0 * savN γ b 2 Q 0 h = (I γ (Dφ γ b (Q 1) h) (Q 0))⁻¹ := by
  have hG : 0 ≤ b h * Q 1 ^ ex γ * (1 + 0) := by
    have := Real.rpow_pos_of_pos hQ1 (ex γ)
    have := hb h
    positivity
  rw [savN0, qs_eq γ (b h) _ (Q 0) hγ (hb h) hG hQ0]
  simp only [I, Dφ, add_zero, mul_one]

omit [Fintype H] in
theorem qs1 (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 < b h)
    (hQ1 : 0 < Q 1) (h : H) :
    Q 1 * savN γ b 2 Q 1 h = (I γ (b h) (Q 1))⁻¹ := by
  rw [savN1, qs_eq γ (b h) 0 (Q 1) hγ (hb h) le_rfl hQ1]
  simp only [I, add_zero, mul_one]

/-- **A two-period equilibrium satisfies the two clearing equations.** -/
theorem reduce (g σ c γ : ℝ) (b x0 : H → ℝ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 2 x Q) (hγ : 0 < γ) (hb : ∀ h, 0 < b h) (hg : 0 ≤ g)
    (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) :
    R1 γ b x0 (Q 0) (Q 1) ∧ R2 γ b x0 (amp g σ) (g * σ * c) (1 + g) (Q 0) (Q 1) := by
  obtain ⟨h0, hs⟩ := hE
  obtain ⟨ex0, eq0⟩ := hs 0 (by norm_num)
  obtain ⟨-, eq1⟩ := hs 1 (by norm_num)
  rw [h0] at ex0 eq0
  have hB0 : B (savN γ b 2 Q 0) x0 ≠ 0 := by
    intro hz; rw [hz, div_zero] at eq0; linarith
  have hB1 : B (savN γ b 2 Q 1) (x 1) ≠ 0 := by
    intro hz; rw [hz, div_zero] at eq1; linarith
  have k0 : Q 0 * B (savN γ b 2 Q 0) x0 = 1 := by
    rw [eq0]; field_simp
  have k1 : Q 1 * B (savN γ b 2 Q 1) (x 1) = 1 := by
    rw [eq1]; field_simp
  have hR1 : R1 γ b x0 (Q 0) (Q 1) := by
    unfold R1
    rw [← k0, B, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← qs0 γ b Q hγ hb hQ0 hQ1 h]
    ring
  refine ⟨hR1, ?_⟩
  have hx1 : ∀ h, x 1 h = (amp g σ * ((I γ (Dφ γ b (Q 1) h) (Q 0))⁻¹ * x0 h) + g * σ * c) /
      (1 + g) := by
    intro h
    rw [ex0, T, ← qs0 γ b Q hγ hb hQ0 hQ1 h]
    congr 2
    rw [eq0]
    field_simp
  unfold R2
  have hg1 : (1 + g) ≠ 0 := by positivity
  have : ∑ h, (I γ (b h) (Q 1))⁻¹ * x 1 h = 1 := by
    rw [← k1, B, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← qs1 γ b Q hγ hb hQ1 h]
    ring
  have h2 : ∑ h, (I γ (b h) (Q 1))⁻¹ * x 1 h = (∑ h, (I γ (b h) (Q 1))⁻¹ *
      (amp g σ * ((I γ (Dφ γ b (Q 1) h) (Q 0))⁻¹ * x0 h) + g * σ * c)) / (1 + g) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hx1]
    ring
  rw [h2, div_eq_one_iff_eq hg1] at this
  exact this

/-! ## Uniqueness of the solution of the two equations -/

theorem exists_pos (x : H → ℝ) (v : H → ℝ) (hx : ∀ h, 0 ≤ x h) (hs : ∑ h, v h * x h = 1) :
    ∃ h, 0 < x h := by
  by_contra hn
  push Not at hn
  have : ∑ h, v h * x h = 0 := Finset.sum_eq_zero fun h _ => by
    rw [le_antisymm (hn h) (hx h), mul_zero]
  linarith

/-- Same date-1 return: at most one date-0 return clears. -/
theorem date0_unique (γ : ℝ) (b x0 : H → ℝ) (Q1 q q' : ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 < b h)
    (hx : ∀ h, 0 ≤ x0 h) (hQ1 : 0 < Q1) (hq : 0 < q) (hq' : 0 < q')
    (h1 : R1 γ b x0 q Q1) (h2 : R1 γ b x0 q' Q1) : q = q' := by
  obtain ⟨h0, hh0⟩ := exists_pos x0 _ hx h1
  have mono : ∀ p p', 0 < p → p < p' →
      ∑ h, (I γ (Dφ γ b Q1 h) p)⁻¹ * x0 h < ∑ h, (I γ (Dφ γ b Q1 h) p')⁻¹ * x0 h := by
    intro p p' hp hpp
    have hp' : 0 < p' := by linarith
    have key : ∀ h, (I γ (Dφ γ b Q1 h) p)⁻¹ < (I γ (Dφ γ b Q1 h) p')⁻¹ := fun h =>
      (inv_lt_inv₀ (I_pos γ _ p (Dφ_pos γ b Q1 hb hQ1 h) hp)
        (I_pos γ _ p' (Dφ_pos γ b Q1 hb hQ1 h) hp')).2
        (I_anti γ _ p p' hγ (Dφ_pos γ b Q1 hb hQ1 h) hp hpp)
    refine Finset.sum_lt_sum (fun h _ => mul_le_mul_of_nonneg_right (key h).le (hx h))
      ⟨h0, Finset.mem_univ _, mul_lt_mul_of_pos_right (key h0) hh0⟩
  unfold R1 at h1 h2
  rcases lt_trichotomy q q' with h | h | h
  · have := mono q q' hq h; linarith
  · exact h
  · have := mono q' q hq' h; linarith

/-- The core comparison: a strictly higher date-1 return is impossible. -/
theorem no_lt (γ lo hi : ℝ) (b x0 : H → ℝ) (A K C Q0 Q1 Q0' Q1' : ℝ) (hγ : 0 < γ)
    (hlo : 0 < lo) (hlo1 : lo ≤ 1) (hlog : lo ≤ 1 / γ) (hhi1 : 1 ≤ hi) (hhig : 1 / γ ≤ hi)
    (hcond : (hi - lo) * (hi + lo) < lo * lo) (hb : ∀ h, 0 < b h) (hx : ∀ h, 0 ≤ x0 h)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hQ0 : 0 < Q0) (hQ1 : 0 < Q1) (hQ0' : 0 < Q0')
    (hlt : Q1 < Q1') (e1 : R1 γ b x0 Q0 Q1) (e1' : R1 γ b x0 Q0' Q1')
    (e2 : R2 γ b x0 A K C Q0 Q1) (e2' : R2 γ b x0 A K C Q0' Q1') : False := by
  have hQ1' : 0 < Q1' := by linarith
  set μ := Q1' / Q1 with hμ
  have hμ1 : 1 < μ := by rw [hμ, lt_div_iff₀ hQ1]; linarith
  have hμ0 : 0 < μ := by linarith
  have hQ1e : Q1' = μ * Q1 := by rw [hμ]; field_simp
  set t := Q0 / Q0' with htd
  have ht : 0 < t := div_pos hQ0 hQ0'
  have hQ0e : Q0 = t * Q0' := by rw [htd]; field_simp
  set e := hi - lo with he
  have he0 : 0 ≤ e := by linarith
  have hexg : ex γ = 1 / γ - 1 := by unfold ex; field_simp
  have hexu : ex γ ≤ e := by rw [hexg, he]; linarith
  have hexl : -e ≤ ex γ := by rw [hexg, he]; linarith
  have hme : 1 ≤ μ ^ e := Real.one_le_rpow hμ1.le he0
  -- the date-0 coefficients at the two date-1 returns
  have hDup : ∀ h, Dφ γ b Q1' h ≤ μ ^ e * Dφ γ b Q1 h := by
    intro h
    have hp : 0 < Q1 ^ ex γ := Real.rpow_pos_of_pos hQ1 _
    have h1 : μ ^ ex γ ≤ μ ^ e := Real.rpow_le_rpow_of_exponent_le hμ1.le hexu
    have hbh := hb h
    unfold Dφ
    rw [hQ1e, Real.mul_rpow hμ0.le hQ1.le]
    have : b h * μ ^ ex γ * Q1 ^ ex γ ≤ μ ^ e * (b h * Q1 ^ ex γ) := by
      have := mul_le_mul_of_nonneg_right h1 (mul_pos hbh hp).le
      linarith
    nlinarith
  have hDdn : ∀ h, Dφ γ b Q1 h ≤ μ ^ e * Dφ γ b Q1' h := by
    intro h
    have hp : 0 < Q1 ^ ex γ := Real.rpow_pos_of_pos hQ1 _
    have h1 : 1 ≤ μ ^ (e + ex γ) := Real.one_le_rpow hμ1.le (by linarith)
    rw [Real.rpow_add hμ0] at h1
    have hbh := hb h
    unfold Dφ
    rw [hQ1e, Real.mul_rpow hμ0.le hQ1.le]
    have : b h * Q1 ^ ex γ ≤ μ ^ e * (b h * (μ ^ ex γ * Q1 ^ ex γ)) := by
      have := mul_le_mul_of_nonneg_right h1 (mul_pos hbh hp).le
      nlinarith
    nlinarith
  set Tm := max t 1 with hTm
  have hT1 : 1 ≤ Tm := le_max_right _ _
  have hT0 : 0 < Tm := by linarith
  -- step A: the date-0 equation bounds `Tm`
  have stepA : Tm ^ lo ≤ μ ^ e := by
    rcases le_total t 1 with h | h
    · rw [hTm, max_eq_right h, Real.one_rpow]; exact hme
    · rw [hTm, max_eq_left h]
      have a1 : t ^ lo ≤ t := by
        calc t ^ lo ≤ t ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h hlo1
          _ = t := Real.rpow_one t
      have a2 : t ^ lo ≤ t ^ (1 / γ) := Real.rpow_le_rpow_of_exponent_le h hlog
      have key : ∀ h, t ^ lo * (I γ (Dφ γ b Q1' h) Q0')⁻¹ ≤ μ ^ e * (I γ (Dφ γ b Q1 h) Q0)⁻¹ :=
        fun h => inv_cmp _ _ _ _ (I_pos γ _ _ (Dφ_pos γ b Q1 hb hQ1 h) hQ0)
          (I_pos γ _ _ (Dφ_pos γ b Q1' hb hQ1' h) hQ0')
          (I_lower γ _ _ Q0 Q0' t _ _ ht hQ0' hQ0e (Dφ_pos γ b Q1 hb hQ1 h)
            (Dφ_pos γ b Q1' hb hQ1' h) a1 a2 (hDup h) hme)
      unfold R1 at e1 e1'
      calc t ^ lo = t ^ lo * ∑ h, (I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h := by rw [e1', mul_one]
        _ = ∑ h, t ^ lo * (I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
        _ ≤ ∑ h, μ ^ e * (I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h :=
          Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (key h) (hx h)
        _ = μ ^ e * ∑ h, (I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
        _ = μ ^ e := by rw [e1, mul_one]
  -- step B: the date-0 terms at the primed returns are not much smaller
  set Af := Tm ^ hi * μ ^ e with hAf
  have hThi : 1 ≤ Tm ^ hi := Real.one_le_rpow hT1 (by linarith)
  have hAf1 : 1 ≤ Af := by rw [hAf]; nlinarith
  have stepB : ∀ h, (I γ (Dφ γ b Q1 h) Q0)⁻¹ ≤ Af * (I γ (Dφ γ b Q1' h) Q0')⁻¹ := by
    intro h
    have b1 : t ≤ Tm ^ hi := by
      calc t ≤ Tm := le_max_left _ _
        _ = Tm ^ (1:ℝ) := (Real.rpow_one Tm).symm
        _ ≤ Tm ^ hi := Real.rpow_le_rpow_of_exponent_le hT1 hhi1
    have b2 : t ^ (1 / γ) ≤ Tm ^ hi := by
      calc t ^ (1 / γ) ≤ Tm ^ (1 / γ) :=
            Real.rpow_le_rpow ht.le (le_max_left _ _) (by positivity)
        _ ≤ Tm ^ hi := Real.rpow_le_rpow_of_exponent_le hT1 hhig
    have := I_upper γ _ _ Q0 Q0' t (Tm ^ hi) (μ ^ e) ht hQ0' hQ0e (Dφ_pos γ b Q1 hb hQ1 h)
      (Dφ_pos γ b Q1' hb hQ1' h) b1 b2 (hDdn h) hme
    have := inv_cmp 1 Af _ _ (I_pos γ _ _ (Dφ_pos γ b Q1' hb hQ1' h) hQ0')
      (I_pos γ _ _ (Dφ_pos γ b Q1 hb hQ1 h) hQ0) (by rw [hAf]; linarith)
    linarith
  -- step C: the bound factor is below `μ ^ lo`
  have stepC : Af < μ ^ lo := by
    have hAf0 : 0 ≤ Af := by linarith
    refine (Real.rpow_lt_rpow_iff hAf0 (Real.rpow_nonneg hμ0.le _) hlo).1 ?_
    have c1 : Af ^ lo = (Tm ^ lo) ^ hi * μ ^ (e * lo) := by
      rw [hAf, Real.mul_rpow (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hμ0.le _),
        ← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hμ0.le, mul_comm hi lo]
    have c2 : (Tm ^ lo) ^ hi ≤ μ ^ (e * hi) := by
      rw [Real.rpow_mul hμ0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) stepA (by linarith)
    have c3 : μ ^ (e * hi) * μ ^ (e * lo) < (μ ^ lo) ^ lo := by
      rw [← Real.rpow_add hμ0, ← Real.rpow_mul hμ0.le]
      exact Real.rpow_lt_rpow_of_exponent_lt hμ1 (by rw [he]; nlinarith)
    rw [c1]
    calc (Tm ^ lo) ^ hi * μ ^ (e * lo) ≤ μ ^ (e * hi) * μ ^ (e * lo) :=
          mul_le_mul_of_nonneg_right c2 (Real.rpow_nonneg hμ0.le _)
      _ < (μ ^ lo) ^ lo := c3
  -- step D: the date-1 factor rises by at least `μ ^ lo`
  have stepD : ∀ h, μ ^ lo * (I γ (b h) Q1)⁻¹ ≤ (I γ (b h) Q1')⁻¹ := by
    intro h
    have d1 : μ ^ lo ≤ μ := by
      calc μ ^ lo ≤ μ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hμ1.le hlo1
        _ = μ := Real.rpow_one μ
    have d2 : μ ^ lo ≤ μ ^ (1 / γ) := Real.rpow_le_rpow_of_exponent_le hμ1.le hlog
    have := I_lower γ (b h) (b h) Q1' Q1 μ (μ ^ lo) 1 hμ0 hQ1 hQ1e (hb h) (hb h) d1 d2
      (by linarith) le_rfl
    have := inv_cmp _ _ _ _ (I_pos γ _ _ (hb h) hQ1') (I_pos γ _ _ (hb h) hQ1) this
    linarith
  -- step E: date-1 clearing fails at the primed returns
  have term : ∀ h, μ ^ lo * ((I γ (b h) Q1)⁻¹ * (A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K)) ≤
      Af * ((I γ (b h) Q1')⁻¹ * (A * ((I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h) + K)) := by
    intro h
    have p1 : 0 ≤ (I γ (Dφ γ b Q1 h) Q0)⁻¹ := (inv_pos.2 (I_pos γ _ _ (Dφ_pos γ b Q1 hb hQ1 h)
      hQ0)).le
    have p2 : 0 ≤ (I γ (b h) Q1')⁻¹ := (inv_pos.2 (I_pos γ _ _ (hb h) hQ1')).le
    have s1 : 0 ≤ A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K := by
      have := mul_nonneg hA (mul_nonneg p1 (hx h)); linarith
    have s2 : A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K ≤
        Af * (A * ((I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h) + K) := by
      have q1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (stepB h) (hx h)) hA
      have q2 : K ≤ Af * K := by nlinarith
      nlinarith
    calc μ ^ lo * ((I γ (b h) Q1)⁻¹ * (A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K))
        = (μ ^ lo * (I γ (b h) Q1)⁻¹) * (A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K) := by ring
      _ ≤ (I γ (b h) Q1')⁻¹ * (A * ((I γ (Dφ γ b Q1 h) Q0)⁻¹ * x0 h) + K) :=
          mul_le_mul_of_nonneg_right (stepD h) s1
      _ ≤ (I γ (b h) Q1')⁻¹ * (Af * (A * ((I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h) + K)) :=
          mul_le_mul_of_nonneg_left s2 p2
      _ = Af * ((I γ (b h) Q1')⁻¹ * (A * ((I γ (Dφ γ b Q1' h) Q0')⁻¹ * x0 h) + K)) := by ring
  unfold R2 at e2 e2'
  have hsum : μ ^ lo * C ≤ Af * C := by
    have := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) => term h
    rw [← Finset.mul_sum, ← Finset.mul_sum, e2, e2'] at this
    exact this
  have := (mul_le_mul_iff_of_pos_right hC).1 hsum
  linarith

/-- **The two clearing equations have at most one positive solution** under the band
condition. -/
theorem reduced_unique (γ lo hi : ℝ) (b x0 : H → ℝ) (A K C Q0 Q1 Q0' Q1' : ℝ) (hγ : 0 < γ)
    (hlo : 0 < lo) (hlo1 : lo ≤ 1) (hlog : lo ≤ 1 / γ) (hhi1 : 1 ≤ hi) (hhig : 1 / γ ≤ hi)
    (hcond : (hi - lo) * (hi + lo) < lo * lo) (hb : ∀ h, 0 < b h) (hx : ∀ h, 0 ≤ x0 h)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 < C) (hQ0 : 0 < Q0) (hQ1 : 0 < Q1) (hQ0' : 0 < Q0')
    (hQ1' : 0 < Q1') (e1 : R1 γ b x0 Q0 Q1) (e1' : R1 γ b x0 Q0' Q1')
    (e2 : R2 γ b x0 A K C Q0 Q1) (e2' : R2 γ b x0 A K C Q0' Q1') : Q0 = Q0' ∧ Q1 = Q1' := by
  rcases lt_trichotomy Q1 Q1' with h | h | h
  · exact (no_lt γ lo hi b x0 A K C Q0 Q1 Q0' Q1' hγ hlo hlo1 hlog hhi1 hhig hcond hb hx hA hK
      hC hQ0 hQ1 hQ0' h e1 e1' e2 e2').elim
  · subst h
    exact ⟨date0_unique γ b x0 Q1 Q0 Q0' hγ hb hx hQ1 hQ0 hQ0' e1 e1', rfl⟩
  · exact (no_lt γ lo hi b x0 A K C Q0' Q1' Q0 Q1 hγ hlo hlo1 hlog hhi1 hhig hcond hb hx hA hK
      hC hQ0' hQ1' hQ0 h e1' e1 e2' e2).elim

/-! ## The two-period path -/

/-- **Heterogeneous patience, `γ ≠ 1`, horizon two: the equilibrium path is unique** under the
band condition. -/
theorem unique_two_period (g σ c γ lo hi : ℝ) (b x0 : H → ℝ) (hγ : 0 < γ) (hlo : 0 < lo)
    (hlo1 : lo ≤ 1) (hlog : lo ≤ 1 / γ) (hhi1 : 1 ≤ hi) (hhig : 1 / γ ≤ hi)
    (hcond : (hi - lo) * (hi + lo) < lo * lo) (hb : ∀ h, 0 < b h) (hx0 : ∀ h, 0 ≤ x0 h)
    (hg : 0 ≤ g) (hamp : 0 ≤ amp g σ) (hgsc : 0 ≤ g * σ * c) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 2 x Q) (hE' : IsEqN g σ c γ b x0 2 x' Q')
    (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) (hQ0' : 0 < Q' 0) (hQ1' : 0 < Q' 1) :
    (∀ t < 2, Q t = Q' t) ∧ ∀ t ≤ 2, x t = x' t := by
  obtain ⟨a1, a2⟩ := reduce g σ c γ b x0 x Q hE hγ hb hg hQ0 hQ1
  obtain ⟨a1', a2'⟩ := reduce g σ c γ b x0 x' Q' hE' hγ hb hg hQ0' hQ1'
  obtain ⟨q0, q1⟩ := reduced_unique γ lo hi b x0 (amp g σ) (g * σ * c) (1 + g) (Q 0) (Q 1)
    (Q' 0) (Q' 1) hγ hlo hlo1 hlog hhi1 hhig hcond hb hx0 hamp hgsc (by linarith) hQ0 hQ1
    hQ0' hQ1' a1 a1' a2 a2'
  have s0 : savN γ b 2 Q 0 = savN γ b 2 Q' 0 := by
    funext h; rw [savN0, savN0, q0, q1]
  have s1 : savN γ b 2 Q 1 = savN γ b 2 Q' 1 := by
    funext h; rw [savN1, savN1, q1]
  have x1 : x 1 = x' 1 := by
    rw [(hE.2 0 (by norm_num)).1, (hE'.2 0 (by norm_num)).1, hE.1, hE'.1, s0]
  have x2 : x 2 = x' 2 := by
    rw [(hE.2 1 (by norm_num)).1, (hE'.2 1 (by norm_num)).1, x1, s1]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · interval_cases t
    · exact q0
    · exact q1
  · interval_cases t
    · rw [hE.1, hE'.1]
    · exact x1
    · exact x2

/-- The band condition holds for `1 / 2 < γ ^ 2 < 2`. -/
theorem band (γ : ℝ) (hγ : 0 < γ) (h1 : 1 / 2 < γ ^ 2) (h2 : γ ^ 2 < 2) :
    ∃ lo hi, 0 < lo ∧ lo ≤ 1 ∧ lo ≤ 1 / γ ∧ 1 ≤ hi ∧ 1 / γ ≤ hi ∧
      (hi - lo) * (hi + lo) < lo * lo := by
  have hu : γ * (1 / γ) = 1 := by field_simp
  have hu0 : 0 < 1 / γ := by positivity
  rcases le_total γ 1 with h | h
  · have hu1 : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
    refine ⟨1, 1 / γ, one_pos, le_rfl, hu1, hu1, le_rfl, ?_⟩
    nlinarith [mul_pos hγ hu0]
  · have hu1 : 1 / γ ≤ 1 := by rw [div_le_iff₀ hγ]; linarith
    refine ⟨1 / γ, 1, hu0, hu1, le_rfl, le_rfl, hu1, ?_⟩
    nlinarith [mul_pos hγ hu0]

/-- **The two-period path is unique for `1 / √2 < γ < √2`** with heterogeneous patience. -/
theorem unique_two_period_band (g σ c γ : ℝ) (b x0 : H → ℝ) (hγ : 0 < γ)
    (h1 : 1 / 2 < γ ^ 2) (h2 : γ ^ 2 < 2) (hb : ∀ h, 0 < b h) (hx0 : ∀ h, 0 ≤ x0 h)
    (hg : 0 ≤ g) (hamp : 0 ≤ amp g σ) (hgsc : 0 ≤ g * σ * c) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 2 x Q) (hE' : IsEqN g σ c γ b x0 2 x' Q')
    (hQ0 : 0 < Q 0) (hQ1 : 0 < Q 1) (hQ0' : 0 < Q' 0) (hQ1' : 0 < Q' 1) :
    (∀ t < 2, Q t = Q' t) ∧ ∀ t ≤ 2, x t = x' t := by
  obtain ⟨lo, hi, a, b1, c1, d, e, f⟩ := band γ hγ h1 h2
  exact unique_two_period g σ c γ lo hi b x0 hγ a b1 c1 d e f hb hx0 hg hamp hgsc x x' Q Q'
    hE hE' hQ0 hQ1 hQ0' hQ1'

end PathUniquenessHetero

end

#print axioms PathUniquenessHetero.I_lower
#print axioms PathUniquenessHetero.I_upper
#print axioms PathUniquenessHetero.reduce
#print axioms PathUniquenessHetero.date0_unique
#print axioms PathUniquenessHetero.no_lt
#print axioms PathUniquenessHetero.reduced_unique
#print axioms PathUniquenessHetero.unique_two_period
#print axioms PathUniquenessHetero.band
#print axioms PathUniquenessHetero.unique_two_period_band
