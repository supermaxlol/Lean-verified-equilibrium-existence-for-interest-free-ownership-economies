import Mathlib

/-!
# Stage 363: convergence, equilibrium paths, and wealth-dependent patience

Continues stage 357 (definitions restated so the file stands alone). With full access, the
equilibrium issuance step is `T x h = (amp · s h x h / B s x + g σ c) / (1 + g)` (stage 357,
`step_full`), where `B s x = ∑ s k x k` and `amp = 1 + g (1 − σ)`.

* **Convergence** (`contract_step`, `converges`, `converges_tendsto`, `fixed_unique`): with
  constant saving rates, `σ > 0` and `g > 0`, every positive starting distribution converges to
  the long-run distribution `y`, geometrically: `|x n h − y h| ≤ λ ^ n (K0 − 1)` with the explicit
  factor `λ = 1 − g σ c / (1 + g) < 1`, where `K0` bounds the initial spread of the ratios
  `x h / y h`. The proof is a contraction of that spread: each step maps the ratio
  `x h / y h` to a convex combination of `(x h / y h) / ρ` and `1`.
* **Equilibrium with forward-looking saving**:
  - log utility (`γ = 1`, `log_equilibrium`, `log_equilibrium_unique`, `log_equilibrium_converges`):
    for every positive starting distribution a perfect-foresight equilibrium path exists, it is
    unique, and it converges to the long-run distribution;
  - CRRA steady state (`steady_equilibrium`): for any curvature `γ ≠ 0`, the long-run
    distribution with the constant return `R = B ^ (−γ)` is a perfect-foresight equilibrium, under
    `b h B ^ (γ − 1) < 1` (automatic when `γ ≥ 1`, `steady_condition`). The long-run
    distribution does not depend on `γ` except through the patience factors `b`.
* **Wealth-dependent patience** (`Tp`, `rank_preserved`, `threshold_equalizes`, `ex_equal_rest`,
  `ex_unequal_rest`): if patience rises with wealth, the step never reverses the ranking. With a
  threshold `θ` (patience `hi` at or above it), if `(1 + g) θ ≤ g σ c` every household is above the
  threshold after one step and the economy converges to equal shares. Without that, identical
  households can stay unequal forever: an explicit two-household economy has both the equal
  distribution and `(1/5, 4/5)` as rest points.

Limits: convergence is proved for constant saving rates (exogenous, or the log-utility
equilibrium); a transitional equilibrium path with forward-looking saving and `γ ≠ 1` is not
proved to exist (only its steady state); the return on saved ownership is `1 / B` as in stage 357;
the threshold result is a sufficient condition, and existence of a long-run distribution with
general wealth-dependent patience is not proved.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace OwnershipDynamics

variable {H : Type*} [Fintype H]

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def amp (g σ : ℝ) : ℝ := 1 + g * (1 - σ)

/-- The full-access equilibrium issuance step (stage 357, `step_full`). -/
def T (g σ c : ℝ) (s x : H → ℝ) (h : H) : ℝ :=
  (amp g σ * (s h * x h / B s x) + g * σ * c) / (1 + g)

def orbit (g σ c : ℝ) (s x0 : H → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | n + 1 => T g σ c s (orbit g σ c s x0 n)

/-- The contraction factor. -/
def lam (g σ c : ℝ) : ℝ := 1 - g * σ * c / (1 + g)

/-! ## Real-number lemmas -/

theorem ratio_form (a b u : ℝ) (hab : 0 < a + b) :
    (a * u + b) / (a + b) = 1 + a / (a + b) * (u - 1) := by
  field_simp
  ring

theorem ratio_upper (a b u l : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hl : a / (a + b) ≤ l) :
    (a * u + b) / (a + b) ≤ 1 + l * (max u 1 - 1) := by
  rw [ratio_form a b u (by linarith)]
  have hμ : 0 ≤ a / (a + b) := div_nonneg ha (by linarith)
  rcases le_total u 1 with hu | hu
  · rw [max_eq_right hu]
    nlinarith [mul_nonneg hμ (sub_nonneg.2 hu)]
  · rw [max_eq_left hu]
    nlinarith [mul_le_mul_of_nonneg_right hl (sub_nonneg.2 hu)]

theorem ratio_lower (a b u l : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hl : a / (a + b) ≤ l) :
    1 - l * (1 - min u 1) ≤ (a * u + b) / (a + b) := by
  rw [ratio_form a b u (by linarith)]
  have hμ : 0 ≤ a / (a + b) := div_nonneg ha (by linarith)
  rcases le_total u 1 with hu | hu
  · rw [min_eq_left hu]
    nlinarith [mul_le_mul_of_nonneg_right hl (sub_nonneg.2 hu)]
  · rw [min_eq_right hu]
    nlinarith [mul_nonneg hμ (sub_nonneg.2 hu)]

theorem combine (l K P Q : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1) (hK : 1 ≤ K) (hQ : Q ≤ 1)
    (hPQ : P ≤ K * Q) : 1 + l * (P - 1) ≤ (1 + l * (K - 1)) * (1 - l * (1 - Q)) := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1) h0)
    (mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hQ)), mul_nonneg h0 (sub_nonneg.2 hPQ)]

theorem max_min_bound (uh uk K : ℝ) (h1 : uh ≤ K * uk) (h2 : uh ≤ K) (h3 : 1 ≤ K * uk)
    (h4 : 1 ≤ K) : max uh 1 ≤ K * min uk 1 := by
  rcases le_total uk 1 with hu | hu
  · rw [min_eq_left hu]; exact max_le h1 h3
  · rw [min_eq_right hu, mul_one]; exact max_le h2 h4

/-- **The pairwise contraction.** -/
theorem pair_bound (ah ak b l K uh uk : ℝ) (hah : 0 ≤ ah) (hak : 0 ≤ ak) (hb : 0 < b)
    (hlh : ah / (ah + b) ≤ l) (hlk : ak / (ak + b) ≤ l) (h0 : 0 ≤ l) (h1 : l ≤ 1)
    (hK : 1 ≤ K) (h1' : uh ≤ K * uk) (h2 : uh ≤ K) (h3 : 1 ≤ K * uk) :
    (ah * uh + b) / (ah + b) ≤ (1 + l * (K - 1)) * ((ak * uk + b) / (ak + b)) :=
  calc (ah * uh + b) / (ah + b) ≤ 1 + l * (max uh 1 - 1) := ratio_upper ah b uh l hah hb hlh
    _ ≤ (1 + l * (K - 1)) * (1 - l * (1 - min uk 1)) :=
        combine l K _ _ h0 h1 hK (min_le_right _ _) (max_min_bound uh uk K h1' h2 h3 hK)
    _ ≤ (1 + l * (K - 1)) * ((ak * uk + b) / (ak + b)) :=
        mul_le_mul_of_nonneg_left (ratio_lower ak b uk l hak hb hlk) (by nlinarith)

/-! ## The step -/

theorem B_pos [Nonempty H] (s x : H → ℝ) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) :
    0 < B s x :=
  Finset.sum_pos (fun h _ => mul_pos (hs h) (hx h)) Finset.univ_nonempty

theorem amp_pos (g σ : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) : 0 < amp g σ := by
  unfold amp; nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]

theorem T_floor (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h) (h : H) :
    g * σ * c / (1 + g) ≤ T g σ c s x h := by
  unfold T
  have hB : 0 ≤ B s x := Finset.sum_nonneg fun k _ => mul_nonneg (hs k) (hx k)
  have hq : 0 ≤ s h * x h / B s x := div_nonneg (mul_nonneg (hs h) (hx h)) hB
  have := mul_nonneg (amp_pos g σ hg hσ1).le hq
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem T_pos (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 < c) (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h) (h : H) : 0 < T g σ c s x h :=
  lt_of_lt_of_le (div_pos (mul_pos (mul_pos hg hσ) hc0) (by linarith))
    (T_floor g σ c s x hg hσ1 hs hx h)

theorem T_sum (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hB : B s x ≠ 0)
    (hc : (Fintype.card H : ℝ) * c = 1) : ∑ h, T g σ c s x h = 1 := by
  unfold T
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e : ∑ h, s h * x h = B s x := rfl
  rw [e, div_self hB, div_eq_one_iff_eq (by linarith)]
  unfold amp
  linear_combination g * σ * hc

theorem fixed_eq (g σ c : ℝ) (s y : H → ℝ) (hg : 0 < g)
    (hfix : ∀ h, T g σ c s y h = y h) (j : H) :
    amp g σ * s j * y j / B s y + g * σ * c = (1 + g) * y j := by
  have e := hfix j
  unfold T at e
  rw [div_eq_iff (by linarith)] at e
  have e2 : amp g σ * s j * y j / B s y = amp g σ * (s j * y j / B s y) := by ring
  linarith

theorem B_ratio (s x y : H → ℝ) (hy : ∀ h, 0 < y h) :
    B s x = ∑ j, s j * y j * (x j / y j) := by
  unfold B
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, mul_div_cancel₀ _ (hy j).ne']

theorem le_one_of_sum (y : H → ℝ) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1) (j : H) : y j ≤ 1 :=
  hy1 ▸ Finset.single_le_sum (fun i _ => (hy i).le) (Finset.mem_univ j)

theorem lam_bounds [Nonempty H] (g σ c : ℝ) (s y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hs : ∀ h, 0 < s h) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1)
    (hfix : ∀ h, T g σ c s y h = y h) : 0 ≤ lam g σ c ∧ lam g σ c < 1 := by
  obtain ⟨j⟩ := ‹Nonempty H›
  have hb : 0 < g * σ * c := mul_pos (mul_pos hg hσ) hc0
  have ha : 0 ≤ amp g σ * s j * y j / B s y :=
    div_nonneg (mul_nonneg (mul_nonneg (amp_pos g σ hg hσ1).le (hs j).le) (hy j).le)
      (B_pos s y hs hy).le
  have e := fixed_eq g σ c s y hg hfix j
  have hyj := le_one_of_sum y hy hy1 j
  unfold lam
  constructor
  · have : g * σ * c / (1 + g) ≤ 1 := by
      rw [div_le_one (by linarith)]
      nlinarith
    linarith
  · have : 0 < g * σ * c / (1 + g) := div_pos hb (by linarith)
    linarith

/-- **One step contracts the spread of the ratios `x h / y h`** by the factor `λ`. -/
theorem contract_step [Nonempty H] (g σ c K : ℝ) (s x y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) (hy : ∀ h, 0 < y h)
    (hy1 : ∑ h, y h = 1) (hfix : ∀ h, T g σ c s y h = y h) (hK : 1 ≤ K)
    (hr : ∀ h k, x h / y h ≤ K * (x k / y k)) (h k : H) :
    T g σ c s x h / y h ≤ (1 + lam g σ c * (K - 1)) * (T g σ c s x k / y k) := by
  have hBy := B_pos s y hs hy
  have hBx := B_pos s x hs hx
  have hBy' := hBy.ne'
  have hBx' := hBx.ne'
  have hb : 0 < g * σ * c := mul_pos (mul_pos hg hσ) hc0
  have hamp := amp_pos g σ hg hσ1
  have hg1 : (1 + g) ≠ 0 := by linarith
  have ha : ∀ j, 0 ≤ amp g σ * s j * y j / B s y := fun j =>
    div_nonneg (mul_nonneg (mul_nonneg hamp.le (hs j).le) (hy j).le) hBy.le
  have hratio : ∀ j, T g σ c s x j / y j =
      (amp g σ * s j * y j / B s y * (x j / y j * (B s y / B s x)) + g * σ * c) /
        (amp g σ * s j * y j / B s y + g * σ * c) := fun j => by
    have hyj := (hy j).ne'
    rw [fixed_eq g σ c s y hg hfix j, div_eq_div_iff hyj (mul_pos (by linarith) (hy j)).ne']
    unfold T
    field_simp
  have hlam : ∀ j, amp g σ * s j * y j / B s y / (amp g σ * s j * y j / B s y + g * σ * c) ≤
      lam g σ c := fun j => by
    have e := fixed_eq g σ c s y hg hfix j
    have hpos : 0 < (1 + g) * y j := mul_pos (by linarith) (hy j)
    have e2 : amp g σ * s j * y j / B s y = (1 + g) * y j - g * σ * c := by linarith
    rw [e, e2, sub_div, div_self hpos.ne']
    unfold lam
    have hle : (1 + g) * y j ≤ 1 + g := by
      have := le_one_of_sum y hy hy1 j
      nlinarith
    have := div_le_div_of_nonneg_left hb.le hpos hle
    linarith
  obtain ⟨h0, h1⟩ := lam_bounds g σ c s y hg hσ hσ1 hc0 hs hy hy1 hfix
  have hq : 0 < B s y / B s x := div_pos hBy hBx
  have hu2 : x h / y h * (B s y / B s x) ≤ K * (x k / y k * (B s y / B s x)) := by
    have := mul_le_mul_of_nonneg_right (hr h k) hq.le
    linarith
  have hu1 : x h / y h * (B s y / B s x) ≤ K := by
    rw [← mul_div_assoc, div_le_iff₀ hBx, B_ratio s x y hy, Finset.mul_sum]
    unfold B
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsy : 0 ≤ s i * y i := mul_nonneg (hs i).le (hy i).le
    nlinarith [mul_le_mul_of_nonneg_left (hr h i) hsy]
  have hu3 : 1 ≤ K * (x k / y k * (B s y / B s x)) := by
    rw [show K * (x k / y k * (B s y / B s x)) = K * (x k / y k) * B s y / B s x by ring,
      le_div_iff₀ hBx, one_mul, B_ratio s x y hy]
    unfold B
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsy : 0 ≤ s i * y i := mul_nonneg (hs i).le (hy i).le
    nlinarith [mul_le_mul_of_nonneg_left (hr i k) hsy]
  rw [hratio h, hratio k]
  exact pair_bound _ _ _ _ _ _ _ (ha h) (ha k) hb (hlam h) (hlam k) h0 h1.le hK hu2 hu1 hu3

/-! ## Convergence -/

def Kseq (l K0 : ℝ) (n : ℕ) : ℝ := 1 + l ^ n * (K0 - 1)

theorem orbit_pos_sum (g σ c : ℝ) (s x0 : H → ℝ) (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h)
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) (n : ℕ) :
    (∀ h, 0 < orbit g σ c s x0 n h) ∧ ∑ h, orbit g σ c s x0 n h = 1 := by
  induction n with
  | zero => exact ⟨hx0, hx01⟩
  | succ n ih =>
    have hne : Nonempty H := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      simp at hx01
    refine ⟨fun h => T_pos g σ c s _ hg hσ hσ1 hc0 (fun k => (hs k).le)
      (fun k => (ih.1 k).le) h, ?_⟩
    exact T_sum g σ c s _ hg (B_pos s _ hs ih.1).ne' hc

theorem orbit_ratio [Nonempty H] (g σ c K0 : ℝ) (s x0 y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h)
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1)
    (hfix : ∀ h, T g σ c s y h = y h) (hK0 : 1 ≤ K0)
    (hr0 : ∀ h k, x0 h / y h ≤ K0 * (x0 k / y k)) (n : ℕ) :
    ∀ h k, orbit g σ c s x0 n h / y h ≤
      Kseq (lam g σ c) K0 n * (orbit g σ c s x0 n k / y k) := by
  obtain ⟨h0, _⟩ := lam_bounds g σ c s y hg hσ hσ1 hc0 hs hy hy1 hfix
  induction n with
  | zero =>
    intro h k
    have e : Kseq (lam g σ c) K0 0 = K0 := by unfold Kseq; ring
    rw [e]
    exact hr0 h k
  | succ n ih =>
    intro h k
    have hKn : 1 ≤ Kseq (lam g σ c) K0 n := by
      unfold Kseq
      have := mul_nonneg (pow_nonneg h0 n) (sub_nonneg.2 hK0)
      linarith
    have e : Kseq (lam g σ c) K0 (n + 1) = 1 + lam g σ c * (Kseq (lam g σ c) K0 n - 1) := by
      unfold Kseq; ring
    rw [e]
    exact contract_step g σ c _ s _ y hg hσ hσ1 hc0 hs
      (orbit_pos_sum g σ c s x0 hg hσ hσ1 hc0 hc hs hx0 hx01 n).1 hy hy1 hfix hKn ih h k

theorem dist_bound (x y : H → ℝ) (K : ℝ) (hx : ∀ h, 0 < x h) (hy : ∀ h, 0 < y h)
    (hx1 : ∑ h, x h = 1) (hy1 : ∑ h, y h = 1) (hK : 1 ≤ K)
    (hr : ∀ h k, x h / y h ≤ K * (x k / y k)) (h : H) : |x h - y h| ≤ K - 1 := by
  have canc : ∀ k, x k / y k * y k = x k := fun k => div_mul_cancel₀ _ (hy k).ne'
  have up : x h ≤ K * y h := by
    have hs : ∑ k, x h / y h * y k ≤ ∑ k, K * (x k / y k) * y k :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hr h k) (hy k).le
    have e1 : ∑ k, x h / y h * y k = x h / y h := by rw [← Finset.mul_sum, hy1, mul_one]
    have e2 : ∑ k, K * (x k / y k) * y k = K := by
      calc ∑ k, K * (x k / y k) * y k = ∑ k, K * x k :=
            Finset.sum_congr rfl fun k _ => by rw [mul_assoc, canc k]
        _ = K := by rw [← Finset.mul_sum, hx1, mul_one]
    rw [e1, e2, div_le_iff₀ (hy h)] at hs
    exact hs
  have low : y h ≤ K * x h := by
    have hs : ∑ k, x k / y k * y k ≤ ∑ k, K * (x h / y h) * y k :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hr k h) (hy k).le
    rw [Finset.sum_congr rfl fun k _ => canc k, hx1, ← Finset.mul_sum, hy1, mul_one,
      ← mul_div_assoc, le_div_iff₀ (hy h), one_mul] at hs
    exact hs
  have hxh := le_one_of_sum x hx hx1 h
  have hyh := le_one_of_sum y hy hy1 h
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hxh (sub_nonneg.2 hK)]
  · nlinarith [mul_le_mul_of_nonneg_left hyh (sub_nonneg.2 hK)]

/-- **Geometric convergence to the long-run distribution.** -/
theorem converges [Nonempty H] (g σ c K0 : ℝ) (s x0 y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h)
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1)
    (hfix : ∀ h, T g σ c s y h = y h) (hK0 : 1 ≤ K0)
    (hr0 : ∀ h k, x0 h / y h ≤ K0 * (x0 k / y k)) (n : ℕ) (h : H) :
    |orbit g σ c s x0 n h - y h| ≤ lam g σ c ^ n * (K0 - 1) := by
  obtain ⟨h0, _⟩ := lam_bounds g σ c s y hg hσ hσ1 hc0 hs hy hy1 hfix
  have hps := orbit_pos_sum g σ c s x0 hg hσ hσ1 hc0 hc hs hx0 hx01 n
  have hKn : 1 ≤ Kseq (lam g σ c) K0 n := by
    unfold Kseq
    have := mul_nonneg (pow_nonneg h0 n) (sub_nonneg.2 hK0)
    linarith
  have := dist_bound _ y _ hps.1 hy hps.2 hy1 hKn
    (orbit_ratio g σ c K0 s x0 y hg hσ hσ1 hc0 hc hs hx0 hx01 hy hy1 hfix hK0 hr0 n) h
  unfold Kseq at this
  linarith

/-- Any positive starting distribution has a finite initial spread `K0`. -/
theorem exists_K0 [Nonempty H] (x0 y : H → ℝ) (hx0 : ∀ h, 0 < x0 h) (hy : ∀ h, 0 < y h) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧ ∀ h k, x0 h / y h ≤ K0 * (x0 k / y k) := by
  set r : H → ℝ := fun j => x0 j / y j with hr
  have hrpos : ∀ j, 0 < r j := fun j => div_pos (hx0 j) (hy j)
  set m := Finset.univ.inf' Finset.univ_nonempty r with hm
  set M := ∑ j, r j with hM
  have hmpos : 0 < m := (Finset.lt_inf'_iff _).2 fun j _ => hrpos j
  have hmle : ∀ j, m ≤ r j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hleM : ∀ j, r j ≤ M := fun j =>
    Finset.single_le_sum (fun i _ => (hrpos i).le) (Finset.mem_univ j)
  obtain ⟨j0⟩ := ‹Nonempty H›
  refine ⟨M / m, (one_le_div hmpos).2 ((hmle j0).trans (hleM j0)), fun h k => ?_⟩
  have e : M / m * m = M := div_mul_cancel₀ _ hmpos.ne'
  have hMm : 0 ≤ M / m := div_nonneg ((hrpos j0).le.trans (hleM j0)) hmpos.le
  calc x0 h / y h = r h := rfl
    _ ≤ M := hleM h
    _ = M / m * m := e.symm
    _ ≤ M / m * r k := mul_le_mul_of_nonneg_left (hmle k) hMm

theorem converges_tendsto [Nonempty H] (g σ c : ℝ) (s x0 y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h)
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1)
    (hfix : ∀ h, T g σ c s y h = y h) (h : H) :
    Tendsto (fun n => orbit g σ c s x0 n h) atTop (𝓝 (y h)) := by
  obtain ⟨K0, hK0, hr0⟩ := exists_K0 x0 y hx0 hy
  obtain ⟨h0, h1⟩ := lam_bounds g σ c s y hg hσ hσ1 hc0 hs hy hy1 hfix
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (K0 - 1)
  rw [zero_mul] at hlim
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [Real.norm_eq_abs]
  exact converges g σ c K0 s x0 y hg hσ hσ1 hc0 hc hs hx0 hx01 hy hy1 hfix hK0 hr0 n h

theorem orbit_fixed (g σ c : ℝ) (s z : H → ℝ) (hfix : ∀ h, T g σ c s z h = z h) (n : ℕ) :
    orbit g σ c s z n = z := by
  induction n with
  | zero => rfl
  | succ n ih => show T g σ c s (orbit g σ c s z n) = z; rw [ih]; exact funext hfix

/-- Uniqueness of the positive long-run distribution follows from convergence. -/
theorem fixed_unique [Nonempty H] (g σ c : ℝ) (s y z : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h)
    (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1) (hfix : ∀ h, T g σ c s y h = y h)
    (hz : ∀ h, 0 < z h) (hz1 : ∑ h, z h = 1) (hfixz : ∀ h, T g σ c s z h = z h) : z = y := by
  funext h
  have t := converges_tendsto g σ c s z y hg hσ hσ1 hc0 hc hs hz hz1 hy hy1 hfix h
  simp only [orbit_fixed g σ c s z hfixz] at t
  exact tendsto_nhds_unique tendsto_const_nhds t

/-! ## Equilibrium paths with forward-looking saving

As in stage 357: `fut b r t` is the bounded solution of the Euler-and-budget recursion, the
saving rate is `fut / (1 + fut)`, with `r t = R (t + 1) ^ ((1 − γ) / γ)` and the gross return on
saved ownership `R (t + 1) = 1 / B`. -/

def term (b : ℝ) (r : ℕ → ℝ) (t j : ℕ) : ℝ := b ^ (j + 1) * ∏ i ∈ Finset.range (j + 1), r (t + i)

def fut (b : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, term b r t j

def fsave (b : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ := fut b r t / (1 + fut b r t)

def rr (γ : ℝ) (R : ℕ → ℝ) (t : ℕ) : ℝ := R (t + 1) ^ ((1 - γ) / γ)

def sav (γ : ℝ) (b : H → ℝ) (R : ℕ → ℝ) (t : ℕ) (h : H) : ℝ := fsave (b h) (rr γ R) t

/-- A perfect-foresight equilibrium path: each date's saving rates come from the whole future
return path, the distribution follows the issuance step, and the return is `1 / B`. -/
def IsEquilibrium (g σ c γ : ℝ) (b x0 : H → ℝ) (x : ℕ → H → ℝ) (R : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t, x (t + 1) = T g σ c (sav γ b R t) (x t) ∧
    R (t + 1) = 1 / B (sav γ b R t) (x t)

theorem fut_const (b ρ : ℝ) (h0 : 0 ≤ b * ρ) (h1 : b * ρ < 1) (t : ℕ) :
    fut b (fun _ => ρ) t = b * ρ / (1 - b * ρ) := by
  have e : ∀ j : ℕ, term b (fun _ => ρ) t j = (b * ρ) * (b * ρ) ^ j := fun j => by
    simp only [term, Finset.prod_const, Finset.card_range]
    ring
  simp only [fut, e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

theorem fsave_const (b ρ : ℝ) (h0 : 0 ≤ b * ρ) (h1 : b * ρ < 1) (t : ℕ) :
    fsave b (fun _ => ρ) t = b * ρ := by
  unfold fsave
  rw [fut_const b ρ h0 h1 t]
  have hne : 1 - b * ρ ≠ 0 := by linarith
  have hd : 0 < 1 + b * ρ / (1 - b * ρ) := by
    have : 0 ≤ b * ρ / (1 - b * ρ) := div_nonneg h0 (by linarith)
    linarith
  rw [div_eq_iff hd.ne']
  have hq : b * ρ / (1 - b * ρ) * (1 - b * ρ) = b * ρ := div_mul_cancel₀ _ hne
  linear_combination hq

theorem rr_log (R : ℕ → ℝ) : rr 1 R = fun _ => 1 := by
  funext t
  simp [rr]

omit [Fintype H] in
theorem sav_log (b : H → ℝ) (hb0 : ∀ h, 0 < b h) (hb1 : ∀ h, b h < 1) (R : ℕ → ℝ) (t : ℕ) :
    sav 1 b R t = b := by
  funext h
  unfold sav
  rw [rr_log, fsave_const (b h) 1 (by linarith [hb0 h]) (by linarith [hb1 h]), mul_one]

/-- The log-utility equilibrium return path. -/
def Rlog (g σ c : ℝ) (b x0 : H → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => 1 / B b (orbit g σ c b x0 t)

/-- **Log utility: a perfect-foresight equilibrium path exists** from every starting distribution. -/
theorem log_equilibrium (g σ c : ℝ) (b x0 : H → ℝ) (hb0 : ∀ h, 0 < b h) (hb1 : ∀ h, b h < 1) :
    IsEquilibrium g σ c 1 b x0 (orbit g σ c b x0) (Rlog g σ c b x0) := by
  refine ⟨rfl, fun t => ?_⟩
  rw [sav_log b hb0 hb1]
  exact ⟨rfl, rfl⟩

/-- **…and it is unique.** -/
theorem log_equilibrium_unique (g σ c : ℝ) (b x0 : H → ℝ) (hb0 : ∀ h, 0 < b h)
    (hb1 : ∀ h, b h < 1) (x : ℕ → H → ℝ) (R : ℕ → ℝ)
    (hE : IsEquilibrium g σ c 1 b x0 x R) (n : ℕ) : x n = orbit g σ c b x0 n := by
  induction n with
  | zero => exact hE.1
  | succ n ih =>
    rw [(hE.2 n).1, sav_log b hb0 hb1, ih]
    rfl

/-- **…and every log-utility equilibrium converges to the long-run distribution.** -/
theorem log_equilibrium_converges [Nonempty H] (g σ c : ℝ) (b x0 y : H → ℝ) (hg : 0 < g)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1)
    (hb0 : ∀ h, 0 < b h) (hb1 : ∀ h, b h < 1) (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1)
    (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1) (hfix : ∀ h, T g σ c b y h = y h)
    (x : ℕ → H → ℝ) (R : ℕ → ℝ) (hE : IsEquilibrium g σ c 1 b x0 x R) (h : H) :
    Tendsto (fun n => x n h) atTop (𝓝 (y h)) := by
  have e : (fun n => x n h) = fun n => orbit g σ c b x0 n h :=
    funext fun n => by rw [log_equilibrium_unique g σ c b x0 hb0 hb1 x R hE n]
  rw [e]
  exact converges_tendsto g σ c b x0 y hg hσ hσ1 hc0 hc hb0 hx0 hx01 hy hy1 hfix h

theorem T_scale (g σ c ρ : ℝ) (s x : H → ℝ) (hρ : ρ ≠ 0) :
    T g σ c (fun h => ρ * s h) x = T g σ c s x := by
  funext h
  simp only [T, B]
  have e : ∑ k, ρ * s k * x k = ρ * ∑ k, s k * x k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, show ρ * s h * x h = ρ * (s h * x h) by ring, mul_div_mul_left _ _ hρ]

/-- **CRRA steady-state equilibrium** for any curvature `γ ≠ 0`: the long-run distribution `y` of
the patience factors `b`, with the constant return `R = B b y ^ (−γ)`. -/
theorem steady_equilibrium [Nonempty H] (g σ c γ : ℝ) (b y : H → ℝ) (hγ : γ ≠ 0)
    (hb0 : ∀ h, 0 < b h) (hy : ∀ h, 0 < y h) (hfix : ∀ h, T g σ c b y h = y h)
    (hb1 : ∀ h, b h * B b y ^ (γ - 1) < 1) :
    IsEquilibrium g σ c γ b y (fun _ => y) (fun _ => B b y ^ (-γ)) := by
  have hBb := B_pos b y hb0 hy
  have hρ : 0 < B b y ^ (γ - 1) := Real.rpow_pos_of_pos hBb _
  have hrr : rr γ (fun _ => B b y ^ (-γ)) = fun _ => B b y ^ (γ - 1) := by
    funext t
    unfold rr
    rw [← Real.rpow_mul hBb.le]
    congr 1
    field_simp
    ring
  have hsav : sav γ b (fun _ => B b y ^ (-γ)) = fun _ h => B b y ^ (γ - 1) * b h := by
    funext t h
    unfold sav
    rw [hrr, fsave_const (b h) _ (mul_nonneg (hb0 h).le hρ.le) (hb1 h)]
    ring
  refine ⟨rfl, fun t => ⟨?_, ?_⟩⟩
  · rw [hsav]
    show y = T g σ c (fun h => B b y ^ (γ - 1) * b h) y
    rw [T_scale g σ c _ b y hρ.ne']
    exact (funext hfix).symm
  · rw [hsav]
    show B b y ^ (-γ) = 1 / B (fun h => B b y ^ (γ - 1) * b h) y
    have e : B (fun h => B b y ^ (γ - 1) * b h) y = B b y ^ (γ - 1) * B b y := by
      unfold B
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, Real.rpow_sub_one hBb.ne', div_mul_cancel₀ _ hBb.ne', Real.rpow_neg hBb.le, one_div]

/-- The steady-state condition holds automatically when `γ ≥ 1`. -/
theorem steady_condition (b y : H → ℝ) (γ : ℝ) (hγ : 1 ≤ γ) (hb0 : ∀ h, 0 < b h)
    (hb1 : ∀ h, b h < 1) (hy : ∀ h, 0 < y h) (hy1 : ∑ h, y h = 1) (h : H) :
    b h * B b y ^ (γ - 1) < 1 := by
  have hB0 : 0 ≤ B b y := Finset.sum_nonneg fun k _ => mul_nonneg (hb0 k).le (hy k).le
  have hB1 : B b y ≤ 1 := by
    unfold B
    calc ∑ k, b k * y k ≤ ∑ k, y k :=
          Finset.sum_le_sum fun k _ => by nlinarith [hb1 k, hy k]
      _ = 1 := hy1
  have := Real.rpow_le_one hB0 hB1 (by linarith : 0 ≤ γ - 1)
  have hpow : 0 ≤ B b y ^ (γ - 1) := Real.rpow_nonneg hB0 _
  nlinarith [hb0 h, hb1 h]

/-! ## Wealth-dependent patience -/

/-- The step when each household's saving rate depends on its own share through `φ`. -/
def Tp (g σ c : ℝ) (φ : ℝ → ℝ) (x : H → ℝ) : H → ℝ := T g σ c (fun h => φ (x h)) x

def orbitp (g σ c : ℝ) (φ : ℝ → ℝ) (x0 : H → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | n + 1 => Tp g σ c φ (orbitp g σ c φ x0 n)

/-- **Patience rising with wealth never reverses the ranking.** -/
theorem rank_preserved (g σ c : ℝ) (φ : ℝ → ℝ) (x : H → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hφ : Monotone φ) (hφ0 : ∀ z, 0 ≤ φ z) (hx : ∀ h, 0 ≤ x h) (h k : H) (hhk : x h ≤ x k) :
    Tp g σ c φ x h ≤ Tp g σ c φ x k := by
  simp only [Tp, T]
  have hB : 0 ≤ B (fun h => φ (x h)) x :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hφ0 _) (hx j)
  have h1 : φ (x h) * x h ≤ φ (x k) * x k := mul_le_mul (hφ hhk) hhk (hx h) (hφ0 _)
  have h2 := div_le_div_of_nonneg_right h1 hB
  have h3 := mul_le_mul_of_nonneg_left h2 (amp_pos g σ hg hσ1).le
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem const_fixed (g σ c b : ℝ) (hg : 0 < g) (hb : 0 < b)
    (hc : (Fintype.card H : ℝ) * c = 1) (h : H) :
    T g σ c (fun _ => b) (fun _ => c) h = c := by
  have hB : B (fun _ => b) (fun _ : H => c) = b := by
    unfold B
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination b * hc
  simp only [T]
  rw [hB, mul_div_cancel_left₀ _ hb.ne', div_eq_iff (by linarith)]
  unfold amp
  ring

/-- **A threshold in patience is overcome when the equal part alone lifts everyone above it.**
Patience is `hi` at or above `θ`; if `(1 + g) θ ≤ g σ c`, the economy converges to equal shares
from every positive starting distribution. -/
theorem threshold_equalizes [Nonempty H] (g σ c θ hi : ℝ) (φ : ℝ → ℝ) (x0 : H → ℝ)
    (hg : 0 < g) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc0 : 0 < c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hhi : 0 < hi) (hφ0 : ∀ z, 0 < φ z)
    (hφhi : ∀ z, θ ≤ z → φ z = hi) (hθ : (1 + g) * θ ≤ g * σ * c)
    (hx0 : ∀ h, 0 < x0 h) (h : H) :
    Tendsto (fun n => orbitp g σ c φ x0 n h) atTop (𝓝 c) := by
  have hfloor : θ ≤ g * σ * c / (1 + g) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hpos : ∀ n k, 0 < orbitp g σ c φ x0 n k := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih =>
      intro k
      exact T_pos g σ c _ _ hg hσ hσ1 hc0 (fun j => (hφ0 _).le) (fun j => (ih j).le) k
  have habove : ∀ n k, θ ≤ orbitp g σ c φ x0 (n + 1) k := fun n k =>
    hfloor.trans (T_floor g σ c _ _ hg hσ1 (fun j => (hφ0 _).le) (fun j => (hpos n j).le) k)
  have hsum1 : ∑ k, orbitp g σ c φ x0 1 k = 1 :=
    T_sum g σ c _ _ hg (B_pos (fun j => φ (x0 j)) x0 (fun j => hφ0 _) hx0).ne' hc
  have hshift : ∀ n, orbitp g σ c φ x0 (n + 1) =
      orbit g σ c (fun _ => hi) (orbitp g σ c φ x0 1) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show T g σ c (fun j => φ (orbitp g σ c φ x0 (n + 1) j)) (orbitp g σ c φ x0 (n + 1)) =
        T g σ c (fun _ => hi) (orbit g σ c (fun _ => hi) (orbitp g σ c φ x0 1) n)
      have e : (fun j => φ (orbitp g σ c φ x0 (n + 1) j)) = fun _ => hi :=
        funext fun j => hφhi _ (habove n j)
      rw [e, ih]
  have hy1 : ∑ _k : H, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have t := converges_tendsto g σ c (fun _ => hi) (orbitp g σ c φ x0 1) (fun _ => c) hg hσ hσ1
    hc0 hc (fun _ => hhi) (hpos 1) hsum1 (fun _ => hc0) hy1
    (fun k => const_fixed g σ c hi hg hhi hc k) h
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : (fun n => orbitp g σ c φ x0 (n + 1) h) =
      fun n => orbit g σ c (fun _ => hi) (orbitp g σ c φ x0 1) n h :=
    funext fun n => by rw [hshift n]
  rw [e]
  exact t

/-- The two-household example: patience `1/2` at or above the threshold `1/2`, `2/5` below it;
`g = 1`, `σ = 1/5`, `c = 1/2`. -/
def φex (z : ℝ) : ℝ := if 1 / 2 ≤ z then 1 / 2 else 2 / 5

/-- **The equal distribution is a rest point** of the example. -/
theorem ex_equal_rest (h : Fin 2) :
    Tp 1 (1 / 5) (1 / 2) φex (fun _ => 1 / 2) h = 1 / 2 := by
  norm_num [Tp, T, B, amp, φex, Fin.sum_univ_two]

/-- **…and so is the unequal distribution `(1/5, 4/5)`**: identical households, with patience
rising in wealth, can stay unequal forever when the equal part is small. -/
theorem ex_unequal_rest (h : Fin 2) :
    Tp 1 (1 / 5) (1 / 2) φex ![1 / 5, 4 / 5] h = ![1 / 5, 4 / 5] h := by
  fin_cases h <;> norm_num [Tp, T, B, amp, φex, Fin.sum_univ_two]

end OwnershipDynamics

end

#print axioms OwnershipDynamics.pair_bound
#print axioms OwnershipDynamics.contract_step
#print axioms OwnershipDynamics.orbit_ratio
#print axioms OwnershipDynamics.dist_bound
#print axioms OwnershipDynamics.converges
#print axioms OwnershipDynamics.exists_K0
#print axioms OwnershipDynamics.converges_tendsto
#print axioms OwnershipDynamics.fixed_unique
#print axioms OwnershipDynamics.fut_const
#print axioms OwnershipDynamics.fsave_const
#print axioms OwnershipDynamics.log_equilibrium
#print axioms OwnershipDynamics.log_equilibrium_unique
#print axioms OwnershipDynamics.log_equilibrium_converges
#print axioms OwnershipDynamics.steady_equilibrium
#print axioms OwnershipDynamics.steady_condition
#print axioms OwnershipDynamics.rank_preserved
#print axioms OwnershipDynamics.threshold_equalizes
#print axioms OwnershipDynamics.ex_equal_rest
#print axioms OwnershipDynamics.ex_unequal_rest
