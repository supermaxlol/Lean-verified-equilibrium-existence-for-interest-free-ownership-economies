import Mathlib

/-!
# Stage 356: the issuance equilibrium with different patience and unequal access

This generalises the stage-263 issuance equilibrium. Stage 263 assumed that every household has
the same patience, the same saving rate and the same access to new units. Here household `h`
saves the fraction `s t h` of its wealth in period `t` (any rule; for log utility `s = β h`, for
CRRA at gross return `R` the stationary rate `(β h R ^ (1 − γ)) ^ (1 / γ)`), and only households in
the access set `A` take part in the pro rata part of issuance. A fraction `σ` of new units is
issued equally (`c` each) to every household.

Equilibrium in one period (wealth `x h (Q + D)`, units value `Q`, dividends `D`):
* `aggregate_demand`, `clearing_unique`, `clearing_exists`: the units market clears exactly at
  `Q = B D / (1 − B)`, where `B = ∑ s h x h` is the wealth-weighted saving rate.
* `equilibrium_return`: the gross return on ownership is `1 / B`, set by aggregate patience.
* `units_share`: in equilibrium household `h` ends up with the unit share `s h x h / B`.
* `consumption_share_iff`: a household's consumption share equals its wealth share exactly when
  its saving rate equals the aggregate one, so the stage-250 link breaks under heterogeneity.
* `B_ge`, `B_le`: `B` lies between the lowest and highest saving rates.

Issuance with access:
* `step_sum`, `path_pos_sum`: shares stay positive and sum to one along the equilibrium path.
* `reduces_to_common`: with a common saving rate and full access, the step is exactly stage 263's.
* `excluded_step`: a household outside `A` receives only the equal part.
* `floor_every_step`: every household, with or without access, holds at least `g σ c / (1 + g)`.

Patience (full access, `σ = 0`):
* `pro_rata_closed`: shares are `P n h x0 h / ∑ P n k x0 k`, `P n h = ∏ t < n, s t h`.
* `ratio_bound`, `ratio_vanishes`, `most_patient_takes_all`: if every other household's saving
  rate stays below `ρ k < 1` times household `h`'s, then `h`'s share tends to one.
* `log_takes_all`: for log utility (`s = β`), the most patient household takes everything.
* `crra_ratio`, `crra_takes_all`: for CRRA with a common `γ`, saving-rate ratios are
  `(β k / β h) ^ (1 / γ)` at every return, so the most patient takes everything along any
  positive return path.

Access:
* `excluded_dilution`: with `σ = 0`, an excluded household's share is at most
  `(κ / (1 + g)) ^ n x0 h`, where its saving rate is at most `κ` times the lowest rate.
* `excluded_floor`, `excluded_floor_eventually`: with `σ > 0`, an excluded household's share is at
  least a sequence tending to `g σ c / (1 + g − lo / hi)`; for a common rate this is `σ c`.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace HeterogeneousIssuance

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Wealth-weighted aggregate saving rate. -/
def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

omit [DecidableEq H] in
theorem aggregate_demand (s x : H → ℝ) (V : ℝ) : ∑ h, s h * (x h * V) = B s x * V := by
  unfold B
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun h _ => by ring

theorem clearing_unique (b Q D : ℝ) (hb1 : b < 1) (h : b * (Q + D) = Q) :
    Q = b * D / (1 - b) := by
  have h1 : (0:ℝ) < 1 - b := by linarith
  rw [eq_div_iff h1.ne']
  linarith

theorem clearing_exists (b D : ℝ) (hb1 : b < 1) :
    b * (b * D / (1 - b) + D) = b * D / (1 - b) := by
  have h1 : (1:ℝ) - b ≠ 0 := by linarith
  field_simp
  ring

theorem equilibrium_return (b Q D : ℝ) (hb : 0 < b) (hQ : 0 < Q) (h : b * (Q + D) = Q) :
    (Q + D) / Q = 1 / b := by
  rw [div_eq_div_iff hQ.ne' hb.ne']
  linarith

/-- Share of units held after trade. -/
def post (s x : H → ℝ) (h : H) : ℝ := s h * x h / B s x

omit [DecidableEq H] in
theorem units_share (s x : H → ℝ) (Q D : ℝ) (hQ : Q ≠ 0) (hB : B s x ≠ 0)
    (h : B s x * (Q + D) = Q) (k : H) : s k * (x k * (Q + D)) / Q = post s x k := by
  unfold post
  rw [div_eq_div_iff hQ hB]
  linear_combination (s k * x k) * h

omit [DecidableEq H] in
theorem consumption_share_iff (s x : H → ℝ) (k : H) (hx : x k ≠ 0) (hB : 1 - B s x ≠ 0) :
    (1 - s k) * x k / (1 - B s x) = x k ↔ s k = B s x := by
  rw [div_eq_iff hB]
  constructor
  · intro h
    have e : (B s x - s k) * x k = 0 := by linear_combination h
    rcases mul_eq_zero.1 e with h1 | h1
    · linarith
    · exact absurd h1 hx
  · intro h
    rw [h]
    ring

omit [DecidableEq H] in
theorem B_ge (s x : H → ℝ) (lo : ℝ) (hlo : ∀ h, lo ≤ s h) (hx : ∀ h, 0 ≤ x h)
    (hs : ∑ h, x h = 1) : lo ≤ B s x := by
  unfold B
  calc lo = ∑ h, lo * x h := by rw [← Finset.mul_sum, hs, mul_one]
    _ ≤ ∑ h, s h * x h :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hlo h) (hx h)

omit [DecidableEq H] in
theorem B_le (s x : H → ℝ) (hi : ℝ) (hhi : ∀ h, s h ≤ hi) (hx : ∀ h, 0 ≤ x h)
    (hs : ∑ h, x h = 1) : B s x ≤ hi := by
  unfold B
  calc ∑ h, s h * x h ≤ ∑ h, hi * x h :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right (hhi h) (hx h)
    _ = hi := by rw [← Finset.mul_sum, hs, mul_one]

omit [DecidableEq H] in
theorem post_sum (s x : H → ℝ) (hB : B s x ≠ 0) : ∑ h, post s x h = 1 := by
  unfold post
  rw [← Finset.sum_div]
  exact div_self hB

omit [DecidableEq H] in
theorem post_nonneg (s x : H → ℝ) (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h) (h : H) :
    0 ≤ post s x h :=
  div_nonneg (mul_nonneg (hs h) (hx h))
    (Finset.sum_nonneg fun k _ => mul_nonneg (hs k) (hx k))

/-! ## Issuance with an access set -/

def mass (A : Finset H) (s x : H → ℝ) : ℝ := ∑ k ∈ A, post s x k

def prorata (A : Finset H) (s x : H → ℝ) (h : H) : ℝ :=
  if h ∈ A then post s x h / mass A s x else 0

def step (g σ c : ℝ) (A : Finset H) (s x : H → ℝ) (h : H) : ℝ :=
  (post s x h + g * (σ * c + (1 - σ) * prorata A s x h)) / (1 + g)

def path (g σ c : ℝ) (A : Finset H) (s : ℕ → H → ℝ) (x0 : H → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | n + 1 => step g σ c A (s n) (path g σ c A s x0 n)

theorem prorata_sum (A : Finset H) (s x : H → ℝ) (hm : mass A s x ≠ 0) :
    ∑ h, prorata A s x h = 1 := by
  unfold prorata
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
  exact div_self hm

theorem prorata_nonneg (A : Finset H) (s x : H → ℝ) (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h)
    (h : H) : 0 ≤ prorata A s x h := by
  unfold prorata
  split_ifs
  · exact div_nonneg (post_nonneg s x hs hx h)
      (Finset.sum_nonneg fun k _ => post_nonneg s x hs hx k)
  · exact le_rfl

theorem step_sum (g σ c : ℝ) (A : Finset H) (s x : H → ℝ) (hg : 1 + g ≠ 0)
    (hc : (Fintype.card H : ℝ) * c = 1) (hB : B s x ≠ 0) (hm : mass A s x ≠ 0) :
    ∑ h, step g σ c A s x h = 1 := by
  unfold step
  rw [← Finset.sum_div, div_eq_one_iff_eq hg]
  have e : ∀ h, post s x h + g * (σ * c + (1 - σ) * prorata A s x h) =
      post s x h + g * σ * c + g * (1 - σ) * prorata A s x h := fun h => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, post_sum s x hB, prorata_sum A s x hm]
  linear_combination g * σ * hc

theorem full_access_prorata (s x : H → ℝ) (hB : B s x ≠ 0) (h : H) :
    prorata Finset.univ s x h = post s x h := by
  simp only [prorata, Finset.mem_univ, ↓reduceIte]
  unfold mass
  rw [post_sum s x hB, div_one]

omit [DecidableEq H] in
theorem common_post (b : ℝ) (x : H → ℝ) (hb : b ≠ 0) (hs : ∑ h, x h = 1) (h : H) :
    post (fun _ => b) x h = x h := by
  show b * x h / ∑ k, b * x k = x h
  rw [← Finset.mul_sum, hs, mul_one, mul_div_cancel_left₀ _ hb]

/-- Stage 263's issuance rule. -/
def next263 (g σ c y : ℝ) : ℝ := (y + g * (σ * c + (1 - σ) * y)) / (1 + g)

/-- **Consistency with stage 263.** -/
theorem reduces_to_common (g σ c b : ℝ) (x : H → ℝ) (hb : b ≠ 0) (hs : ∑ h, x h = 1) (h : H) :
    step g σ c Finset.univ (fun _ => b) x h = next263 g σ c (x h) := by
  have hB : B (fun _ => b) x ≠ 0 := by
    show ∑ k, b * x k ≠ 0
    rw [← Finset.mul_sum, hs, mul_one]
    exact hb
  unfold step next263
  rw [full_access_prorata _ _ hB, common_post b x hb hs]

theorem excluded_step (g σ c : ℝ) (A : Finset H) (s x : H → ℝ) (h : H) (hA : h ∉ A) :
    step g σ c A s x h = (post s x h + g * σ * c) / (1 + g) := by
  unfold step prorata
  simp only [hA, ↓reduceIte]
  ring

/-- **Every household keeps a floor**, whatever its patience or access. -/
theorem floor_every_step (g σ c : ℝ) (A : Finset H) (s x : H → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h) (h : H) :
    g * σ * c / (1 + g) ≤ step g σ c A s x h := by
  unfold step
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith [post_nonneg s x hs hx h,
    mul_nonneg hg.le (mul_nonneg (sub_nonneg.2 hσ1) (prorata_nonneg A s x hs hx h))]

omit [DecidableEq H] in
theorem B_pos [Nonempty H] (s x : H → ℝ) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) :
    0 < B s x :=
  Finset.sum_pos (fun k _ => mul_pos (hs k) (hx k)) Finset.univ_nonempty

/-- **The equilibrium path is well defined**: shares stay positive and sum to one. -/
theorem path_pos_sum (g σ c : ℝ) (A : Finset H) (hA : A.Nonempty) (s : ℕ → H → ℝ)
    (x0 : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h)
    (hsum : ∑ h, x0 h = 1) (n : ℕ) :
    (∀ h, 0 < path g σ c A s x0 n h) ∧ ∑ h, path g σ c A s x0 n h = 1 := by
  have : Nonempty H := ⟨hA.choose⟩
  induction n with
  | zero => exact ⟨hx0, hsum⟩
  | succ n ih =>
    obtain ⟨hp, _⟩ := ih
    have hB := B_pos (s n) _ (hs n) hp
    have hpost : ∀ h, 0 < post (s n) (path g σ c A s x0 n) h :=
      fun h => div_pos (mul_pos (hs n h) (hp h)) hB
    have hm : 0 < mass A (s n) (path g σ c A s x0 n) := Finset.sum_pos (fun k _ => hpost k) hA
    refine ⟨fun h => ?_, step_sum g σ c A (s n) _ (by linarith) hc hB.ne' hm.ne'⟩
    show 0 < step g σ c A (s n) (path g σ c A s x0 n) h
    unfold step
    apply div_pos _ (by linarith)
    have hq := prorata_nonneg A (s n) (path g σ c A s x0 n) (fun k => (hs n k).le)
      (fun k => (hp k).le) h
    nlinarith [hpost h, mul_nonneg hg.le (mul_nonneg hσ0 hc0),
      mul_nonneg hg.le (mul_nonneg (sub_nonneg.2 hσ1) hq)]

/-! ## Patience under pro rata issuance -/

def P (s : ℕ → H → ℝ) (n : ℕ) (h : H) : ℝ := ∏ t ∈ Finset.range n, s t h

def S (s : ℕ → H → ℝ) (x0 : H → ℝ) (n : ℕ) : ℝ := ∑ k, P s n k * x0 k

omit [Fintype H] [DecidableEq H] in
theorem P_pos (s : ℕ → H → ℝ) (hs : ∀ t h, 0 < s t h) (n : ℕ) (h : H) : 0 < P s n h :=
  Finset.prod_pos fun t _ => hs t h

omit [DecidableEq H] in
theorem S_pos [Nonempty H] (s : ℕ → H → ℝ) (x0 : H → ℝ) (hs : ∀ t h, 0 < s t h)
    (hx0 : ∀ h, 0 < x0 h) (n : ℕ) : 0 < S s x0 n :=
  Finset.sum_pos (fun k _ => mul_pos (P_pos s hs n k) (hx0 k)) Finset.univ_nonempty

theorem step_pro_rata_full (g c : ℝ) (s x : H → ℝ) (hg : 1 + g ≠ 0) (hB : B s x ≠ 0) (h : H) :
    step g 0 c Finset.univ s x h = post s x h := by
  unfold step
  rw [full_access_prorata s x hB, div_eq_iff hg]
  ring

/-- **Closed form under pro rata issuance**, with saving rates that may vary over time. -/
theorem pro_rata_closed [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (n : ℕ) :
    path g 0 c Finset.univ s x0 n = fun h => P s n h * x0 h / S s x0 n := by
  induction n with
  | zero =>
    funext h
    simp [path, P, S, hsum]
  | succ n ih =>
    funext h
    have hS := (S_pos s x0 hs hx0 n).ne'
    have hS1 := (S_pos s x0 hs hx0 (n + 1)).ne'
    have eB : B (s n) (fun k => P s n k * x0 k / S s x0 n) = S s x0 (n + 1) / S s x0 n := by
      show ∑ k, s n k * (P s n k * x0 k / S s x0 n) = (∑ k, P s (n + 1) k * x0 k) / S s x0 n
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by
        unfold P
        rw [Finset.prod_range_succ]
        ring
    show step g 0 c Finset.univ (s n) (path g 0 c Finset.univ s x0 n) h = _
    rw [ih, step_pro_rata_full g c _ _ hg (by rw [eB]; exact div_ne_zero hS1 hS)]
    unfold post
    rw [eB]
    have hP : P s (n + 1) h = P s n h * s n h := by
      unfold P
      rw [Finset.prod_range_succ]
    rw [hP]; beta_reduce; rw [div_div_eq_mul_div, mul_div_assoc', div_mul_cancel₀ _ hS]
    ring

omit [Fintype H] [DecidableEq H] in
theorem P_ratio (s : ℕ → H → ℝ) (k h : H) (ρ : ℝ) (hρ : 0 ≤ ρ) (hs : ∀ t h, 0 < s t h)
    (hr : ∀ t, s t k ≤ ρ * s t h) (n : ℕ) : P s n k ≤ ρ ^ n * P s n h := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    unfold P at *
    rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
    calc (∏ t ∈ Finset.range n, s t k) * s n k
        ≤ (ρ ^ n * ∏ t ∈ Finset.range n, s t h) * (ρ * s n h) :=
          mul_le_mul ih (hr n) (hs n k).le
            (mul_nonneg (pow_nonneg hρ n) (Finset.prod_pos fun t _ => hs t h).le)
      _ = ρ ^ n * ρ * ((∏ t ∈ Finset.range n, s t h) * s n h) := by ring

theorem path_full_nonneg [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (n : ℕ) (k : H) :
    0 ≤ path g 0 c Finset.univ s x0 n k := by
  rw [pro_rata_closed g c s x0 hg hs hx0 hsum n]
  exact div_nonneg (mul_pos (P_pos s hs n k) (hx0 k)).le (S_pos s x0 hs hx0 n).le

theorem path_full_sum [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (n : ℕ) :
    ∑ k, path g 0 c Finset.univ s x0 n k = 1 := by
  rw [pro_rata_closed g c s x0 hg hs hx0 hsum n, ← Finset.sum_div]
  exact div_self (S_pos s x0 hs hx0 n).ne'

/-- **A household that saves less is diluted geometrically.** -/
theorem ratio_bound [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (k h : H) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hr : ∀ t, s t k ≤ ρ * s t h) (n : ℕ) :
    path g 0 c Finset.univ s x0 n k ≤ ρ ^ n * (x0 k / x0 h) := by
  rw [pro_rata_closed g c s x0 hg hs hx0 hsum n]
  have hS := S_pos s x0 hs hx0 n
  have hle : P s n h * x0 h ≤ S s x0 n :=
    Finset.single_le_sum (f := fun k => P s n k * x0 k)
      (fun k _ => (mul_pos (P_pos s hs n k) (hx0 k)).le) (Finset.mem_univ h)
  have hpk := P_ratio s k h ρ hρ hs hr n
  have hxh := (hx0 h).ne'
  show P s n k * x0 k / S s x0 n ≤ ρ ^ n * (x0 k / x0 h)
  rw [div_le_iff₀ hS]
  calc P s n k * x0 k ≤ ρ ^ n * P s n h * x0 k :=
        mul_le_mul_of_nonneg_right hpk (hx0 k).le
    _ = ρ ^ n * (x0 k / x0 h) * (P s n h * x0 h) := by field_simp
    _ ≤ ρ ^ n * (x0 k / x0 h) * S s x0 n :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg (pow_nonneg hρ n) (div_nonneg (hx0 k).le (hx0 h).le))

theorem ratio_vanishes [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (k h : H) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hr : ∀ t, s t k ≤ ρ * s t h) :
    Tendsto (fun n => path g 0 c Finset.univ s x0 n k) atTop (𝓝 0) := by
  have hup : Tendsto (fun n => ρ ^ n * (x0 k / x0 h)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).mul_const (x0 k / x0 h)
    rwa [zero_mul] at this
  exact squeeze_zero (fun n => path_full_nonneg g c s x0 hg hs hx0 hsum n k)
    (fun n => ratio_bound g c s x0 hg hs hx0 hsum k h ρ hρ hr n) hup

/-- **Pro rata issuance ends in complete concentration** on the household that saves most. -/
theorem most_patient_takes_all [Nonempty H] (g c : ℝ) (s : ℕ → H → ℝ) (x0 : H → ℝ)
    (hg : 1 + g ≠ 0) (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1)
    (h : H) (ρ : H → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (hρ1 : ∀ k, k ≠ h → ρ k < 1)
    (hr : ∀ k, k ≠ h → ∀ t, s t k ≤ ρ k * s t h) :
    Tendsto (fun n => path g 0 c Finset.univ s x0 n h) atTop (𝓝 1) := by
  have hrest : Tendsto (fun n => ∑ k ∈ Finset.univ.erase h, path g 0 c Finset.univ s x0 n k)
      atTop (𝓝 (∑ k ∈ Finset.univ.erase h, (0:ℝ))) :=
    tendsto_finsetSum _ fun k hk =>
      ratio_vanishes g c s x0 hg hs hx0 hsum k h (ρ k) (hρ0 k)
        (hρ1 k (Finset.ne_of_mem_erase hk)) (hr k (Finset.ne_of_mem_erase hk))
  rw [Finset.sum_const_zero] at hrest
  have e : (fun n => path g 0 c Finset.univ s x0 n h) =
      fun n => 1 - ∑ k ∈ Finset.univ.erase h, path g 0 c Finset.univ s x0 n k := by
    funext n
    have := path_full_sum g c s x0 hg hs hx0 hsum n
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)] at this
    linarith
  rw [e]
  have := (tendsto_const_nhds (x := (1:ℝ))).sub hrest
  rwa [sub_zero] at this

/-- **Log utility** (saving rate `β h`): the most patient household takes everything. -/
theorem log_takes_all [Nonempty H] (g c : ℝ) (β x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hβ : ∀ h, 0 < β h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (h : H)
    (htop : ∀ k, k ≠ h → β k < β h) :
    Tendsto (fun n => path g 0 c Finset.univ (fun _ => β) x0 n h) atTop (𝓝 1) :=
  most_patient_takes_all g c (fun _ => β) x0 hg (fun _ => hβ) hx0 hsum h (fun k => β k / β h)
    (fun k => div_nonneg (hβ k).le (hβ h).le) (fun k hk => (div_lt_one (hβ h)).2 (htop k hk))
    (fun k _ _ => (div_mul_cancel₀ (β k) (hβ h).ne').ge)

/-- Stationary CRRA saving rate at gross return `R`. -/
def crraRate (γ b R : ℝ) : ℝ := (b * R ^ (1 - γ)) ^ (1 / γ)

theorem crra_pos (γ b R : ℝ) (hb : 0 < b) (hR : 0 < R) : 0 < crraRate γ b R :=
  Real.rpow_pos_of_pos (mul_pos hb (Real.rpow_pos_of_pos hR _)) _

/-- With a common `γ`, CRRA saving rates stand in a fixed ratio at every return. -/
theorem crra_ratio (γ bk bh R : ℝ) (hk : 0 < bk) (hh : 0 < bh) (hR : 0 < R) :
    crraRate γ bk R = (bk / bh) ^ (1 / γ) * crraRate γ bh R := by
  unfold crraRate
  rw [← Real.mul_rpow (div_pos hk hh).le (mul_pos hh (Real.rpow_pos_of_pos hR _)).le,
    ← mul_assoc, div_mul_cancel₀ bk hh.ne']

/-- **CRRA with a common `γ`**: the most patient household takes everything, along any
positive path of returns. -/
theorem crra_takes_all [Nonempty H] (g c γ : ℝ) (β x0 : H → ℝ) (R : ℕ → ℝ) (hg : 1 + g ≠ 0)
    (hγ : 0 < γ) (hβ : ∀ h, 0 < β h) (hR : ∀ t, 0 < R t) (hx0 : ∀ h, 0 < x0 h)
    (hsum : ∑ h, x0 h = 1) (h : H) (htop : ∀ k, k ≠ h → β k < β h) :
    Tendsto (fun n => path g 0 c Finset.univ (fun t k => crraRate γ (β k) (R t)) x0 n h)
      atTop (𝓝 1) :=
  most_patient_takes_all g c _ x0 hg (fun t k => crra_pos γ (β k) (R t) (hβ k) (hR t)) hx0 hsum
    h (fun k => (β k / β h) ^ (1 / γ))
    (fun k => Real.rpow_nonneg (div_nonneg (hβ k).le (hβ h).le) _)
    (fun k hk => Real.rpow_lt_one (div_nonneg (hβ k).le (hβ h).le)
      ((div_lt_one (hβ h)).2 (htop k hk)) (one_div_pos.2 hγ))
    (fun k _ t => (crra_ratio γ (β k) (β h) (R t) (hβ k) (hβ h) (hR t)).le)

/-! ## Unequal access -/

/-- **Exclusion dilutes.** With no equal part, an excluded household whose saving rate is at
most `κ` times the lowest rate holds at most `(κ / (1 + g)) ^ n` of its starting share. -/
theorem excluded_dilution (g c : ℝ) (A : Finset H) (hAne : A.Nonempty) (s : ℕ → H → ℝ)
    (x0 : H → ℝ) (h : H) (hA : h ∉ A) (lo κ : ℝ) (hlo : 0 < lo) (hg : 0 < g) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t k, lo ≤ s t k) (hκ : ∀ t, s t h ≤ κ * lo)
    (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1) (n : ℕ) :
    path g 0 c A s x0 n h ≤ (κ / (1 + g)) ^ n * x0 h := by
  have hκ0 : 0 ≤ κ := by
    have h1 := hκ 0
    have h2 := hs 0 h
    nlinarith
  have hne : (1:ℝ) + g ≠ 0 := by linarith
  induction n with
  | zero => simp [path]
  | succ n ih =>
    obtain ⟨hp, hps⟩ := path_pos_sum g 0 c A hAne s x0 hg le_rfl zero_le_one hc0 hc
      (fun t k => lt_of_lt_of_le hlo (hs t k)) hx0 hsum n
    have hBlo := B_ge (s n) (path g 0 c A s x0 n) lo (hs n) (fun k => (hp k).le) hps
    have hB : 0 < B (s n) (path g 0 c A s x0 n) := lt_of_lt_of_le hlo hBlo
    have hpost : post (s n) (path g 0 c A s x0 n) h ≤ κ * path g 0 c A s x0 n h := by
      unfold post
      rw [div_le_iff₀ hB]
      have := hp h
      nlinarith [hκ n, mul_le_mul_of_nonneg_left hBlo hκ0]
    show step g 0 c A (s n) (path g 0 c A s x0 n) h ≤ _
    rw [excluded_step g 0 c A (s n) _ h hA, div_le_iff₀ (by linarith)]
    have h2 := mul_le_mul_of_nonneg_left ih hκ0
    have e : (κ / (1 + g)) ^ (n + 1) * x0 h * (1 + g) = κ * ((κ / (1 + g)) ^ n * x0 h) := by
      rw [pow_succ, show (κ / (1 + g)) ^ n * (κ / (1 + g)) * x0 h * (1 + g) =
        (κ / (1 + g)) ^ n * x0 h * (κ / (1 + g) * (1 + g)) by ring, div_mul_cancel₀ κ hne]
      ring
    rw [e]
    nlinarith

/-- Comparison sequence for an excluded household's share. -/
def low (ρ g σ c z0 : ℝ) : ℕ → ℝ
  | 0 => z0
  | n + 1 => (ρ * low ρ g σ c z0 n + g * σ * c) / (1 + g)

theorem low_dev (ρ g σ c z0 : ℝ) (hg : 0 < g) (hρ1 : ρ < 1 + g) (n : ℕ) :
    low ρ g σ c z0 n = g * σ * c / (1 + g - ρ) +
      (ρ / (1 + g)) ^ n * (z0 - g * σ * c / (1 + g - ρ)) := by
  have h1 : (1:ℝ) + g ≠ 0 := by linarith
  have h2 : (1:ℝ) + g - ρ ≠ 0 := by linarith
  induction n with
  | zero => simp [low]
  | succ n ih =>
    show (ρ * low ρ g σ c z0 n + g * σ * c) / (1 + g) = _
    rw [ih, pow_succ]
    field_simp
    ring

theorem low_tends (ρ g σ c z0 : ℝ) (hg : 0 < g) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1 + g) :
    Tendsto (low ρ g σ c z0) atTop (𝓝 (g * σ * c / (1 + g - ρ))) := by
  have q0 : 0 ≤ ρ / (1 + g) := div_nonneg hρ (by linarith)
  have q1 : ρ / (1 + g) < 1 := (div_lt_one (by linarith)).2 hρ1
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one q0 q1).mul_const
    (z0 - g * σ * c / (1 + g - ρ))
  rw [zero_mul] at h
  have h2 := (tendsto_const_nhds (x := g * σ * c / (1 + g - ρ))).add h
  rw [add_zero] at h2
  have e : low ρ g σ c z0 = fun n => g * σ * c / (1 + g - ρ) +
      (ρ / (1 + g)) ^ n * (z0 - g * σ * c / (1 + g - ρ)) :=
    funext fun n => low_dev ρ g σ c z0 hg hρ1 n
  rw [e]
  exact h2

/-- **Equal issuance protects an excluded household**: its share stays above the comparison
sequence with `ρ = lo / hi`. -/
theorem excluded_floor (g σ c : ℝ) (A : Finset H) (hAne : A.Nonempty) (s : ℕ → H → ℝ)
    (x0 : H → ℝ) (h : H) (hA : h ∉ A) (lo hi : ℝ) (hlo : 0 < lo) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1)
    (hs : ∀ t k, lo ≤ s t k) (hhi : ∀ t k, s t k ≤ hi) (hx0 : ∀ k, 0 < x0 k)
    (hsum : ∑ k, x0 k = 1) (n : ℕ) :
    low (lo / hi) g σ c (x0 h) n ≤ path g σ c A s x0 n h := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (hs 0 h) (hhi 0 h))
  have hρ : 0 ≤ lo / hi := div_nonneg hlo.le hhi0.le
  induction n with
  | zero => simp [low, path]
  | succ n ih =>
    obtain ⟨hp, hps⟩ := path_pos_sum g σ c A hAne s x0 hg hσ0 hσ1 hc0 hc
      (fun t k => lt_of_lt_of_le hlo (hs t k)) hx0 hsum n
    have hBhi := B_le (s n) (path g σ c A s x0 n) hi (hhi n) (fun k => (hp k).le) hps
    have hB : 0 < B (s n) (path g σ c A s x0 n) :=
      lt_of_lt_of_le hlo (B_ge (s n) _ lo (hs n) (fun k => (hp k).le) hps)
    have hpost : lo / hi * path g σ c A s x0 n h ≤ post (s n) (path g σ c A s x0 n) h := by
      unfold post
      rw [le_div_iff₀ hB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hhi0]
      have := hp h
      nlinarith [hs n h, mul_le_mul_of_nonneg_left hBhi (mul_nonneg hlo.le this.le),
        mul_le_mul_of_nonneg_right (hs n h) (mul_nonneg hhi0.le this.le)]
    show (lo / hi * low (lo / hi) g σ c (x0 h) n + g * σ * c) / (1 + g) ≤
      step g σ c A (s n) (path g σ c A s x0 n) h
    rw [excluded_step g σ c A (s n) _ h hA]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left ih hρ]

/-- **The protected share.** Any target below `g σ c / (1 + g − lo / hi)` is eventually exceeded
by an excluded household; with a common saving rate (`lo = hi`) that level is `σ c`. -/
theorem excluded_floor_eventually (g σ c : ℝ) (A : Finset H) (hAne : A.Nonempty)
    (s : ℕ → H → ℝ) (x0 : H → ℝ) (h : H) (hA : h ∉ A) (lo hi : ℝ) (hlo : 0 < lo) (hg : 0 < g)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1)
    (hs : ∀ t k, lo ≤ s t k) (hhi : ∀ t k, s t k ≤ hi) (hx0 : ∀ k, 0 < x0 k)
    (hsum : ∑ k, x0 k = 1) (f : ℝ) (hf : f < g * σ * c / (1 + g - lo / hi)) :
    ∀ᶠ n in atTop, f < path g σ c A s x0 n h := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (hs 0 h) (hhi 0 h))
  have hρ : 0 ≤ lo / hi := div_nonneg hlo.le hhi0.le
  have hρ1 : lo / hi < 1 + g := by
    have : lo / hi ≤ 1 := (div_le_one hhi0).2 (le_trans (hs 0 h) (hhi 0 h))
    linarith
  filter_upwards [(low_tends (lo / hi) g σ c (x0 h) hg hρ hρ1).eventually (lt_mem_nhds hf)]
    with n hn
  exact lt_of_lt_of_le hn
    (excluded_floor g σ c A hAne s x0 h hA lo hi hlo hg hσ0 hσ1 hc0 hc hs hhi hx0 hsum n)

theorem common_rate_level (g σ c : ℝ) (hg : 0 < g) : g * σ * c / (1 + g - 1) = σ * c := by
  rw [show (1:ℝ) + g - 1 = g by ring]
  field_simp

end HeterogeneousIssuance

end

#print axioms HeterogeneousIssuance.aggregate_demand
#print axioms HeterogeneousIssuance.clearing_unique
#print axioms HeterogeneousIssuance.clearing_exists
#print axioms HeterogeneousIssuance.equilibrium_return
#print axioms HeterogeneousIssuance.units_share
#print axioms HeterogeneousIssuance.consumption_share_iff
#print axioms HeterogeneousIssuance.B_ge
#print axioms HeterogeneousIssuance.B_le
#print axioms HeterogeneousIssuance.step_sum
#print axioms HeterogeneousIssuance.reduces_to_common
#print axioms HeterogeneousIssuance.excluded_step
#print axioms HeterogeneousIssuance.floor_every_step
#print axioms HeterogeneousIssuance.path_pos_sum
#print axioms HeterogeneousIssuance.pro_rata_closed
#print axioms HeterogeneousIssuance.ratio_bound
#print axioms HeterogeneousIssuance.ratio_vanishes
#print axioms HeterogeneousIssuance.most_patient_takes_all
#print axioms HeterogeneousIssuance.log_takes_all
#print axioms HeterogeneousIssuance.crra_ratio
#print axioms HeterogeneousIssuance.crra_takes_all
#print axioms HeterogeneousIssuance.excluded_dilution
#print axioms HeterogeneousIssuance.low_tends
#print axioms HeterogeneousIssuance.excluded_floor
#print axioms HeterogeneousIssuance.excluded_floor_eventually
#print axioms HeterogeneousIssuance.common_rate_level
