import Mathlib

/-!
# Stage 357: the long-run distribution, wealth-dependent access, growth, and forward-looking saving

Builds on the stage-356 issuance equilibrium (definitions restated here so the file stands alone).

* Long-run distribution (`stationary_exists`, `stationary_fixed`, `stationary_unique`,
  `fixed_form`): with full access and any `σ > 0`, there is exactly one long-run distribution.
  It has the closed form `x h = g σ c / (1 + g − l s h)`, where `l` solves `∑ x h = 1`.
* Its properties: every share is at least `g σ c / (1 + g)` (`stationary_floor`); more patient
  households hold strictly more (`stationary_monotone`, `stationary_l_pos`); with a common saving
  rate it is the equal distribution (`common_stationary`); the return is `l / (1 + g (1 − σ))`
  (`stationary_return`).
* Wealth-dependent access (`above`, `pathA`): only households holding at least `θ` take part in
  the pro rata part. `trapped`: below the threshold, a household whose saving rate is at most `κ`
  times the lowest stays below forever when `κ θ + g σ c ≤ (1 + g) θ`; `trapped_decay`: with no
  equal part it is diluted geometrically. `escape`: when `θ < g σ c / (1 + g − lo/hi)`, every
  household eventually holds more than `θ` for good. `common_dichotomy`: with a common saving rate
  the line is exactly `σ c` against `θ`.
* Growth (`growth_gap`, `growth_gap_lower`, `common_no_cost`, `pro_rata_growth_limit`): the
  aggregate saving rate falls short of the highest by at most the spread of patience times the
  share not held by the most patient, and by at least the gap to the second-highest times that
  share. Under pro rata issuance it tends to the highest rate; with equal patience the issuance
  rule costs no growth.
* Forward-looking CRRA saving (`fut`, `fsave`, `fut_recursion`, `recursion_unique`,
  `fut_compare`, `save_ratio`, `forward_takes_all`): the Euler-and-budget recursion
  `u t = b r t (1 + u (t + 1))` (with `b = β ^ (1/γ)`, `r t = R (t+1) ^ ((1−γ)/γ)`) has exactly
  one bounded solution, the discounted sum `fut`. A less patient household's sum is at most
  `b k / b h` times the more patient one's, at every date and along any bounded return path, so
  its saving rate is at most a fixed fraction `ρ < 1` of the other's. Under pro rata issuance the
  most patient household therefore takes everything, along any return path with
  `0 < r t ≤ rhi`, `b h rhi < 1`, including an equilibrium one.

Limits: saving is characterised by the Euler equation and budget, not derived from a utility
maximisation proof; existence of a perfect-foresight equilibrium path with forward-looking saving
is not proved (the result holds on any such path); convergence to the long-run distribution is
not proved; access and patience are exogenous.
-/

noncomputable section

open Finset BigOperators Filter Topology

namespace LongRunOwnership

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Wealth-weighted aggregate saving rate. -/
def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

/-- Share of units held after trade. -/
def post (s x : H → ℝ) (h : H) : ℝ := s h * x h / B s x

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

/-! ## Common lemmas -/

omit [DecidableEq H] in
theorem post_le (s x : H → ℝ) (h : H) (lo κ : ℝ) (hlo : 0 < lo) (hs : ∀ k, lo ≤ s k)
    (hκ : s h ≤ κ * lo) (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) : post s x h ≤ κ * x h := by
  have hBlo := B_ge s x lo hs hx hsum
  have hB : 0 < B s x := lt_of_lt_of_le hlo hBlo
  have hκ0 : 0 ≤ κ := by nlinarith [hs h]
  unfold post
  rw [div_le_iff₀ hB]
  calc s h * x h ≤ κ * lo * x h := mul_le_mul_of_nonneg_right hκ (hx h)
    _ ≤ κ * B s x * x h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBlo hκ0) (hx h)
    _ = κ * x h * B s x := by ring

omit [DecidableEq H] in
theorem post_ge (s x : H → ℝ) (h : H) (lo hi : ℝ) (hlo : 0 < lo) (hs : ∀ k, lo ≤ s k)
    (hhi : ∀ k, s k ≤ hi) (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) :
    lo / hi * x h ≤ post s x h := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (hs h) (hhi h))
  have hBhi := B_le s x hi hhi hx hsum
  have hB : 0 < B s x := lt_of_lt_of_le hlo (B_ge s x lo hs hx hsum)
  unfold post
  rw [le_div_iff₀ hB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hhi0]
  nlinarith [hs h, mul_le_mul_of_nonneg_left hBhi (mul_nonneg hlo.le (hx h)),
    mul_le_mul_of_nonneg_right (hs h) (mul_nonneg hhi0.le (hx h))]

/-- Whatever the access rule, a household gets at least its post-trade units plus the equal part. -/
theorem step_ge (g σ c : ℝ) (A : Finset H) (s x : H → ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hs : ∀ h, 0 ≤ s h) (hx : ∀ h, 0 ≤ x h) (h : H) :
    (post s x h + g * σ * c) / (1 + g) ≤ step g σ c A s x h := by
  unfold step
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith [mul_nonneg hg.le (mul_nonneg (sub_nonneg.2 hσ1) (prorata_nonneg A s x hs hx h))]

/-! ## Item 1: the long-run distribution under full access -/

def amp (g σ : ℝ) : ℝ := 1 + g * (1 - σ)

/-- Candidate stationary shares, indexed by the multiplier `l`. -/
def xs (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (h : H) : ℝ := g * σ * c / (1 + g - l * s h)

def F (g σ c : ℝ) (s : H → ℝ) (l : ℝ) : ℝ := ∑ h, xs g σ c s l h

theorem step_full (g σ c : ℝ) (s x : H → ℝ) (hB : B s x ≠ 0) (h : H) :
    step g σ c Finset.univ s x h = (amp g σ * post s x h + g * σ * c) / (1 + g) := by
  unfold step amp
  rw [full_access_prorata s x hB]
  ring

omit [DecidableEq H] in
theorem c_le_one [Nonempty H] (c : ℝ) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) :
    c ≤ 1 := by
  have hN : (1:ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos
  nlinarith [mul_le_mul_of_nonneg_left hN hc0.le]

omit [DecidableEq H] in
/-- **A long-run distribution exists**: the multiplier equation `F l = 1` has a root. -/
theorem stationary_exists [Nonempty H] (g σ c : ℝ) (s : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ h, 0 < s h) :
    ∃ l, 0 ≤ l ∧ (∀ h, 0 < 1 + g - l * s h) ∧ F g σ c s l = 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  have hgsc : 0 < g * σ * c := by positivity
  have hc1 := c_le_one c hc0 hc
  have hσc : σ * c ≤ 1 := by nlinarith
  have hgle : g * σ * c ≤ g := by nlinarith
  set l1 := (1 + g - g * σ * c) / s m with hl1def
  have hl1 : 0 ≤ l1 := div_nonneg (by linarith) (hs m).le
  have e : l1 * s m = 1 + g - g * σ * c := div_mul_cancel₀ _ (hs m).ne'
  have hden : ∀ l ∈ Set.Icc (0:ℝ) l1, ∀ h, g * σ * c ≤ 1 + g - l * s h := by
    intro l hl h
    nlinarith [mul_le_mul_of_nonneg_left (hm h (Finset.mem_univ h)) hl.1,
      mul_le_mul_of_nonneg_right hl.2 (hs m).le]
  have hcont : ContinuousOn (F g σ c s) (Set.Icc 0 l1) := by
    show ContinuousOn (fun l => ∑ h ∈ Finset.univ, g * σ * c / (1 + g - l * s h)) _
    apply continuousOn_finsetSum
    intro h _
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
    · intro l hl
      exact (lt_of_lt_of_le hgsc (hden l hl h)).ne'
  have hF0 : F g σ c s 0 ≤ 1 := by
    show ∑ h, g * σ * c / (1 + g - 0 * s h) ≤ 1
    simp only [zero_mul, sub_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc,
      div_le_one (by linarith)]
    have : (Fintype.card H : ℝ) * (g * σ * c) = g * σ := by linear_combination g * σ * hc
    nlinarith
  have hF1 : 1 ≤ F g σ c s l1 := by
    have hnn : ∀ h ∈ Finset.univ, 0 ≤ xs g σ c s l1 h := fun h _ =>
      div_nonneg hgsc.le (le_trans hgsc.le (hden l1 ⟨hl1, le_rfl⟩ h))
    have := Finset.single_le_sum hnn (Finset.mem_univ m)
    have hxm : xs g σ c s l1 m = 1 := by
      unfold xs
      rw [e, show (1:ℝ) + g - (1 + g - g * σ * c) = g * σ * c by ring, div_self hgsc.ne']
    unfold F
    linarith
  obtain ⟨l, hl, hFl⟩ := intermediate_value_Icc hl1 hcont ⟨hF0, hF1⟩
  exact ⟨l, hl.1, fun h => lt_of_lt_of_le hgsc (hden l hl h), hFl⟩

omit [Fintype H] [DecidableEq H] in
theorem xs_key (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hd : ∀ h, 0 < 1 + g - l * s h) (h : H) :
    xs g σ c s l h * (1 + g - l * s h) = g * σ * c :=
  div_mul_cancel₀ _ (hd h).ne'

omit [DecidableEq H] in
/-- At a root, the aggregate saving rate is tied to the multiplier: `l B = 1 + g (1 − σ)`. -/
theorem stationary_lB (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hd : ∀ h, 0 < 1 + g - l * s h)
    (hc : (Fintype.card H : ℝ) * c = 1) (hF : F g σ c s l = 1) :
    l * B s (xs g σ c s l) = amp g σ := by
  have h1 : ∑ h, xs g σ c s l h * (1 + g - l * s h) = g * σ := by
    rw [Finset.sum_congr rfl (fun h _ => xs_key g σ c s l hd h), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    linear_combination g * σ * hc
  have h2 : ∑ h, xs g σ c s l h * (1 + g - l * s h) =
      (1 + g) * ∑ h, xs g σ c s l h - l * B s (xs g σ c s l) := by
    unfold B
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hF' : ∑ h, xs g σ c s l h = 1 := hF
  unfold amp
  rw [hF'] at h2
  linarith

omit [Fintype H] [DecidableEq H] in
theorem xs_pos (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ : 0 < σ) (hc0 : 0 < c)
    (hd : ∀ h, 0 < 1 + g - l * s h) (h : H) : 0 < xs g σ c s l h :=
  div_pos (by positivity) (hd h)

/-- **The root is a long-run distribution**: positive shares summing to one, unchanged by the
equilibrium issuance step. -/
theorem stationary_fixed (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hd : ∀ h, 0 < 1 + g - l * s h) (hc : (Fintype.card H : ℝ) * c = 1)
    (hF : F g σ c s l = 1) (h : H) :
    step g σ c Finset.univ s (xs g σ c s l) h = xs g σ c s l h := by
  have hlB := stationary_lB g σ c s l hd hc hF
  have hamp : 0 < amp g σ := by unfold amp; nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]
  have hB : B s (xs g σ c s l) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hlB
    linarith
  rw [step_full g σ c s _ hB, div_eq_iff (by linarith)]
  have e : amp g σ * post s (xs g σ c s l) h = l * s h * xs g σ c s l h := by
    unfold post
    rw [← hlB]
    field_simp
  rw [e]
  linear_combination (-1:ℝ) * xs_key g σ c s l hd h

omit [DecidableEq H] in
theorem F_strict (g σ c : ℝ) (s : H → ℝ) [Nonempty H] (hg : 0 < g) (hσ : 0 < σ) (hc0 : 0 < c)
    (hs : ∀ h, 0 < s h) (l1 l2 : ℝ) (h12 : l1 < l2) (hd : ∀ h, 0 < 1 + g - l2 * s h) :
    F g σ c s l1 < F g σ c s l2 := by
  unfold F
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro h _
  unfold xs
  apply div_lt_div_of_pos_left (by positivity) (hd h)
  nlinarith [mul_lt_mul_of_pos_right h12 (hs h)]

/-- Every long-run distribution has the closed form `xs l` with `l = (1 + g (1 − σ)) / B`. -/
theorem fixed_form [Nonempty H] (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hc0 : 0 < c) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h)
    (hfix : ∀ h, step g σ c Finset.univ s x h = x h) :
    (∀ h, 0 < 1 + g - amp g σ / B s x * s h) ∧ ∀ h, x h = xs g σ c s (amp g σ / B s x) h := by
  have hB := B_pos s x hs hx
  have key : ∀ h, x h * (1 + g - amp g σ / B s x * s h) = g * σ * c := by
    intro h
    have := hfix h
    rw [step_full g σ c s x hB.ne', div_eq_iff (by linarith)] at this
    unfold post at this
    have e : amp g σ * (s h * x h / B s x) = amp g σ / B s x * s h * x h := by
      field_simp
    rw [e] at this
    linear_combination (-1:ℝ) * this
  have hgsc : 0 < g * σ * c := by positivity
  have hd : ∀ h, 0 < 1 + g - amp g σ / B s x * s h := fun h => by
    have := key h
    exact pos_of_mul_pos_right (this ▸ hgsc) (hx h).le
  refine ⟨hd, fun h => ?_⟩
  unfold xs
  rw [eq_div_iff (hd h).ne']
  exact key h

/-- **The long-run distribution is unique.** -/
theorem stationary_unique [Nonempty H] (g σ c : ℝ) (s x y : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hc0 : 0 < c) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) (hy : ∀ h, 0 < y h)
    (hxs : ∑ h, x h = 1) (hys : ∑ h, y h = 1)
    (hfx : ∀ h, step g σ c Finset.univ s x h = x h)
    (hfy : ∀ h, step g σ c Finset.univ s y h = y h) : x = y := by
  obtain ⟨dx, ex⟩ := fixed_form g σ c s x hg hσ hc0 hs hx hfx
  obtain ⟨dy, ey⟩ := fixed_form g σ c s y hg hσ hc0 hs hy hfy
  have Fx : F g σ c s (amp g σ / B s x) = 1 := by
    unfold F; rw [← hxs]; exact Finset.sum_congr rfl fun h _ => (ex h).symm
  have Fy : F g σ c s (amp g σ / B s y) = 1 := by
    unfold F; rw [← hys]; exact Finset.sum_congr rfl fun h _ => (ey h).symm
  have hl : amp g σ / B s x = amp g σ / B s y := by
    rcases lt_trichotomy (amp g σ / B s x) (amp g σ / B s y) with h | h | h
    · have := F_strict g σ c s hg hσ hc0 hs _ _ h dy; linarith
    · exact h
    · have := F_strict g σ c s hg hσ hc0 hs _ _ h dx; linarith
  funext h
  rw [ex h, ey h, hl]

omit [Fintype H] [DecidableEq H] in
/-- **Floor in the long run**: every stationary share is at least `g σ c / (1 + g)`. -/
theorem stationary_floor (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hc0 : 0 < c) (hl : 0 ≤ l) (hs : ∀ h, 0 < s h) (hd : ∀ h, 0 < 1 + g - l * s h) (h : H) :
    g * σ * c / (1 + g) ≤ xs g σ c s l h := by
  unfold xs
  apply div_le_div_of_nonneg_left (by positivity) (hd h)
  nlinarith [mul_nonneg hl (hs h).le]

omit [Fintype H] [DecidableEq H] in
/-- **More patient, larger long-run share.** -/
theorem stationary_monotone (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hc0 : 0 < c) (hl : 0 < l) (hd : ∀ h, 0 < 1 + g - l * s h) (h k : H) (hhk : s h < s k) :
    xs g σ c s l h < xs g σ c s l k := by
  unfold xs
  apply div_lt_div_of_pos_left (by positivity) (hd k)
  nlinarith [mul_lt_mul_of_pos_left hhk hl]

omit [DecidableEq H] in
theorem stationary_l_pos (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hl : 0 ≤ l) (hd : ∀ h, 0 < 1 + g - l * s h) (hc : (Fintype.card H : ℝ) * c = 1)
    (hF : F g σ c s l = 1) : 0 < l := by
  have hlB := stationary_lB g σ c s l hd hc hF
  have hamp : 0 < amp g σ := by unfold amp; nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]
  rcases hl.lt_or_eq with h | h
  · exact h
  · rw [← h, zero_mul] at hlB; linarith

/-- **Equal patience, equal ownership**: with a common saving rate the unique long-run
distribution is the equal one, `c = 1 / N` each. -/
theorem common_stationary [Nonempty H] (g σ c b : ℝ) (x : H → ℝ) (hg : 0 < g) (hσ : 0 < σ)
    (hc0 : 0 < c) (hc : (Fintype.card H : ℝ) * c = 1) (hb : 0 < b) (hx : ∀ h, 0 < x h)
    (hxs : ∑ h, x h = 1) (hfx : ∀ h, step g σ c Finset.univ (fun _ => b) x h = x h) :
    x = fun _ => c := by
  have hcs : ∑ _h : H, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have hBc : B (fun _ => b) (fun _ : H => c) = b := by
    show ∑ _k : H, b * c = b
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination b * hc
  have hfc : ∀ h : H, step g σ c Finset.univ (fun _ => b) (fun _ => c) h = c := by
    intro h
    rw [step_full g σ c _ _ (by rw [hBc]; exact hb.ne'), div_eq_iff (by linarith)]
    unfold post amp
    rw [hBc]
    field_simp
    ring
  exact stationary_unique g σ c (fun _ => b) x _ hg hσ hc0 (fun _ => hb) hx (fun _ => hc0)
    hxs hcs hfx hfc

/-! ## Item 2: access that depends on wealth -/

/-- Path with an access rule that depends on the current distribution. -/
def pathA (g σ c : ℝ) (α : (H → ℝ) → Finset H) (s : ℕ → H → ℝ) (x0 : H → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | n + 1 => step g σ c (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n)

theorem pathA_pos_sum (g σ c : ℝ) (α : (H → ℝ) → Finset H)
    (hα : ∀ x : H → ℝ, (∀ h, 0 < x h) → ∑ h, x h = 1 → (α x).Nonempty) (s : ℕ → H → ℝ)
    (x0 : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t h, 0 < s t h) (hx0 : ∀ h, 0 < x0 h)
    (hsum : ∑ h, x0 h = 1) (n : ℕ) :
    (∀ h, 0 < pathA g σ c α s x0 n h) ∧ ∑ h, pathA g σ c α s x0 n h = 1 := by
  induction n with
  | zero => exact ⟨hx0, hsum⟩
  | succ n ih =>
    obtain ⟨hp, hps⟩ := ih
    have hA := hα _ hp hps
    have : Nonempty H := ⟨hA.choose⟩
    have hB := B_pos (s n) _ (hs n) hp
    have hpost : ∀ h, 0 < post (s n) (pathA g σ c α s x0 n) h :=
      fun h => div_pos (mul_pos (hs n h) (hp h)) hB
    have hm : 0 < mass (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n) :=
      Finset.sum_pos (fun k _ => hpost k) hA
    refine ⟨fun h => ?_, step_sum g σ c _ (s n) _ (by linarith) hc hB.ne' hm.ne'⟩
    show 0 < step g σ c (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n) h
    unfold step
    apply div_pos _ (by linarith)
    have hq := prorata_nonneg (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n)
      (fun k => (hs n k).le) (fun k => (hp k).le) h
    nlinarith [hpost h, mul_nonneg hg.le (mul_nonneg hσ0 hc0),
      mul_nonneg hg.le (mul_nonneg (sub_nonneg.2 hσ1) hq)]

/-- Access only for households holding at least the threshold share `θ` (a minimum lot). -/
def above (θ : ℝ) (x : H → ℝ) : Finset H := Finset.univ.filter fun h => θ ≤ x h

omit [DecidableEq H] in
theorem above_nonempty (θ c : ℝ) (hθ : θ ≤ c) (hc : (Fintype.card H : ℝ) * c = 1)
    (x : H → ℝ) (hs : ∑ h, x h = 1) : (above θ x).Nonempty := by
  by_contra hne
  have hlt : ∀ h, x h < c := fun h => by
    by_contra hh
    exact hne ⟨h, Finset.mem_filter.2 ⟨Finset.mem_univ h, le_trans hθ (not_lt.1 hh)⟩⟩
  have hU : (Finset.univ : Finset H).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra h0
    rw [not_nonempty_iff] at h0
    simp [Fintype.card_eq_zero] at hc
  have := Finset.sum_lt_sum_of_nonempty hU (fun h _ => hlt h)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, hs] at this
  exact lt_irrefl _ this

/-- **The poverty trap.** A household below the threshold, whose saving rate is at most `κ`
times the lowest, stays below it forever when `κ θ + g σ c ≤ (1 + g) θ`. -/
theorem trapped (g σ c θ : ℝ) (hθ : θ ≤ c) (s : ℕ → H → ℝ) (x0 : H → ℝ) (h : H)
    (lo κ : ℝ) (hlo : 0 < lo) (hκ0 : 0 < κ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t k, lo ≤ s t k)
    (hκ : ∀ t, s t h ≤ κ * lo) (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1)
    (hcond : κ * θ + g * σ * c ≤ (1 + g) * θ) (n0 : ℕ)
    (hstart : pathA g σ c (above θ) s x0 n0 h < θ) (m : ℕ) :
    pathA g σ c (above θ) s x0 (n0 + m) h < θ := by
  induction m with
  | zero => simpa using hstart
  | succ m ih =>
    obtain ⟨hp, hps⟩ := pathA_pos_sum g σ c (above θ)
      (fun x _ hx => above_nonempty θ c hθ hc x hx) s x0 hg hσ0 hσ1 hc0 hc
      (fun t k => lt_of_lt_of_le hlo (hs t k)) hx0 hsum (n0 + m)
    have hA : h ∉ above θ (pathA g σ c (above θ) s x0 (n0 + m)) := by
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      exact ih
    have hpost := post_le (s (n0 + m)) _ h lo κ hlo (hs (n0 + m)) (hκ (n0 + m))
      (fun k => (hp k).le) hps
    show step g σ c (above θ (pathA g σ c (above θ) s x0 (n0 + m))) (s (n0 + m))
      (pathA g σ c (above θ) s x0 (n0 + m)) h < θ
    rw [excluded_step _ _ _ _ _ _ h hA, div_lt_iff₀ (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left ih hκ0]

/-- **Trapped households are diluted.** With no equal part, a trapped household's share falls
at least geometrically, by the factor `κ / (1 + g)` per period. -/
theorem trapped_decay (g c θ : ℝ) (hθ : θ ≤ c) (s : ℕ → H → ℝ) (x0 : H → ℝ) (h : H)
    (lo κ : ℝ) (hlo : 0 < lo) (hκ0 : 0 < κ) (hg : 0 < g) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t k, lo ≤ s t k)
    (hκ : ∀ t, s t h ≤ κ * lo) (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1)
    (hcond : κ * θ ≤ (1 + g) * θ) (n0 : ℕ)
    (hstart : pathA g 0 c (above θ) s x0 n0 h < θ) (m : ℕ) :
    pathA g 0 c (above θ) s x0 (n0 + m) h ≤
      (κ / (1 + g)) ^ m * pathA g 0 c (above θ) s x0 n0 h := by
  have hne : (1:ℝ) + g ≠ 0 := by linarith
  induction m with
  | zero => simp
  | succ m ih =>
    have htr := trapped g 0 c θ hθ s x0 h lo κ hlo hκ0 hg le_rfl zero_le_one hc0 hc hs hκ hx0
      hsum (by simpa using hcond) n0 hstart m
    obtain ⟨hp, hps⟩ := pathA_pos_sum g 0 c (above θ)
      (fun x _ hx => above_nonempty θ c hθ hc x hx) s x0 hg le_rfl zero_le_one hc0 hc
      (fun t k => lt_of_lt_of_le hlo (hs t k)) hx0 hsum (n0 + m)
    have hA : h ∉ above θ (pathA g 0 c (above θ) s x0 (n0 + m)) := by
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      exact htr
    have hpost := post_le (s (n0 + m)) _ h lo κ hlo (hs (n0 + m)) (hκ (n0 + m))
      (fun k => (hp k).le) hps
    show step g 0 c (above θ (pathA g 0 c (above θ) s x0 (n0 + m))) (s (n0 + m))
      (pathA g 0 c (above θ) s x0 (n0 + m)) h ≤ _
    rw [excluded_step _ _ _ _ _ _ h hA, div_le_iff₀ (by linarith)]
    have e : (κ / (1 + g)) ^ (m + 1) * pathA g 0 c (above θ) s x0 n0 h * (1 + g) =
        κ * ((κ / (1 + g)) ^ m * pathA g 0 c (above θ) s x0 n0 h) := by
      rw [pow_succ]
      field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left ih hκ0.le]

/-- **Every household's share stays above the comparison sequence**, whatever the access rule. -/
theorem pathA_low (g σ c : ℝ) (α : (H → ℝ) → Finset H)
    (hα : ∀ x : H → ℝ, (∀ h, 0 < x h) → ∑ h, x h = 1 → (α x).Nonempty) (s : ℕ → H → ℝ)
    (x0 : H → ℝ) (h : H) (lo hi : ℝ) (hlo : 0 < lo) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t k, lo ≤ s t k)
    (hhi : ∀ t k, s t k ≤ hi) (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1) (n : ℕ) :
    low (lo / hi) g σ c (x0 h) n ≤ pathA g σ c α s x0 n h := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (hs 0 h) (hhi 0 h))
  have hρ : 0 ≤ lo / hi := div_nonneg hlo.le hhi0.le
  induction n with
  | zero => simp [low, pathA]
  | succ n ih =>
    obtain ⟨hp, hps⟩ := pathA_pos_sum g σ c α hα s x0 hg hσ0 hσ1 hc0 hc
      (fun t k => lt_of_lt_of_le hlo (hs t k)) hx0 hsum n
    have hpost := post_ge (s n) (pathA g σ c α s x0 n) h lo hi hlo (hs n) (hhi n)
      (fun k => (hp k).le) hps
    have hst := step_ge g σ c (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n) hg hσ1
      (fun k => le_trans hlo.le (hs n k)) (fun k => (hp k).le) h
    show (lo / hi * low (lo / hi) g σ c (x0 h) n + g * σ * c) / (1 + g) ≤
      step g σ c (α (pathA g σ c α s x0 n)) (s n) (pathA g σ c α s x0 n) h
    refine le_trans ?_ hst
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left ih hρ]

/-- **Escape.** If the threshold is below `g σ c / (1 + g − lo / hi)`, every household eventually
holds more than the threshold in every period: it gains access and keeps it. -/
theorem escape (g σ c θ : ℝ) (hθ : θ ≤ c) (s : ℕ → H → ℝ) (x0 : H → ℝ) (h : H) (lo hi : ℝ)
    (hlo : 0 < lo) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hs : ∀ t k, lo ≤ s t k) (hhi : ∀ t k, s t k ≤ hi)
    (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1) (hθlt : θ < g * σ * c / (1 + g - lo / hi)) :
    ∀ᶠ n in atTop, θ < pathA g σ c (above θ) s x0 n h := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (hs 0 h) (hhi 0 h))
  have hρ : 0 ≤ lo / hi := div_nonneg hlo.le hhi0.le
  have hρ1 : lo / hi < 1 + g := by
    have : lo / hi ≤ 1 := (div_le_one hhi0).2 (le_trans (hs 0 h) (hhi 0 h))
    linarith
  filter_upwards [(low_tends (lo / hi) g σ c (x0 h) hg hρ hρ1).eventually (lt_mem_nhds hθlt)]
    with n hn
  exact lt_of_lt_of_le hn (pathA_low g σ c (above θ)
    (fun x _ hx => above_nonempty θ c hθ hc x hx) s x0 h lo hi hlo hg hσ0 hσ1 hc0 hc hs hhi
    hx0 hsum n)

/-- **Common patience: a sharp dichotomy.** With a common saving rate, a household below the
threshold stays below it forever when `σ c ≤ θ`; when `σ c > θ`, every household eventually
holds more than the threshold for good. -/
theorem common_dichotomy (g σ c θ b : ℝ) (hθ : θ ≤ c) (x0 : H → ℝ) (h : H) (hb : 0 < b)
    (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1)
    (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1) :
    (σ * c ≤ θ → ∀ n0, pathA g σ c (above θ) (fun _ _ => b) x0 n0 h < θ →
        ∀ m, pathA g σ c (above θ) (fun _ _ => b) x0 (n0 + m) h < θ) ∧
    (θ < σ * c → ∀ᶠ n in atTop, θ < pathA g σ c (above θ) (fun _ _ => b) x0 n h) := by
  constructor
  · intro hle n0 hstart m
    exact trapped g σ c θ hθ _ x0 h b 1 hb one_pos hg hσ0 hσ1 hc0 hc (fun _ _ => le_rfl)
      (fun _ => by rw [one_mul]) hx0 hsum (by nlinarith [mul_le_mul_of_nonneg_left hle hg.le])
      n0 hstart m
  · intro hlt
    have e : g * σ * c / (1 + g - b / b) = σ * c := by
      rw [div_self hb.ne', show (1:ℝ) + g - 1 = g by ring]
      field_simp
    exact escape g σ c θ hθ _ x0 h b b hb hg hσ0 hσ1 hc0 hc (fun _ _ => le_rfl)
      (fun _ _ => le_rfl) hx0 hsum (by rw [e]; exact hlt)

/-! ## Item 4: growth inside the same model -/

/-- **Growth gap.** The aggregate saving rate falls short of the highest one by at most the
spread of patience times the share not held by the most patient household. -/
theorem growth_gap (s x : H → ℝ) (m : H) (lo : ℝ) (hlo : ∀ k, lo ≤ s k) (hm : ∀ k, s k ≤ s m)
    (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) :
    0 ≤ s m - B s x ∧ s m - B s x ≤ (s m - lo) * (1 - x m) := by
  have e : s m - B s x = ∑ k, (s m - s k) * x k := by
    have : ∑ k, (s m - s k) * x k = s m * ∑ k, x k - ∑ k, s k * x k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hsum]
    unfold B
    ring
  have hrest : ∑ k ∈ Finset.univ.erase m, x k = 1 - x m := by
    have := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at this
    linarith
  constructor
  · rw [e]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (sub_nonneg.2 (hm k)) (hx k)
  · rw [e, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), sub_self, zero_mul, zero_add]
    calc ∑ k ∈ Finset.univ.erase m, (s m - s k) * x k
        ≤ ∑ k ∈ Finset.univ.erase m, (s m - lo) * x k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (by linarith [hlo k]) (hx k)
      _ = (s m - lo) * (1 - x m) := by rw [← Finset.mul_sum, hrest]

/-- **Strict growth cost.** If every other household saves at most `s2 < s m`, the gap is at
least `(s m − s2)(1 − x m)`. -/
theorem growth_gap_lower (s x : H → ℝ) (m : H) (s2 : ℝ) (h2 : ∀ k, k ≠ m → s k ≤ s2)
    (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = 1) :
    (s m - s2) * (1 - x m) ≤ s m - B s x := by
  have e : s m - B s x = ∑ k ∈ Finset.univ.erase m, (s m - s k) * x k := by
    have : ∑ k, (s m - s k) * x k = s m * ∑ k, x k - ∑ k, s k * x k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), sub_self, zero_mul, zero_add] at this
    rw [this, hsum]
    unfold B
    ring
  have hrest : ∑ k ∈ Finset.univ.erase m, x k = 1 - x m := by
    have := hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at this
    linarith
  rw [e, ← hrest, Finset.mul_sum]
  exact Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_right (by linarith [h2 k (Finset.ne_of_mem_erase hk)]) (hx k)

omit [DecidableEq H] in
/-- **Equal patience: the issuance rule costs no growth.** -/
theorem common_no_cost (b : ℝ) (x : H → ℝ) (hsum : ∑ k, x k = 1) : B (fun _ => b) x = b := by
  show ∑ k, b * x k = b
  rw [← Finset.mul_sum, hsum, mul_one]

/-- **Pro rata issuance drives the saving rate to the highest one.** -/
theorem pro_rata_growth_limit [Nonempty H] (g c : ℝ) (β x0 : H → ℝ) (hg : 1 + g ≠ 0)
    (hβ : ∀ h, 0 < β h) (hx0 : ∀ h, 0 < x0 h) (hsum : ∑ h, x0 h = 1) (h : H)
    (htop : ∀ k, k ≠ h → β k < β h) :
    Tendsto (fun n => B β (path g 0 c Finset.univ (fun _ => β) x0 n)) atTop (𝓝 (β h)) := by
  have hconc := most_patient_takes_all g c (fun _ => β) x0 hg (fun _ => hβ) hx0 hsum h
    (fun k => β k / β h) (fun k => div_nonneg (hβ k).le (hβ h).le)
    (fun k hk => (div_lt_one (hβ h)).2 (htop k hk))
    (fun k _ _ => (div_mul_cancel₀ (β k) (hβ h).ne').ge)
  have hm : ∀ k, β k ≤ β h := fun k => by
    by_cases hk : k = h
    · rw [hk]
    · exact (htop k hk).le
  have hup : Tendsto (fun n => β h * (1 - path g 0 c Finset.univ (fun _ => β) x0 n h)) atTop
      (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub hconc
    rw [sub_self] at this
    have := this.const_mul (β h)
    rwa [mul_zero] at this
  have hgap : Tendsto (fun n => β h - B β (path g 0 c Finset.univ (fun _ => β) x0 n)) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hup
    · exact (growth_gap β _ h 0 (fun k => (hβ k).le) hm
        (path_full_nonneg g c _ x0 hg (fun _ => hβ) hx0 hsum n)
        (path_full_sum g c _ x0 hg (fun _ => hβ) hx0 hsum n)).1
    · have := (growth_gap β _ h 0 (fun k => (hβ k).le) hm
        (path_full_nonneg g c _ x0 hg (fun _ => hβ) hx0 hsum n)
        (path_full_sum g c _ x0 hg (fun _ => hβ) hx0 hsum n)).2
      rwa [sub_zero] at this
  have := (tendsto_const_nhds (x := β h)).sub hgap
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  ring

omit [DecidableEq H] in
/-- **Return in the long run**: at a stationary distribution the gross return on ownership is
`1 / B = l / (1 + g (1 − σ))`. -/
theorem stationary_return (g σ c : ℝ) (s : H → ℝ) (l : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1)
    (hd : ∀ h, 0 < 1 + g - l * s h) (hc : (Fintype.card H : ℝ) * c = 1)
    (hF : F g σ c s l = 1) : 1 / B s (xs g σ c s l) = l / amp g σ := by
  have hlB := stationary_lB g σ c s l hd hc hF
  have hamp : 0 < amp g σ := by unfold amp; nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]
  have hB : B s (xs g σ c s l) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hlB; linarith
  rw [div_eq_div_iff hB hamp.ne', ← hlB]
  ring

/-! ## Item 3: forward-looking CRRA saving along the transition

For CRRA utility with discount factor `β` and curvature `γ`, the Euler equation and budget give
the consumption-to-wealth ratio `m t` through `1 / m t = 1 + b r t / m (t + 1)`, with
`b = β ^ (1 / γ)` and `r t = R (t + 1) ^ ((1 − γ) / γ)`. Writing `u = 1 / m − 1`, this is
`u t = b r t (1 + u (t + 1))`, and the saving rate is `u / (1 + u)`. Its bounded solution is the
discounted sum `fut b r t`. -/

def term (b : ℝ) (r : ℕ → ℝ) (t j : ℕ) : ℝ := b ^ (j + 1) * ∏ i ∈ Finset.range (j + 1), r (t + i)

def fut (b : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, term b r t j

def fsave (b : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ := fut b r t / (1 + fut b r t)

theorem term_nonneg (b : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t) (t j : ℕ) :
    0 ≤ term b r t j :=
  mul_nonneg (pow_nonneg hb _) (Finset.prod_nonneg fun _ _ => hr _)

theorem term_le (b : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t)
    (hrhi : ∀ t, r t ≤ rhi) (t j : ℕ) : term b r t j ≤ (b * rhi) ^ (j + 1) := by
  unfold term
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb _)
  calc ∏ i ∈ Finset.range (j + 1), r (t + i) ≤ ∏ _i ∈ Finset.range (j + 1), rhi := by
        gcongr with i hi <;> first | exact hrhi _ | exact fun _ _ => hr _
    _ = rhi ^ (j + 1) := by rw [Finset.prod_const, Finset.card_range]

theorem term_summable (b : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t)
    (hrhi : ∀ t, r t ≤ rhi) (hq : b * rhi < 1) (t : ℕ) : Summable (term b r t) := by
  have hq0 : 0 ≤ b * rhi := mul_nonneg hb (le_trans (hr 0) (hrhi 0))
  have hg : Summable fun j : ℕ => (b * rhi) ^ (j + 1) := by
    simp_rw [pow_succ]
    exact (summable_geometric_of_lt_one hq0 hq).mul_right _
  exact Summable.of_nonneg_of_le (term_nonneg b r hb hr t) (term_le b r rhi hb hr hrhi t) hg

theorem fut_nonneg (b : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t) (t : ℕ) :
    0 ≤ fut b r t :=
  tsum_nonneg (term_nonneg b r hb hr t)

theorem fut_pos (b : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hb : 0 < b) (hr : ∀ t, 0 < r t)
    (hrhi : ∀ t, r t ≤ rhi) (hq : b * rhi < 1) (t : ℕ) : 0 < fut b r t := by
  have hs := term_summable b r rhi hb.le (fun t => (hr t).le) hrhi hq t
  have h0 : 0 < term b r t 0 := by
    unfold term
    simp only [zero_add, pow_one, Finset.prod_range_one, add_zero]
    exact mul_pos hb (hr t)
  exact lt_of_lt_of_le h0 (hs.le_tsum 0 fun j _ => term_nonneg b r hb.le (fun t => (hr t).le) t j)

/-- The discounted sum is bounded by the geometric bound `b rhi / (1 − b rhi)`. -/
theorem fut_le (b : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t)
    (hrhi : ∀ t, r t ≤ rhi) (hq : b * rhi < 1) (t : ℕ) :
    fut b r t ≤ b * rhi / (1 - b * rhi) := by
  have hq0 : 0 ≤ b * rhi := mul_nonneg hb (le_trans (hr 0) (hrhi 0))
  have hgeo := summable_geometric_of_lt_one hq0 hq
  have e : ∑' j : ℕ, (b * rhi) ^ (j + 1) = b * rhi / (1 - b * rhi) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq]
    field_simp
  rw [← e]
  apply Summable.tsum_le_tsum (term_le b r rhi hb hr hrhi t)
    (term_summable b r rhi hb hr hrhi hq t)
  simp_rw [pow_succ]
  exact hgeo.mul_right _

/-- **The Euler-and-budget recursion**: `u t = b r t (1 + u (t + 1))`. -/
theorem fut_recursion (b : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t)
    (hrhi : ∀ t, r t ≤ rhi) (hq : b * rhi < 1) (t : ℕ) :
    fut b r t = b * r t * (1 + fut b r (t + 1)) := by
  have hs := term_summable b r rhi hb hr hrhi hq t
  have hs1 := term_summable b r rhi hb hr hrhi hq (t + 1)
  unfold fut
  rw [hs.tsum_eq_zero_add, mul_add, mul_one, ← tsum_mul_left]
  congr 1
  · simp [term]
  · congr 1
    funext j
    unfold term
    rw [Finset.prod_range_succ' _ (j + 1), pow_succ]
    have : ∀ i ∈ Finset.range (j + 1), r (t + (i + 1)) = r (t + 1 + i) :=
      fun i _ => by rw [show t + (i + 1) = t + 1 + i by ring]
    rw [Finset.prod_congr rfl this, add_zero]
    ring

/-- **The bounded solution is unique**: any bounded sequence satisfying the recursion is `fut`
(the transversality condition singles it out). -/
theorem recursion_unique (b : ℝ) (r : ℕ → ℝ) (rhi M : ℝ) (hb : 0 ≤ b) (hr : ∀ t, 0 ≤ r t)
    (hrhi : ∀ t, r t ≤ rhi) (hq : b * rhi < 1) (w : ℕ → ℝ)
    (hw : ∀ t, w t = b * r t * (1 + w (t + 1))) (hM : ∀ t, |w t| ≤ M) (t : ℕ) :
    w t = fut b r t := by
  have hq0 : 0 ≤ b * rhi := mul_nonneg hb (le_trans (hr 0) (hrhi 0))
  set U := b * rhi / (1 - b * rhi)
  set d : ℕ → ℝ := fun t => w t - fut b r t with hd
  have hrec : ∀ t, d t = b * r t * d (t + 1) := fun t => by
    simp only [hd]
    rw [hw t, fut_recursion b r rhi hb hr hrhi hq t]
    ring
  have hbd : ∀ t, |d t| ≤ M + U := fun t => by
    simp only [hd]
    have h1 := fut_nonneg b r hb hr t
    have h2 := fut_le b r rhi hb hr hrhi hq t
    calc |w t - fut b r t| ≤ |w t| + |fut b r t| := abs_sub _ _
      _ ≤ M + U := by rw [abs_of_nonneg h1]; linarith [hM t]
  have hpow : ∀ n t, |d t| ≤ (b * rhi) ^ n * (M + U) := by
    intro n
    induction n with
    | zero => intro t; simpa using hbd t
    | succ n ih =>
      intro t
      rw [hrec t, abs_mul, abs_of_nonneg (mul_nonneg hb (hr t)), pow_succ']
      have h1 := ih (t + 1)
      calc b * r t * |d (t + 1)| ≤ b * rhi * |d (t + 1)| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrhi t) hb) (abs_nonneg _)
        _ ≤ b * rhi * ((b * rhi) ^ n * (M + U)) := mul_le_mul_of_nonneg_left h1 hq0
        _ = _ := by ring
  have hlim : Tendsto (fun n => (b * rhi) ^ n * (M + U)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const (M + U)
    rwa [zero_mul] at this
  have h0 : |d t| ≤ 0 := ge_of_tendsto' hlim fun n => hpow n t
  have : d t = 0 := abs_nonpos_iff.1 h0
  simp only [hd] at this
  linarith

/-- **A less patient household's forward sum is a fixed fraction of the more patient one's.** -/
theorem fut_compare (bk bh : ℝ) (r : ℕ → ℝ) (rhi : ℝ) (hk : 0 ≤ bk) (hkh : bk ≤ bh)
    (hh : 0 < bh) (hr : ∀ t, 0 ≤ r t) (hrhi : ∀ t, r t ≤ rhi) (hq : bh * rhi < 1) (t : ℕ) :
    fut bk r t ≤ bk / bh * fut bh r t := by
  have hqk : bk * rhi < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hkh (le_trans (hr 0) (hrhi 0))) hq
  unfold fut
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (term_summable bk r rhi hk hr hrhi hqk t)
    ((term_summable bh r rhi hh.le hr hrhi hq t).mul_left _)
  intro j
  unfold term
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => hr _)
  calc bk ^ (j + 1) = bk * bk ^ j := by ring
    _ ≤ bk * bh ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk hkh j) hk
    _ = bk / bh * bh ^ (j + 1) := by
        rw [pow_succ, div_mul_eq_mul_div, eq_div_iff hh.ne']; ring

/-- **Saving rates stand in a ratio bounded below one.** -/
theorem save_ratio (uk uh θ U : ℝ) (hk : 0 ≤ uk) (hh : 0 ≤ uh) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc : uk ≤ θ * uh) (hU : uh ≤ U) :
    uk / (1 + uk) ≤ θ * (1 + U) / (1 + θ * U) * (uh / (1 + uh)) := by
  have hU0 : 0 ≤ U := le_trans hh hU
  have h3 : 0 ≤ θ * uh := mul_nonneg hθ0 hh
  have s1 : uk / (1 + uk) ≤ θ * uh / (1 + θ * uh) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : (1 + uh) * (1 + θ * U) ≤ (1 + U) * (1 + θ * uh) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hU)]
  have e : θ * (1 + U) / (1 + θ * U) * (uh / (1 + uh)) =
      θ * (1 + U) * uh / ((1 + θ * U) * (1 + uh)) := by
    rw [div_mul_div_comm]
  refine s1.trans ?_
  rw [e, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 h3]

theorem ratio_lt_one (θ U : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hU : 0 ≤ U) :
    θ * (1 + U) / (1 + θ * U) < 1 := by
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **Forward-looking CRRA saving ends in complete concentration.** Along any return path with
`0 < r t ≤ rhi` and `b h rhi < 1` (in particular, along an equilibrium path, whatever it is), when
every household optimises with a common curvature and household `h` is strictly the most patient,
pro rata issuance concentrates all ownership on `h`. -/
theorem forward_takes_all [Nonempty H] (g c : ℝ) (b x0 : H → ℝ) (r : ℕ → ℝ) (rhi : ℝ)
    (hg : 1 + g ≠ 0) (hb : ∀ k, 0 < b k) (hr : ∀ t, 0 < r t) (hrhi : ∀ t, r t ≤ rhi)
    (hx0 : ∀ k, 0 < x0 k) (hsum : ∑ k, x0 k = 1) (h : H) (htop : ∀ k, k ≠ h → b k < b h)
    (hq : b h * rhi < 1) :
    Tendsto (fun n => path g 0 c Finset.univ (fun t k => fsave (b k) r t) x0 n h) atTop
      (𝓝 1) := by
  have hr0 : ∀ t, 0 ≤ r t := fun t => (hr t).le
  have hrhi0 : 0 ≤ rhi := le_trans (hr0 0) (hrhi 0)
  set U := b h * rhi / (1 - b h * rhi)
  have hU : 0 ≤ U := div_nonneg (mul_nonneg (hb h).le hrhi0) (by linarith)
  have hle : ∀ k, b k ≤ b h := fun k => by
    by_cases hk : k = h
    · rw [hk]
    · exact (htop k hk).le
  have hqk : ∀ k, b k * rhi < 1 := fun k =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hle k) hrhi0) hq
  refine most_patient_takes_all g c _ x0 hg (fun t k => ?_) hx0 hsum h
    (fun k => b k / b h * (1 + U) / (1 + b k / b h * U)) (fun k => ?_) (fun k hk => ?_)
    (fun k _ t => ?_)
  · have := fut_pos (b k) r rhi (hb k) hr hrhi (hqk k) t
    exact div_pos this (by linarith)
  · have := div_nonneg (hb k).le (hb h).le
    positivity
  · exact ratio_lt_one _ U (div_nonneg (hb k).le (hb h).le) ((div_lt_one (hb h)).2 (htop k hk)) hU
  · exact save_ratio _ _ _ U (fut_nonneg _ r (hb k).le hr0 t) (fut_nonneg _ r (hb h).le hr0 t)
      (div_nonneg (hb k).le (hb h).le) ((div_le_one (hb h)).2 (hle k))
      (fut_compare (b k) (b h) r rhi (hb k).le (hle k) (hb h) hr0 hrhi hq t)
      (fut_le (b h) r rhi (hb h).le hr0 hrhi hq t)

end LongRunOwnership

end

#print axioms LongRunOwnership.step_full
#print axioms LongRunOwnership.stationary_exists
#print axioms LongRunOwnership.stationary_lB
#print axioms LongRunOwnership.stationary_fixed
#print axioms LongRunOwnership.fixed_form
#print axioms LongRunOwnership.stationary_unique
#print axioms LongRunOwnership.stationary_floor
#print axioms LongRunOwnership.stationary_monotone
#print axioms LongRunOwnership.stationary_l_pos
#print axioms LongRunOwnership.common_stationary
#print axioms LongRunOwnership.pathA_pos_sum
#print axioms LongRunOwnership.above_nonempty
#print axioms LongRunOwnership.trapped
#print axioms LongRunOwnership.trapped_decay
#print axioms LongRunOwnership.pathA_low
#print axioms LongRunOwnership.escape
#print axioms LongRunOwnership.common_dichotomy
#print axioms LongRunOwnership.growth_gap
#print axioms LongRunOwnership.growth_gap_lower
#print axioms LongRunOwnership.common_no_cost
#print axioms LongRunOwnership.pro_rata_growth_limit
#print axioms LongRunOwnership.stationary_return
#print axioms LongRunOwnership.fut_recursion
#print axioms LongRunOwnership.recursion_unique
#print axioms LongRunOwnership.fut_compare
#print axioms LongRunOwnership.save_ratio
#print axioms LongRunOwnership.forward_takes_all
