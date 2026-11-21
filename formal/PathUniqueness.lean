import Mathlib

/-!
# Stage 370: when the transition path is unique

Stage 364 proved that a finite-horizon perfect-foresight equilibrium path exists for every
`γ > 0` (Brouwer), but not that it is unique. This file gives sufficient conditions for
uniqueness. The definitions of stage 364 are restated (`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`,
`IsEqN`), unchanged.

* `qs_eq`, `e_anti`: a household's saving rate times the return, `Q · F / (1 + F)` with
  `F = b Q ^ ((1 − γ) / γ) (1 + G)`, equals `1 / (1 / Q + 1 / (b (1 + G) Q ^ (1 / γ)))`, which is
  strictly increasing in `Q` for every `γ > 0`. So at a single date, with the distribution and the
  households' continuation plans `G` held fixed, at most one return clears the market.
* `date_unique`: that date-by-date statement for heterogeneous patience and non-negative
  ownership shares.
* **`unique_log`** (`γ = 1`, any heterogeneous patience): saving rates do not depend on returns,
  so the distribution path and the return path are pinned down date by date. Two equilibria over
  the same horizon from the same start agree at every date.
* **`unique_common`** (any `γ > 0`, common patience `b h = β₀`): every household saves at the
  same rate, so the distribution path does not depend on returns; returns are then pinned down
  by backward induction from the last date using `date_unique_common`. Two equilibria with
  positive return paths agree at every date.
* **`unique_one_period`** (any `γ > 0`, heterogeneous patience, horizon one): the equilibrium is
  unique.
* `date_unique_path`: for any horizon and heterogeneous patience, if two equilibria have the same
  distribution at date `t` and every household has the same continuation plan, they have the
  same return at `t`.

Limits: these are sufficient conditions. Uniqueness for heterogeneous patience with `γ ≠ 1` and
horizon above one is NOT proved: the distribution path then depends on returns and returns on
future distributions, and no contraction or monotonicity bound for that coupled system is given
here. No example of two distinct equilibrium paths is given either, so whether uniqueness can
fail there is open. Uniqueness is among equilibria with positive returns (`unique_common`,
`unique_one_period`); returns after the horizon play no role in the equilibrium conditions and
are not compared. The infinite-horizon path of stage 364 is not covered.
-/

noncomputable section

open Finset BigOperators

namespace PathUniqueness

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

theorem F_nonneg (b : ℝ) (hb : 0 ≤ b) (r : ℕ → ℝ) (hr : ∀ t, 0 ≤ r t) :
    ∀ k t, 0 ≤ F b r k t := by
  intro k
  induction k with
  | zero => intro t; show (0:ℝ) ≤ 0; exact le_rfl
  | succ k ih =>
    intro t
    show 0 ≤ b * r t * (1 + F b r k (t + 1))
    exact mul_nonneg (mul_nonneg hb (hr t)) (by linarith [ih (t + 1)])

/-! ## One date -/

/-- Saving rate times return, in a form that is visibly increasing in the return. -/
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

theorem e_anti (γ K q q' : ℝ) (hγ : 0 < γ) (hK : 0 < K) (hq : 0 < q) (hqq : q < q') :
    q'⁻¹ + (K * q' ^ (1 / γ))⁻¹ < q⁻¹ + (K * q ^ (1 / γ))⁻¹ := by
  have hq' : 0 < q' := by linarith
  have h1 : q'⁻¹ < q⁻¹ := (inv_lt_inv₀ hq' hq).2 hqq
  have h2 : q ^ (1 / γ) < q' ^ (1 / γ) := Real.rpow_lt_rpow hq.le hqq (by positivity)
  have h3 : (K * q' ^ (1 / γ))⁻¹ < (K * q ^ (1 / γ))⁻¹ :=
    (inv_lt_inv₀ (by positivity) (by positivity)).2 (mul_lt_mul_of_pos_left h2 hK)
  linarith

/-- The clearing term `(1 / q + 1 / (K q ^ (1 / γ)))⁻¹` is strictly increasing in `q`. -/
theorem psi_lt (γ K q q' : ℝ) (hγ : 0 < γ) (hK : 0 < K) (hq : 0 < q) (hqq : q < q') :
    (q⁻¹ + (K * q ^ (1 / γ))⁻¹)⁻¹ < (q'⁻¹ + (K * q' ^ (1 / γ))⁻¹)⁻¹ := by
  have hq' : 0 < q' := by linarith
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (e_anti γ K q q' hγ hK hq hqq)

/-- **Common patience, one date**: at most one return clears the market. -/
theorem date_unique_common (γ b G S q q' : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hG : 0 ≤ G)
    (hq : 0 < q) (hq' : 0 < q')
    (h1 : q = 1 / (b * q ^ ex γ * (1 + G) / (1 + b * q ^ ex γ * (1 + G)) * S))
    (h2 : q' = 1 / (b * q' ^ ex γ * (1 + G) / (1 + b * q' ^ ex γ * (1 + G)) * S)) :
    q = q' := by
  have hn1 : b * q ^ ex γ * (1 + G) / (1 + b * q ^ ex γ * (1 + G)) * S ≠ 0 := by
    intro h0; rw [h0, div_zero] at h1; linarith
  have hn2 : b * q' ^ ex γ * (1 + G) / (1 + b * q' ^ ex γ * (1 + G)) * S ≠ 0 := by
    intro h0; rw [h0, div_zero] at h2; linarith
  rw [eq_div_iff hn1] at h1
  rw [eq_div_iff hn2] at h2
  have k1 : S * (q⁻¹ + (b * (1 + G) * q ^ (1 / γ))⁻¹)⁻¹ = 1 := by
    rw [← qs_eq γ b G q hγ hb hG hq]; linarith
  have k2 : S * (q'⁻¹ + (b * (1 + G) * q' ^ (1 / γ))⁻¹)⁻¹ = 1 := by
    rw [← qs_eq γ b G q' hγ hb hG hq']; linarith
  have hS : S ≠ 0 := by intro h0; rw [h0, zero_mul] at k1; norm_num at k1
  have hK : 0 < b * (1 + G) := by have : 0 < 1 + G := by linarith
                                  positivity
  rcases lt_trichotomy q q' with h | h | h
  · have := psi_lt γ _ q q' hγ hK hq h
    have k : (q⁻¹ + (b * (1 + G) * q ^ (1 / γ))⁻¹)⁻¹ =
        (q'⁻¹ + (b * (1 + G) * q' ^ (1 / γ))⁻¹)⁻¹ := mul_left_cancel₀ hS (k1.trans k2.symm)
    linarith
  · exact h
  · have := psi_lt γ _ q' q hγ hK hq' h
    have k : (q⁻¹ + (b * (1 + G) * q ^ (1 / γ))⁻¹)⁻¹ =
        (q'⁻¹ + (b * (1 + G) * q' ^ (1 / γ))⁻¹)⁻¹ := mul_left_cancel₀ hS (k1.trans k2.symm)
    linarith

/-- The aggregate clearing expression with heterogeneous patience. -/
def Phi (γ : ℝ) (b G x : H → ℝ) (q : ℝ) : ℝ :=
  ∑ h, (q⁻¹ + (b h * (1 + G h) * q ^ (1 / γ))⁻¹)⁻¹ * x h

/-- **Heterogeneous patience, one date**: with the distribution `x ≥ 0` and the continuation
plans `G` fixed, at most one return clears the market. -/
theorem date_unique (γ q q' : ℝ) (b G x : H → ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 < b h)
    (hG : ∀ h, 0 ≤ G h) (hx : ∀ h, 0 ≤ x h) (hq : 0 < q) (hq' : 0 < q')
    (h1 : q = 1 / ∑ h, b h * q ^ ex γ * (1 + G h) / (1 + b h * q ^ ex γ * (1 + G h)) * x h)
    (h2 : q' = 1 / ∑ h, b h * q' ^ ex γ * (1 + G h) / (1 + b h * q' ^ ex γ * (1 + G h)) * x h) :
    q = q' := by
  have conv : ∀ p, 0 < p →
      p = 1 / ∑ h, b h * p ^ ex γ * (1 + G h) / (1 + b h * p ^ ex γ * (1 + G h)) * x h →
      Phi γ b G x p = 1 := by
    intro p hp hp1
    have hn : ∑ h, b h * p ^ ex γ * (1 + G h) / (1 + b h * p ^ ex γ * (1 + G h)) * x h ≠ 0 := by
      intro h0; rw [h0, div_zero] at hp1; linarith
    rw [eq_div_iff hn, Finset.mul_sum] at hp1
    rw [← hp1, Phi]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← qs_eq γ (b h) (G h) p hγ (hb h) (hG h) hp]
    ring
  have k1 := conv q hq h1
  have k2 := conv q' hq' h2
  have hex : ∃ h, 0 < x h := by
    by_contra hn
    push Not at hn
    have : Phi γ b G x q = 0 := Finset.sum_eq_zero fun h _ => by
      rw [le_antisymm (hn h) (hx h), mul_zero]
    linarith
  obtain ⟨h0, hh0⟩ := hex
  have mono : ∀ p p', 0 < p → p < p' → Phi γ b G x p < Phi γ b G x p' := by
    intro p p' hp hpp
    have hK : ∀ h, 0 < b h * (1 + G h) := fun h => mul_pos (hb h) (by linarith [hG h])
    refine Finset.sum_lt_sum (fun h _ => ?_) ⟨h0, Finset.mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_right (psi_lt γ _ p p' hγ (hK h) hp hpp).le (hx h)
    · exact mul_lt_mul_of_pos_right (psi_lt γ _ p p' hγ (hK h0) hp hpp) hh0
  rcases lt_trichotomy q q' with h | h | h
  · have := mono q q' hq h; linarith
  · exact h
  · have := mono q' q hq' h; linarith

/-! ## Paths -/

theorem T_const (g σ c v : ℝ) (y : H → ℝ) (hv : v ≠ 0) :
    T g σ c (fun _ => v) y = T g σ c (fun _ => 1) y := by
  funext h
  simp only [T, B]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hv]
  simp only [one_mul]

/-- **Log utility: the path is unique** for any heterogeneous patience profile. -/
theorem unique_log (g σ c : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c 1 b x0 N x Q) (hE' : IsEqN g σ c 1 b x0 N x' Q') :
    (∀ t < N, Q t = Q' t) ∧ ∀ t ≤ N, x t = x' t := by
  obtain ⟨h0, hs⟩ := hE
  obtain ⟨h0', hs'⟩ := hE'
  have hrr : rr 1 Q = rr 1 Q' := funext fun i => by simp [rr, ex]
  have hsv : ∀ t, savN 1 b N Q t = savN 1 b N Q' t := fun t => by
    funext h; simp only [savN, hrr]
  have hx : ∀ t ≤ N, x t = x' t := by
    intro t
    induction t with
    | zero => intro _; rw [h0, h0']
    | succ t ih =>
      intro ht
      rw [(hs t (by omega)).1, (hs' t (by omega)).1, ih (by omega), hsv t]
  refine ⟨fun t ht => ?_, hx⟩
  rw [(hs t ht).2, (hs' t ht).2, hsv t, hx t ht.le]

/-- The common saving rate. -/
def sc (β0 γ : ℝ) (N : ℕ) (P : ℕ → ℝ) (t : ℕ) : ℝ :=
  F β0 (rr γ P) (N - t) t / (1 + F β0 (rr γ P) (N - t) t)

theorem sc_pos (β0 γ : ℝ) (N : ℕ) (P : ℕ → ℝ) (hβ : 0 < β0) (hP : ∀ t, 0 < P t) (t : ℕ)
    (ht : t < N) : 0 < sc β0 γ N P t := by
  obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
  have hr : ∀ i, 0 ≤ rr γ P i := fun i => Real.rpow_nonneg (hP i).le _
  have hF := F_nonneg β0 hβ.le (rr γ P) hr k (t + 1)
  have hp : 0 < β0 * rr γ P t := mul_pos hβ (Real.rpow_pos_of_pos (hP t) _)
  have e : F β0 (rr γ P) (k + 1) t = β0 * rr γ P t * (1 + F β0 (rr γ P) k (t + 1)) := rfl
  have hpos : 0 < F β0 (rr γ P) (k + 1) t := by rw [e]; nlinarith
  unfold sc
  rw [hk]
  exact div_pos hpos (by linarith)

/-- **Common patience: the path is unique** for every `γ > 0`, among equilibria with positive
returns. -/
theorem unique_common (g σ c γ β0 : ℝ) (b x0 : H → ℝ) (N : ℕ) (hγ : 0 < γ) (hβ : 0 < β0)
    (hb : ∀ h, b h = β0) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ t, 0 < Q t) (hQ' : ∀ t, 0 < Q' t) :
    (∀ t < N, Q t = Q' t) ∧ ∀ t ≤ N, x t = x' t := by
  obtain ⟨h0, hs⟩ := hE
  obtain ⟨h0', hs'⟩ := hE'
  have hsv : ∀ (P : ℕ → ℝ) t, savN γ b N P t = fun _ => sc β0 γ N P t := by
    intro P t; funext h; simp only [savN, sc, hb]
  have hx : ∀ t ≤ N, x t = x' t := by
    intro t
    induction t with
    | zero => intro _; rw [h0, h0']
    | succ t ih =>
      intro ht
      rw [(hs t (by omega)).1, (hs' t (by omega)).1, ih (by omega), hsv Q t, hsv Q' t,
        T_const g σ c _ _ (sc_pos β0 γ N Q hβ hQ t (by omega)).ne',
        T_const g σ c _ _ (sc_pos β0 γ N Q' hβ hQ' t (by omega)).ne']
  have step : ∀ t < N, F β0 (rr γ Q) (N - (t + 1)) (t + 1) =
      F β0 (rr γ Q') (N - (t + 1)) (t + 1) → Q t = Q' t := by
    intro t ht hG
    have e1 := (hs t ht).2
    have e2 := (hs' t ht).2
    rw [hsv Q t, hx t ht.le] at e1
    rw [hsv Q' t] at e2
    have hk : N - t = N - (t + 1) + 1 := by omega
    have r1 : sc β0 γ N Q t = β0 * Q t ^ ex γ * (1 + F β0 (rr γ Q) (N - (t + 1)) (t + 1)) /
        (1 + β0 * Q t ^ ex γ * (1 + F β0 (rr γ Q) (N - (t + 1)) (t + 1))) := by
      unfold sc; rw [hk]; rfl
    have r2 : sc β0 γ N Q' t = β0 * Q' t ^ ex γ * (1 + F β0 (rr γ Q') (N - (t + 1)) (t + 1)) /
        (1 + β0 * Q' t ^ ex γ * (1 + F β0 (rr γ Q') (N - (t + 1)) (t + 1))) := by
      unfold sc; rw [hk]; rfl
    simp only [B] at e1 e2
    rw [← Finset.mul_sum, r1] at e1
    rw [← Finset.mul_sum, r2, ← hG] at e2
    exact date_unique_common γ β0 _ _ (Q t) (Q' t) hγ hβ
      (F_nonneg β0 hβ.le _ (fun i => Real.rpow_nonneg (hQ i).le _) _ _) (hQ t) (hQ' t) e1 e2
  have claim : ∀ k t, t + k = N → F β0 (rr γ Q) k t = F β0 (rr γ Q') k t := by
    intro k
    induction k with
    | zero => intro t _; rfl
    | succ k ih =>
      intro t ht
      have hq : Q t = Q' t := step t (by omega) (by
        rw [show N - (t + 1) = k by omega]; exact ih (t + 1) (by omega))
      show β0 * rr γ Q t * (1 + F β0 (rr γ Q) k (t + 1)) =
        β0 * rr γ Q' t * (1 + F β0 (rr γ Q') k (t + 1))
      rw [ih (t + 1) (by omega), show rr γ Q t = Q t ^ ex γ from rfl,
        show rr γ Q' t = Q' t ^ ex γ from rfl, hq]
  exact ⟨fun t ht => step t ht (claim _ _ (by omega)), hx⟩

/-- **Heterogeneous patience, any horizon, one date**: same distribution and same continuation
plans give the same return. -/
theorem date_unique_path (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (hγ : 0 < γ)
    (hb : ∀ h, 0 < b h) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ t, 0 < Q t) (hQ' : ∀ t, 0 < Q' t) (t : ℕ) (ht : t < N)
    (hxt : x t = x' t) (hxn : ∀ h, 0 ≤ x t h)
    (hG : ∀ h, F (b h) (rr γ Q) (N - (t + 1)) (t + 1) = F (b h) (rr γ Q') (N - (t + 1)) (t + 1)) :
    Q t = Q' t := by
  have e1 := (hE.2 t ht).2
  have e2 := (hE'.2 t ht).2
  rw [← hxt] at e2
  have hk : N - t = N - (t + 1) + 1 := by omega
  have r : ∀ (P : ℕ → ℝ) h, savN γ b N P t h =
      b h * P t ^ ex γ * (1 + F (b h) (rr γ P) (N - (t + 1)) (t + 1)) /
        (1 + b h * P t ^ ex γ * (1 + F (b h) (rr γ P) (N - (t + 1)) (t + 1))) := by
    intro P h; unfold savN; rw [hk]; rfl
  simp only [B, r] at e1 e2
  simp only [← hG] at e2
  exact date_unique γ (Q t) (Q' t) b (fun h => F (b h) (rr γ Q) (N - (t + 1)) (t + 1)) (x t)
    hγ hb (fun h => F_nonneg _ (hb h).le _ (fun i => Real.rpow_nonneg (hQ i).le _) _ _) hxn
    (hQ t) (hQ' t) e1 e2

/-- **Heterogeneous patience, horizon one: the equilibrium is unique.** -/
theorem unique_one_period (g σ c γ : ℝ) (b x0 : H → ℝ) (hγ : 0 < γ) (hb : ∀ h, 0 < b h)
    (hx0 : ∀ h, 0 ≤ x0 h) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 1 x Q) (hE' : IsEqN g σ c γ b x0 1 x' Q')
    (hQ : 0 < Q 0) (hQ' : 0 < Q' 0) : Q 0 = Q' 0 ∧ x 1 = x' 1 := by
  have r : ∀ (P : ℕ → ℝ) h, savN γ b 1 P 0 h =
      b h * P 0 ^ ex γ * (1 + (fun _ : H => (0:ℝ)) h) /
        (1 + b h * P 0 ^ ex γ * (1 + (fun _ : H => (0:ℝ)) h)) := fun P h => rfl
  have e1 := (hE.2 0 one_pos).2
  have e2 := (hE'.2 0 one_pos).2
  rw [hE.1] at e1
  rw [hE'.1] at e2
  simp only [B, r] at e1 e2
  have hq : Q 0 = Q' 0 := date_unique γ (Q 0) (Q' 0) b (fun _ => 0) x0 hγ hb (fun _ => le_rfl)
    hx0 hQ hQ' (by simpa using e1) (by simpa using e2)
  refine ⟨hq, ?_⟩
  have hsv : savN γ b 1 Q 0 = savN γ b 1 Q' 0 := by
    funext h; rw [r, r, hq]
  rw [(hE.2 0 one_pos).1, (hE'.2 0 one_pos).1, hE.1, hE'.1, hsv]

end PathUniqueness

end

#print axioms PathUniqueness.qs_eq
#print axioms PathUniqueness.date_unique_common
#print axioms PathUniqueness.date_unique
#print axioms PathUniqueness.unique_log
#print axioms PathUniqueness.unique_common
#print axioms PathUniqueness.date_unique_path
#print axioms PathUniqueness.unique_one_period
