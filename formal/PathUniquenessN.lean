import Mathlib

/-!
# Stage 378: a unique path at every finite horizon, heterogeneous patience, `γ` near one

Stage 373 proved uniqueness of the stage 364 equilibrium path with heterogeneous patience and
`γ ≠ 1` for horizon two. This file proves it for every finite horizon `N`, under a band on `γ`
that narrows with `N`. The stage 364 definitions are restated unchanged (`B`, `amp`, `T`, `F`,
`ex`, `rr`, `savN`, `IsEqN`).

The argument is a ratio contraction, not the date-by-date comparison of stage 373. Let `L ≥ 1`
be the largest ratio `max (Q' t / Q t) (Q t / Q' t)` between two equilibria over the dates
`t < N`, and let `e ≥ |ex γ| = |1 / γ − 1|`, `ε = e N`.

* `F_ratio`, `sav_ratio`: returns within a factor `L` move every saving rate by at most `L ^ ε`
  (the annuity sum `F` changes by at most `(L ^ e) ^ (N − t)`, and `F / (1 + F)` by no more).
* `date_step`: if the date-`t` holdings of the two paths are within `β`, then date-`t`
  clearing puts the returns within `L ^ ε β` and the date-`t + 1` holdings within
  `(L ^ ε β) ^ 2`.
* `propagate`: holdings at date `t` are within `L ^ ((2 ^ (t + 1) − 2) ε)`, so returns at date
  `t < N` are within `L ^ ((2 ^ N − 1) ε)`.
* **`unique_N`**: two equilibria with positive returns at every date `t < N` have equal returns
  at those dates and equal distributions at every date `t ≤ N`, if
  `(2 ^ N − 1) e N < 1` for some `e ≥ |ex γ|`, with `b ≥ 0`, `x0 ≥ 0`, `g ≥ 0`, `amp ≥ 0`,
  `g σ c ≥ 0`. (The largest ratio `L` is then at most `L ^ κ` with `κ < 1`, so `L = 1`.)
* **`unique_N_band`**: the same with `γ > 0` and `|1 / γ − 1| N (2 ^ N − 1) < 1`.
* `unique_three_period`: horizon three under `|1 / γ − 1| < 1 / 21`.

Limits. The band is a sufficient condition from crude bounds, not a sharp one. It shrinks
roughly like `2 ^ (−N) / N`, so it gives no uniform statement in `N` and none for the
infinite horizon, which is not covered. At horizon two it (`|1 / γ − 1| < 1 / 6`) is narrower
than the stage 373 band `1 / 2 < γ ^ 2 < 2`; this file does not supersede stage 373 there.
Outside the band uniqueness is neither proved nor refuted, and no example of two distinct
equilibrium paths is given. Uniqueness is among equilibria with positive returns at every
date `t < N`; existence is not addressed here.
-/

noncomputable section

open Finset BigOperators

namespace PathUniquenessN

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

/-! ## Saving rates move little when returns move little -/

theorem F_nonneg (b : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) :
    ∀ k t, (∀ j, t ≤ j → j < t + k → 0 ≤ r j) → 0 ≤ F b r k t := by
  intro k
  induction k with
  | zero => intro t _; show (0:ℝ) ≤ 0; exact le_rfl
  | succ k ih =>
    intro t hr
    have h1 : 0 ≤ r t := hr t le_rfl (by omega)
    have h2 : 0 ≤ F b r k (t + 1) := ih (t + 1) fun j hj hj' => hr j (by omega) (by omega)
    show 0 ≤ b * r t * (1 + F b r k (t + 1))
    exact mul_nonneg (mul_nonneg hb h1) (by linarith)

theorem F_ratio (b ν : ℝ) (r r' : ℕ → ℝ) (hb : 0 ≤ b) (hν : 1 ≤ ν) :
    ∀ k t, (∀ j, t ≤ j → j < t + k → 0 ≤ r j ∧ 0 ≤ r' j ∧ r' j ≤ ν * r j) →
      F b r' k t ≤ ν ^ k * F b r k t := by
  intro k
  induction k with
  | zero => intro t _; show (0:ℝ) ≤ ν ^ 0 * 0; simp
  | succ k ih =>
    intro t hr
    obtain ⟨h0, -, h1⟩ := hr t le_rfl (by omega)
    have hw : ∀ j, t + 1 ≤ j → j < t + 1 + k → 0 ≤ r j ∧ 0 ≤ r' j ∧ r' j ≤ ν * r j :=
      fun j hj hj' => hr j (by omega) (by omega)
    have h2 := ih (t + 1) hw
    have hF' : 0 ≤ F b r' k (t + 1) :=
      F_nonneg b r' hb k (t + 1) fun j hj hj' => (hw j hj hj').2.1
    have hνk : 1 ≤ ν ^ k := one_le_pow₀ hν
    show b * r' t * (1 + F b r' k (t + 1)) ≤ ν ^ (k + 1) * (b * r t * (1 + F b r k (t + 1)))
    have e1 : 1 + F b r' k (t + 1) ≤ ν ^ k * (1 + F b r k (t + 1)) := by
      rw [mul_add, mul_one]; linarith
    have e2 : b * r' t ≤ ν * (b * r t) := by
      have := mul_le_mul_of_nonneg_left h1 hb; linarith
    calc b * r' t * (1 + F b r' k (t + 1))
        ≤ (ν * (b * r t)) * (ν ^ k * (1 + F b r k (t + 1))) :=
          mul_le_mul e2 e1 (by linarith) (mul_nonneg (by linarith) (mul_nonneg hb h0))
      _ = ν ^ (k + 1) * (b * r t * (1 + F b r k (t + 1))) := by ring

theorem rpow_ratio (q q' L a e : ℝ) (hq : 0 < q) (hq' : 0 < q') (hL : 1 ≤ L)
    (h1 : q' ≤ L * q) (h2 : q ≤ L * q') (hae : a ≤ e) (hae' : -e ≤ a) :
    q' ^ a ≤ L ^ e * q ^ a := by
  have hL0 : 0 < L := by linarith
  rcases le_total 0 a with ha | ha
  · calc q' ^ a ≤ (L * q) ^ a := Real.rpow_le_rpow hq'.le h1 ha
      _ = L ^ a * q ^ a := Real.mul_rpow hL0.le hq.le
      _ ≤ L ^ e * q ^ a := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hL hae) (Real.rpow_nonneg hq.le _)
  · have k1 : (L * q') ^ a ≤ q ^ a := Real.rpow_le_rpow_of_nonpos hq h2 ha
    have hLa : 0 < L ^ a := Real.rpow_pos_of_pos hL0 a
    calc q' ^ a = (L ^ a)⁻¹ * (L ^ a * q' ^ a) := by
          rw [← mul_assoc, inv_mul_cancel₀ hLa.ne', one_mul]
      _ ≤ (L ^ a)⁻¹ * q ^ a := mul_le_mul_of_nonneg_left
          (by rw [← Real.mul_rpow hL0.le hq'.le]; exact k1) (inv_nonneg.2 hLa.le)
      _ = L ^ (-a) * q ^ a := by rw [Real.rpow_neg hL0.le]
      _ ≤ L ^ e * q ^ a := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (Real.rpow_nonneg hq.le _)

theorem frac_ratio (c F F' : ℝ) (hF : 0 ≤ F) (hF' : 0 ≤ F') (hc : 1 ≤ c) (h : F' ≤ c * F) :
    F' / (1 + F') ≤ c * (F / (1 + F)) := by
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (mul_nonneg hF hF')]

omit [Fintype H] in
theorem savN_nonneg (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (t : ℕ) (h : H) (hb : 0 ≤ b h)
    (hQ : ∀ j < N, 0 < Q j) : 0 ≤ savN γ b N Q t h := by
  have := F_nonneg (b h) (rr γ Q) hb (N - t) t fun j _ hj =>
    Real.rpow_nonneg (hQ j (by omega)).le _
  unfold savN
  exact div_nonneg this (by linarith)

omit [Fintype H] in
/-- **Saving rates within `L ^ (e N)`** when all returns before `N` are within `L`. -/
theorem sav_ratio (γ e L : ℝ) (b : H → ℝ) (N : ℕ) (Q Q' : ℕ → ℝ) (t : ℕ) (h : H)
    (hb : 0 ≤ b h) (hL : 1 ≤ L) (he : 0 ≤ e) (hxe : ex γ ≤ e) (hxe' : -e ≤ ex γ)
    (hQ : ∀ j < N, 0 < Q j) (hQ' : ∀ j < N, 0 < Q' j)
    (h1 : ∀ j < N, Q' j ≤ L * Q j) (h2 : ∀ j < N, Q j ≤ L * Q' j) :
    savN γ b N Q' t h ≤ L ^ (e * N) * savN γ b N Q t h := by
  have hν : 1 ≤ L ^ e := Real.one_le_rpow hL he
  have hw : ∀ j, t ≤ j → j < t + (N - t) →
      0 ≤ rr γ Q j ∧ 0 ≤ rr γ Q' j ∧ rr γ Q' j ≤ L ^ e * rr γ Q j := by
    intro j _ hj
    have hjN : j < N := by omega
    exact ⟨Real.rpow_nonneg (hQ j hjN).le _, Real.rpow_nonneg (hQ' j hjN).le _,
      rpow_ratio _ _ _ _ _ (hQ j hjN) (hQ' j hjN) hL (h1 j hjN) (h2 j hjN) hxe hxe'⟩
  have hF := F_ratio (b h) (L ^ e) (rr γ Q) (rr γ Q') hb hν (N - t) t hw
  have hF0 : 0 ≤ F (b h) (rr γ Q) (N - t) t :=
    F_nonneg _ _ hb _ _ fun j a c => (hw j a c).1
  have hF0' : 0 ≤ F (b h) (rr γ Q') (N - t) t :=
    F_nonneg _ _ hb _ _ fun j a c => (hw j a c).2.1
  have hpow : (L ^ e) ^ (N - t) ≤ L ^ (e * N) := by
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
    exact pow_le_pow_right₀ hν (Nat.sub_le N t)
  have hc : F (b h) (rr γ Q') (N - t) t ≤ L ^ (e * N) * F (b h) (rr γ Q) (N - t) t :=
    le_trans hF (mul_le_mul_of_nonneg_right hpow hF0)
  have hc1 : 1 ≤ L ^ (e * N) := Real.one_le_rpow hL (mul_nonneg he (Nat.cast_nonneg N))
  unfold savN
  exact frac_ratio _ _ _ hF0 hF0' hc1 hc

/-! ## One date of clearing -/

theorem clear (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (t : ℕ) (ht : t < N) (hQ : 0 < Q t) :
    Q t * ∑ h, savN γ b N Q t h * x t h = 1 ∧
    ∀ h, x (t + 1) h =
      (amp g σ * (Q t * savN γ b N Q t h * x t h) + g * σ * c) / (1 + g) := by
  obtain ⟨hx, eq⟩ := hE.2 t ht
  have hB : B (savN γ b N Q t) (x t) ≠ 0 := by
    intro hz; rw [hz, div_zero] at eq; linarith
  have k : Q t * B (savN γ b N Q t) (x t) = 1 := by rw [eq]; field_simp
  refine ⟨k, fun h => ?_⟩
  rw [hx, T, eq]
  ring

theorem x_nonneg (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (hQ : ∀ j < N, 0 < Q j) (hb : ∀ h, 0 ≤ b h)
    (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ) (hK : 0 ≤ g * σ * c) :
    ∀ t ≤ N, ∀ h, 0 ≤ x t h := by
  intro t
  induction t with
  | zero => intro _ h; rw [hE.1]; exact hx0 h
  | succ t ih =>
    intro ht h
    have htN : t < N := by omega
    rw [(clear g σ c γ b x0 N x Q hE t htN (hQ t htN)).2 h]
    have hz : 0 ≤ Q t * savN γ b N Q t h * x t h :=
      mul_nonneg (mul_nonneg (hQ t htN).le (savN_nonneg γ b N Q t h (hb h) hQ)) (ih (by omega) h)
    exact div_nonneg (add_nonneg (mul_nonneg hA hz) hK) (by linarith)

theorem sum_ratio (s x s' x' : H → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hs' : ∀ h, 0 ≤ s' h)
    (hx : ∀ h, 0 ≤ x h) (h1 : ∀ h, s h ≤ α * s' h) (h2 : ∀ h, x h ≤ β * x' h) :
    ∑ h, s h * x h ≤ α * β * ∑ h, s' h * x' h := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h _ => ?_
  calc s h * x h ≤ (α * s' h) * (β * x' h) :=
        mul_le_mul (h1 h) (h2 h) (hx h) (mul_nonneg hα (hs' h))
    _ = α * β * (s' h * x' h) := by ring

theorem q_ratio (q q' S S' c : ℝ) (hq : 0 < q) (hq' : 0 < q') (hS : q * S = 1)
    (hS' : q' * S' = 1) (h : S ≤ c * S') : q' ≤ c * q := by
  calc q' = q' * (q * S) := by rw [hS, mul_one]
    _ ≤ q' * (q * (c * S')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hq.le) hq'.le
    _ = c * q * (q' * S') := by ring
    _ = c * q := by rw [hS', mul_one]

theorem prod3 (a b c a' b' c' p1 p2 p3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 0 ≤ p1)
    (hp2 : 0 ≤ p2) (hb' : 0 ≤ b') (hc' : 0 ≤ c')
    (h1 : a' ≤ p1 * a) (h2 : b' ≤ p2 * b) (h3 : c' ≤ p3 * c) :
    a' * b' * c' ≤ p1 * p2 * p3 * (a * b * c) := by
  calc a' * b' * c' ≤ (p1 * a) * (p2 * b) * (p3 * c) :=
        mul_le_mul (mul_le_mul h1 h2 hb' (mul_nonneg hp1 ha)) h3 hc'
          (mul_nonneg (mul_nonneg hp1 ha) (mul_nonneg hp2 hb))
    _ = p1 * p2 * p3 * (a * b * c) := by ring

theorem upd (A K g z z' c : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hg : 0 ≤ g) (hc : 1 ≤ c)
    (h : z' ≤ c * z) : (A * z' + K) / (1 + g) ≤ c * ((A * z + K) / (1 + g)) := by
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h hA, mul_nonneg (sub_nonneg.2 hc) hK]

theorem step (q q' A K g α β : ℝ) (s x s' x' y y' : H → ℝ)
    (hq : 0 < q) (hq' : 0 < q') (hα : 1 ≤ α) (hβ : 1 ≤ β) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hg : 0 ≤ g) (hs : ∀ h, 0 ≤ s h) (hs' : ∀ h, 0 ≤ s' h) (hx : ∀ h, 0 ≤ x h)
    (hx' : ∀ h, 0 ≤ x' h)
    (hs1 : ∀ h, s h ≤ α * s' h) (hs2 : ∀ h, s' h ≤ α * s h)
    (hx1 : ∀ h, x h ≤ β * x' h) (hx2 : ∀ h, x' h ≤ β * x h)
    (e : q * ∑ h, s h * x h = 1) (e' : q' * ∑ h, s' h * x' h = 1)
    (hy : ∀ h, y h = (A * (q * s h * x h) + K) / (1 + g))
    (hy' : ∀ h, y' h = (A * (q' * s' h * x' h) + K) / (1 + g)) :
    q' ≤ α * β * q ∧ ∀ h, y' h ≤ α * β * α * β * y h := by
  have hqb : q' ≤ α * β * q :=
    q_ratio q q' _ _ _ hq hq' e e' (sum_ratio s x s' x' α β (by linarith) hs' hx hs1 hx1)
  refine ⟨hqb, fun h => ?_⟩
  have hab : 1 ≤ α * β := one_le_mul_of_one_le_of_one_le hα hβ
  have hc : 1 ≤ α * β * α * β :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hab hα) hβ
  rw [hy, hy']
  exact upd A K g _ _ _ hA hK hg hc
    (prod3 q (s h) (x h) q' (s' h) (x' h) (α * β) α β hq.le (hs h) (by linarith) (by linarith)
      (hs' h) (hx' h) hqb (hs2 h) (hx2 h))

/-- **One date of the comparison.** Holdings within `β` at date `t` give returns within
`L ^ (e N) β` at date `t` and holdings within `(L ^ (e N) β) ^ 2` at date `t + 1`. -/
theorem date_step (g σ c γ e L β : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hQ' : ∀ j < N, 0 < Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (he : 0 ≤ e) (hxe : ex γ ≤ e) (hxe' : -e ≤ ex γ) (hL : 1 ≤ L)
    (hβ : 1 ≤ β) (h1 : ∀ j < N, Q' j ≤ L * Q j) (h2 : ∀ j < N, Q j ≤ L * Q' j)
    (t : ℕ) (ht : t < N) (hx1 : ∀ h, x t h ≤ β * x' t h) (hx2 : ∀ h, x' t h ≤ β * x t h) :
    Q' t ≤ L ^ (e * N) * β * Q t ∧
      ∀ h, x' (t + 1) h ≤ L ^ (e * N) * β * L ^ (e * N) * β * x (t + 1) h := by
  have hα : 1 ≤ L ^ (e * N) := Real.one_le_rpow hL (mul_nonneg he (Nat.cast_nonneg N))
  obtain ⟨c1, u1⟩ := clear g σ c γ b x0 N x Q hE t ht (hQ t ht)
  obtain ⟨c2, u2⟩ := clear g σ c γ b x0 N x' Q' hE' t ht (hQ' t ht)
  exact step (Q t) (Q' t) (amp g σ) (g * σ * c) g _ β (savN γ b N Q t) (x t)
    (savN γ b N Q' t) (x' t) (x (t + 1)) (x' (t + 1)) (hQ t ht) (hQ' t ht) hα hβ hA hK hg
    (fun h => savN_nonneg γ b N Q t h (hb h) hQ) (fun h => savN_nonneg γ b N Q' t h (hb h) hQ')
    (fun h => x_nonneg g σ c γ b x0 N x Q hE hQ hb hx0 hg hA hK t ht.le h)
    (fun h => x_nonneg g σ c γ b x0 N x' Q' hE' hQ' hb hx0 hg hA hK t ht.le h)
    (fun h => sav_ratio γ e L b N Q' Q t h (hb h) hL he hxe hxe' hQ' hQ h2 h1)
    (fun h => sav_ratio γ e L b N Q Q' t h (hb h) hL he hxe hxe' hQ hQ' h1 h2)
    hx1 hx2 c1 c2 u1 u2

/-- **Holdings at date `t` are within `L ^ ((2 ^ (t + 1) − 2) e N)`.** -/
theorem propagate (g σ c γ e L : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hQ' : ∀ j < N, 0 < Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (he : 0 ≤ e) (hxe : ex γ ≤ e) (hxe' : -e ≤ ex γ) (hL : 1 ≤ L)
    (h1 : ∀ j < N, Q' j ≤ L * Q j) (h2 : ∀ j < N, Q j ≤ L * Q' j) :
    ∀ t ≤ N, ∀ h, x' t h ≤ L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) * x t h ∧
      x t h ≤ L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) * x' t h := by
  have hL0 : 0 < L := by linarith
  intro t
  induction t with
  | zero =>
    intro _ h
    have h0 : ((2:ℝ) ^ (0 + 1) - 2) * (e * N) = 0 := by norm_num
    rw [h0, Real.rpow_zero, hE.1, hE'.1, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  | succ t ih =>
    intro ht h
    have htN : t < N := by omega
    have h2t : (2:ℝ) ≤ 2 ^ (t + 1) := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (t + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hβ : 1 ≤ L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) :=
      Real.one_le_rpow hL (mul_nonneg (by linarith) (mul_nonneg he (Nat.cast_nonneg N)))
    obtain ⟨-, k1⟩ := date_step g σ c γ e L _ b x0 N x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK
      he hxe hxe' hL hβ h1 h2 t htN (fun h => (ih htN.le h).2) (fun h => (ih htN.le h).1)
    obtain ⟨-, k2⟩ := date_step g σ c γ e L _ b x0 N x' x Q' Q hE' hE hQ' hQ hb hx0 hg hA hK
      he hxe hxe' hL hβ h2 h1 t htN (fun h => (ih htN.le h).1) (fun h => (ih htN.le h).2)
    have hpow : L ^ (e * N) * L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) * L ^ (e * N) *
        L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) =
        L ^ (((2:ℝ) ^ (t + 1 + 1) - 2) * (e * N)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      ring
    rw [← hpow]
    exact ⟨k1 h, k2 h⟩

/-! ## Uniqueness at every finite horizon -/

/-- **Unique path at horizon `N`.** Two equilibria with positive returns before `N` coincide,
when `(2 ^ N − 1) e N < 1` for some `e ≥ |ex γ|`. -/
theorem unique_N (g σ c γ e : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hQ' : ∀ j < N, 0 < Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (he : 0 ≤ e) (hxe : ex γ ≤ e) (hxe' : -e ≤ ex γ)
    (hband : ((2:ℝ) ^ N - 1) * (e * N) < 1) :
    (∀ t < N, Q' t = Q t) ∧ ∀ t ≤ N, x' t = x t := by
  have hQeq : ∀ j < N, Q' j = Q j := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · intro j hj; omega
    obtain ⟨t0, ht0m, hmax⟩ := Finset.exists_max_image (Finset.range N)
      (fun t => max (Q' t / Q t) (Q t / Q' t)) ⟨0, Finset.mem_range.2 hN⟩
    set L := max (Q' t0 / Q t0) (Q t0 / Q' t0) with hLd
    have h1 : ∀ j < N, Q' j ≤ L * Q j := by
      intro j hj
      have := le_trans (le_max_left _ _) (hmax j (Finset.mem_range.2 hj))
      rwa [div_le_iff₀ (hQ j hj)] at this
    have h2 : ∀ j < N, Q j ≤ L * Q' j := by
      intro j hj
      have := le_trans (le_max_right _ _) (hmax j (Finset.mem_range.2 hj))
      rwa [div_le_iff₀ (hQ' j hj)] at this
    have ht0 : t0 < N := Finset.mem_range.1 ht0m
    have hL : 1 ≤ L := by
      rcases le_total (Q t0) (Q' t0) with h | h
      · exact le_max_of_le_left ((one_le_div (hQ t0 ht0)).2 h)
      · exact le_max_of_le_right ((one_le_div (hQ' t0 ht0)).2 h)
    set κ := ((2:ℝ) ^ N - 1) * (e * N) with hκd
    have hx := propagate g σ c γ e L b x0 N x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK he hxe
      hxe' hL h1 h2
    have hκ : ∀ t < N, Q' t ≤ L ^ κ * Q t ∧ Q t ≤ L ^ κ * Q' t := by
      intro t ht
      have h2t : (2:ℝ) ≤ 2 ^ (t + 1) := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (t + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2N : (2:ℝ) ^ (t + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
      have heN : 0 ≤ e * N := mul_nonneg he (Nat.cast_nonneg N)
      have hβ : 1 ≤ L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) :=
        Real.one_le_rpow hL (mul_nonneg (by linarith) heN)
      obtain ⟨k1, -⟩ := date_step g σ c γ e L _ b x0 N x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK
        he hxe hxe' hL hβ h1 h2 t ht (fun h => (hx t ht.le h).2) (fun h => (hx t ht.le h).1)
      obtain ⟨k2, -⟩ := date_step g σ c γ e L _ b x0 N x' x Q' Q hE' hE hQ' hQ hb hx0 hg hA hK
        he hxe hxe' hL hβ h2 h1 t ht (fun h => (hx t ht.le h).1) (fun h => (hx t ht.le h).2)
      have hmono : L ^ (e * N) * L ^ (((2:ℝ) ^ (t + 1) - 2) * (e * N)) ≤ L ^ κ := by
        rw [← Real.rpow_add (by linarith)]
        apply Real.rpow_le_rpow_of_exponent_le hL
        rw [hκd]
        nlinarith [mul_nonneg (sub_nonneg.2 h2N) heN]
      exact ⟨le_trans k1 (mul_le_mul_of_nonneg_right hmono (hQ t ht).le),
        le_trans k2 (mul_le_mul_of_nonneg_right hmono (hQ' t ht).le)⟩
    have hL1 : L = 1 := by
      by_contra hne
      have hgt : 1 < L := lt_of_le_of_ne hL (Ne.symm hne)
      have hle : L ≤ L ^ κ := by
        obtain ⟨k1, k2⟩ := hκ t0 ht0
        rw [hLd]
        exact max_le ((div_le_iff₀ (hQ t0 ht0)).2 k1) ((div_le_iff₀ (hQ' t0 ht0)).2 k2)
      have hlt : L ^ κ < L ^ (1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hgt hband
      rw [Real.rpow_one] at hlt
      linarith
    intro j hj
    obtain ⟨k1, k2⟩ := hκ j hj
    rw [hL1, Real.one_rpow, one_mul] at k1 k2
    exact le_antisymm k1 k2
  refine ⟨hQeq, ?_⟩
  have hx := propagate g σ c γ e 1 b x0 N x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK he hxe hxe'
    le_rfl (fun j hj => by rw [one_mul, hQeq j hj]) (fun j hj => by rw [one_mul, hQeq j hj])
  intro t ht
  funext h
  obtain ⟨k1, k2⟩ := hx t ht h
  rw [Real.one_rpow, one_mul] at k1 k2
  exact le_antisymm k1 k2

/-- **Unique path at horizon `N`, band form:** `γ > 0` and `|1 / γ − 1| N (2 ^ N − 1) < 1`. -/
theorem unique_N_band (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hQ' : ∀ j < N, 0 < Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (hγ : 0 < γ) (hband : |1 / γ - 1| * N * ((2:ℝ) ^ N - 1) < 1) :
    (∀ t < N, Q' t = Q t) ∧ ∀ t ≤ N, x' t = x t := by
  have hex : ex γ = 1 / γ - 1 := by rw [ex, sub_div, div_self hγ.ne']
  exact unique_N g σ c γ |1 / γ - 1| b x0 N x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK
    (abs_nonneg _) (by rw [hex]; exact le_abs_self _) (by rw [hex]; exact neg_abs_le _)
    (by linarith)

/-- **Unique three-period path** for `|1 / γ − 1| < 1 / 21`. -/
theorem unique_three_period (g σ c γ : ℝ) (b x0 : H → ℝ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 3 x Q) (hE' : IsEqN g σ c γ b x0 3 x' Q')
    (hQ : ∀ j < 3, 0 < Q j) (hQ' : ∀ j < 3, 0 < Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (hγ : 0 < γ) (hband : |1 / γ - 1| < 1 / 21) :
    (∀ t < 3, Q' t = Q t) ∧ ∀ t ≤ 3, x' t = x t :=
  unique_N_band g σ c γ b x0 3 x x' Q Q' hE hE' hQ hQ' hb hx0 hg hA hK hγ (by
    have e : |1 / γ - 1| * ((3:ℕ):ℝ) * ((2:ℝ) ^ 3 - 1) = 21 * |1 / γ - 1| := by push_cast; ring
    rw [e]; linarith)

end PathUniquenessN

#print axioms PathUniquenessN.F_ratio
#print axioms PathUniquenessN.rpow_ratio
#print axioms PathUniquenessN.sav_ratio
#print axioms PathUniquenessN.clear
#print axioms PathUniquenessN.x_nonneg
#print axioms PathUniquenessN.step
#print axioms PathUniquenessN.date_step
#print axioms PathUniquenessN.propagate
#print axioms PathUniquenessN.unique_N
#print axioms PathUniquenessN.unique_N_band
#print axioms PathUniquenessN.unique_three_period
