import Mathlib

/-!
# Stage 383: gross substitutes and the equilibrium path at every finite horizon

Stages 370, 373 and 378 proved uniqueness of the stage 364 equilibrium path in special cases:
log utility, common patience, horizon one, horizon two under a band on `γ`, and every finite
horizon under a band that narrows with the horizon. This file uses the sign of the saving
response for `0 < γ ≤ 1` instead of a band. The stage 364 definitions are restated unchanged
(`B`, `amp`, `T`, `F`, `ex`, `rr`, `savN`, `IsEqN`).

* `F_mono`, `savN_mono`: for `0 < γ ≤ 1` (so `ex γ ≥ 0`) and `b ≥ 0`, a household's saving
  rate at any date is non-decreasing in the returns of that date and of every later date
  (gross substitutes across dates). `ex_nonneg` records `0 ≤ ex γ` for `0 < γ ≤ 1`.
* `date_eq`: at a date where the two paths have the same nonnegative holdings, where the
  returns are ordered `Q t ≤ Q' t` and every saving rate is ordered the same way, clearing
  forces equal returns and equal holdings at the next date.
* **`ordered_unique`**: for `0 < γ ≤ 1`, every horizon `N`, heterogeneous patience `b ≥ 0`,
  `x0 ≥ 0`, `g ≥ 0`, `amp ≥ 0`, `g σ c ≥ 0`: two equilibria whose returns are positive and
  ordered (`Q t ≤ Q' t` for every `t < N`) have the same returns at every `t < N` and the same
  distributions at every `t ≤ N`. No band condition is needed.
* **`no_higher_path`**: equivalently, no equilibrium path has returns weakly above another's at
  every date and strictly above at some date.
* **`unique_log`**: for `γ = 1` (log utility) two equilibria coincide at every horizon with no
  further condition: saving rates do not depend on returns, so the path is determined forward.

Limits. The full statement aimed at, that any two equilibria with positive returns coincide
for `0 < γ ≤ 1` with no ordering assumption, is not proved here. The order argument compares
the two paths at one date at a time and needs the returns of one path to lie weakly above the
other's at every date. A max-ratio argument across dates was considered and not completed:
when returns rise at some dates and fall at others, the change in saving rates and the induced
redistribution of holdings have no sign that the argument can use. So for unordered pairs of
equilibria with `γ ≠ 1`, uniqueness at horizon above one rests on the band conditions of
stages 373 and 378. The case `γ > 1` (`ex γ < 0`, saving falling in returns) is not covered by
any result in this file. Uniqueness is among equilibria with positive returns at every date
`t < N`; existence is not addressed. The infinite horizon is not covered.
-/

noncomputable section

open Finset BigOperators

namespace PathUniquenessGS

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

/-! ## Saving is non-decreasing in returns when `γ ≤ 1` -/

theorem ex_nonneg (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) : 0 ≤ ex γ :=
  div_nonneg (by linarith) hγ.le

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

theorem F_mono (b : ℝ) (r r' : ℕ → ℝ) (hb : 0 ≤ b) :
    ∀ k t, (∀ j, t ≤ j → j < t + k → 0 ≤ r j ∧ r j ≤ r' j) → F b r k t ≤ F b r' k t := by
  intro k
  induction k with
  | zero => intro t _; show (0:ℝ) ≤ 0; exact le_rfl
  | succ k ih =>
    intro t hr
    obtain ⟨h0, h1⟩ := hr t le_rfl (by omega)
    have hw : ∀ j, t + 1 ≤ j → j < t + 1 + k → 0 ≤ r j ∧ r j ≤ r' j :=
      fun j hj hj' => hr j (by omega) (by omega)
    have h2 := ih (t + 1) hw
    have hF : 0 ≤ F b r k (t + 1) := F_nonneg b r hb k (t + 1) fun j a c => (hw j a c).1
    show b * r t * (1 + F b r k (t + 1)) ≤ b * r' t * (1 + F b r' k (t + 1))
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hb) (by linarith) (by linarith)
      (mul_nonneg hb (by linarith))

omit [Fintype H] in
/-- **Gross substitutes:** for `ex γ ≥ 0` the saving rate is non-decreasing in returns. -/
theorem savN_mono (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q Q' : ℕ → ℝ) (t : ℕ) (h : H) (hb : 0 ≤ b h)
    (hex : 0 ≤ ex γ) (hQ : ∀ j < N, 0 < Q j) (hle : ∀ j < N, Q j ≤ Q' j) :
    savN γ b N Q t h ≤ savN γ b N Q' t h := by
  have hw : ∀ j, t ≤ j → j < t + (N - t) → 0 ≤ rr γ Q j ∧ rr γ Q j ≤ rr γ Q' j := by
    intro j _ hj
    have hjN : j < N := by omega
    exact ⟨Real.rpow_nonneg (hQ j hjN).le _, Real.rpow_le_rpow (hQ j hjN).le (hle j hjN) hex⟩
  have hF := F_mono (b h) (rr γ Q) (rr γ Q') hb (N - t) t hw
  have hF0 : 0 ≤ F (b h) (rr γ Q) (N - t) t := F_nonneg _ _ hb _ _ fun j a c => (hw j a c).1
  unfold savN
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

omit [Fintype H] in
theorem savN_nonneg (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (t : ℕ) (h : H) (hb : 0 ≤ b h)
    (hQ : ∀ j < N, 0 < Q j) : 0 ≤ savN γ b N Q t h := by
  have := F_nonneg (b h) (rr γ Q) hb (N - t) t fun j _ hj =>
    Real.rpow_nonneg (hQ j (by omega)).le _
  unfold savN
  exact div_nonneg this (by linarith)

/-! ## Holdings stay nonnegative -/

theorem clear (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (t : ℕ) (ht : t < N) (hQ : 0 < Q t) :
    ∀ h, x (t + 1) h =
      (amp g σ * (Q t * savN γ b N Q t h * x t h) + g * σ * c) / (1 + g) := by
  obtain ⟨hx, eq⟩ := hE.2 t ht
  have hB : B (savN γ b N Q t) (x t) ≠ 0 := by
    intro hz; rw [hz, div_zero] at eq; linarith
  intro h
  rw [hx, T, eq]
  field_simp

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
    rw [clear g σ c γ b x0 N x Q hE t htN (hQ t htN) h]
    have hz : 0 ≤ Q t * savN γ b N Q t h * x t h :=
      mul_nonneg (mul_nonneg (hQ t htN).le (savN_nonneg γ b N Q t h (hb h) hQ)) (ih (by omega) h)
    exact div_nonneg (add_nonneg (mul_nonneg hA hz) hK) (by linarith)

/-! ## One date: ordered returns and ordered saving force equality -/

theorem date_eq (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q') (t : ℕ) (ht : t < N)
    (hxt : x' t = x t) (hxn : ∀ h, 0 ≤ x t h)
    (hs : ∀ h, savN γ b N Q t h ≤ savN γ b N Q' t h) (hQt : 0 < Q t) (hle : Q t ≤ Q' t) :
    Q' t = Q t ∧ x' (t + 1) = x (t + 1) := by
  obtain ⟨e1, q1⟩ := hE.2 t ht
  obtain ⟨e1', q1'⟩ := hE'.2 t ht
  rw [hxt] at e1' q1'
  have hB0 : 0 < B (savN γ b N Q t) (x t) := by
    rw [q1] at hQt; exact one_div_pos.mp hQt
  have hle' : ∀ h ∈ (Finset.univ : Finset H),
      savN γ b N Q t h * x t h ≤ savN γ b N Q' t h * x t h :=
    fun h _ => mul_le_mul_of_nonneg_right (hs h) (hxn h)
  have hB01 : B (savN γ b N Q t) (x t) ≤ B (savN γ b N Q' t) (x t) := Finset.sum_le_sum hle'
  have hB1 : 0 < B (savN γ b N Q' t) (x t) := lt_of_lt_of_le hB0 hB01
  have hB10 : B (savN γ b N Q' t) (x t) ≤ B (savN γ b N Q t) (x t) := by
    rw [q1, q1'] at hle; exact (one_div_le_one_div hB0 hB1).1 hle
  have hB : B (savN γ b N Q' t) (x t) = B (savN γ b N Q t) (x t) := le_antisymm hB10 hB01
  have hsum : ∑ k, savN γ b N Q t k * x t k = ∑ k, savN γ b N Q' t k * x t k := hB.symm
  have hterm : ∀ h, savN γ b N Q' t h * x t h = savN γ b N Q t h * x t h := fun h =>
    ((Finset.sum_eq_sum_iff_of_le hle').1 hsum h (Finset.mem_univ h)).symm
  refine ⟨by rw [q1', q1, hB], ?_⟩
  rw [e1', e1]
  funext h
  simp only [T]
  rw [hterm h, hB]

/-! ## Every horizon -/

/-- **Ordered equilibria coincide** at every horizon for `0 < γ ≤ 1`. -/
theorem ordered_unique (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hle : ∀ j < N, Q j ≤ Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∀ t < N, Q' t = Q t) ∧ ∀ t ≤ N, x' t = x t := by
  have hex := ex_nonneg γ hγ hγ1
  have hxn := x_nonneg g σ c γ b x0 N x Q hE hQ hb hx0 hg hA hK
  have hs : ∀ t h, savN γ b N Q t h ≤ savN γ b N Q' t h :=
    fun t h => savN_mono γ b N Q Q' t h (hb h) hex hQ hle
  have hx : ∀ t ≤ N, x' t = x t := by
    intro t
    induction t with
    | zero => intro _; rw [hE.1, hE'.1]
    | succ t ih =>
      intro ht
      exact (date_eq g σ c γ b x0 N x x' Q Q' hE hE' t (by omega) (ih (by omega))
        (hxn t (by omega)) (hs t) (hQ t (by omega)) (hle t (by omega))).2
  exact ⟨fun t ht => (date_eq g σ c γ b x0 N x x' Q Q' hE hE' t ht (hx t ht.le)
    (hxn t ht.le) (hs t) (hQ t ht) (hle t ht)).1, hx⟩

/-- **No equilibrium path lies weakly above another and strictly above somewhere.** -/
theorem no_higher_path (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ)
    (Q Q' : ℕ → ℝ) (hE : IsEqN g σ c γ b x0 N x Q) (hE' : IsEqN g σ c γ b x0 N x' Q')
    (hQ : ∀ j < N, 0 < Q j) (hle : ∀ j < N, Q j ≤ Q' j)
    (hb : ∀ h, 0 ≤ b h) (hx0 : ∀ h, 0 ≤ x0 h) (hg : 0 ≤ g) (hA : 0 ≤ amp g σ)
    (hK : 0 ≤ g * σ * c) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ¬ ∃ t < N, Q t < Q' t := by
  rintro ⟨t, ht, hlt⟩
  have := (ordered_unique g σ c γ b x0 N x x' Q Q' hE hE' hQ hle hb hx0 hg hA hK hγ hγ1).1 t ht
  linarith

/-- **Log utility:** two equilibria coincide at every horizon, with no further condition. -/
theorem unique_log (g σ c : ℝ) (b x0 : H → ℝ) (N : ℕ) (x x' : ℕ → H → ℝ) (Q Q' : ℕ → ℝ)
    (hE : IsEqN g σ c 1 b x0 N x Q) (hE' : IsEqN g σ c 1 b x0 N x' Q') :
    (∀ t < N, Q' t = Q t) ∧ ∀ t ≤ N, x' t = x t := by
  have hrr : rr 1 Q' = rr 1 Q := by funext t; simp [rr, ex]
  have hsav : ∀ t, savN 1 b N Q' t = savN 1 b N Q t := by
    intro t; funext h; unfold savN; rw [hrr]
  have hx : ∀ t ≤ N, x' t = x t := by
    intro t
    induction t with
    | zero => intro _; rw [hE.1, hE'.1]
    | succ t ih =>
      intro ht
      rw [(hE'.2 t (by omega)).1, (hE.2 t (by omega)).1, hsav t, ih (by omega)]
  refine ⟨fun t ht => ?_, hx⟩
  rw [(hE'.2 t ht).2, (hE.2 t ht).2, hsav t, hx t ht.le]

end PathUniquenessGS

#print axioms PathUniquenessGS.ex_nonneg
#print axioms PathUniquenessGS.F_mono
#print axioms PathUniquenessGS.savN_mono
#print axioms PathUniquenessGS.x_nonneg
#print axioms PathUniquenessGS.date_eq
#print axioms PathUniquenessGS.ordered_unique
#print axioms PathUniquenessGS.no_higher_path
#print axioms PathUniquenessGS.unique_log
