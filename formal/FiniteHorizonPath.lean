import FixedPointTheorems.brouwer
import Mathlib

/-!
# Stage 364: an equilibrium path with forward-looking saving, finite and infinite horizon

Continues stages 357 and 363 (definitions restated). Households have CRRA utility with curvature
`γ > 0` and patience factor `b h = β h ^ (1 / γ)`. A household that saves at date `t` earns the
gross return `Q t` on saved ownership, and the return is set by the issuance step: `Q t = 1 / B`,
with `B = ∑ s h x h` the aggregate saving rate weighted by ownership (as in stage 357).

* **The saving rule** (`F`, `savN`, `euler`, `terminal`): with `k` dates left, the ratio of planned
  future to present consumption is `F (k + 1) t = b r t (1 + F k (t + 1))`, `F 0 = 0`, where
  `r t = Q t ^ ((1 − γ) / γ)`; the saving rate is `F / (1 + F)`. `euler` proves that this rule
  meets the budget constraint and the CRRA Euler equation `c (t + 1) = (β Q t) ^ (1 / γ) c t`
  exactly, and `terminal` that the household consumes everything at the last date.
* **Finite horizon** (`exists_finite_equilibrium`, `finite_equilibrium`): for every `γ > 0`, every
  positive patience profile, every positive starting distribution and every horizon `N`, a
  perfect-foresight equilibrium path exists. The proof applies Brouwer's fixed-point theorem
  (`FixedPointTheorems.brouwer`) to the return path in a box `[1, M] ^ N`. Every equilibrium
  return lies in `[1, M]`, with `M` independent of `N`.
* **Infinite horizon** (`FInf`, `FInf_rec`, `IsEqInf`, `infinite_equilibrium_of`): with
  infinitely many dates the rule becomes the convergent series
  `FInf t = ∑ j, ∏ i ≤ j, b r (t + i)`, which satisfies the same recursion
  `FInf t = b r t (1 + FInf (t + 1))`. `infinite_equilibrium_of` shows that a cluster point of the
  finite-horizon equilibria (in the compact product `[0, 1] ^ ℕ × [1, M] ^ ℕ`) is an
  infinite-horizon equilibrium, whenever `b h q ^ ((1 − γ) / γ) ≤ bmax < 1` on `[1, M]`.
  * `infinite_equilibrium`: `γ ≥ 1` (log utility included) and every `b h < 1`.
  * `infinite_equilibrium_low`: `γ ≤ 1`, under the explicit condition
    `b h ((1 + bmin) / bmin) ^ ((1 − γ) / γ) < 1`, i.e. the plan has finite value even at the
    highest return the economy can produce.

Limits: uniqueness of the path is not proved (finite or infinite horizon); for `γ < 1` the
infinite-horizon result needs the stated condition, and it is not shown to be necessary; the
Euler equation and budget constraint are proved, but optimality of the rule (sufficiency of these
conditions, including a transversality condition) is not formalized; convergence of the path to
the long-run distribution is not proved; the return is `1 / B` as in stage 357; patience and
access remain exogenous.
-/

noncomputable section

open Finset BigOperators

namespace FiniteHorizonPath

variable {H : Type*} [Fintype H]

def B (s x : H → ℝ) : ℝ := ∑ k, s k * x k

def amp (g σ : ℝ) : ℝ := 1 + g * (1 - σ)

/-- The full-access issuance step (stage 357, `step_full`). -/
def T (g σ c : ℝ) (s x : H → ℝ) (h : H) : ℝ :=
  (amp g σ * (s h * x h / B s x) + g * σ * c) / (1 + g)

/-- Planned future-to-present consumption with `k` decision dates left, from date `t`. -/
def F (b : ℝ) (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k + 1, t => b * r t * (1 + F b r k (t + 1))

def ex (γ : ℝ) : ℝ := (1 - γ) / γ

def rr (γ : ℝ) (Q : ℕ → ℝ) (t : ℕ) : ℝ := Q t ^ ex γ

/-- The saving rate at date `t` with horizon `N` and return path `Q`. -/
def savN (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (t : ℕ) (h : H) : ℝ :=
  F (b h) (rr γ Q) (N - t) t / (1 + F (b h) (rr γ Q) (N - t) t)

/-- A perfect-foresight equilibrium path over `N` dates. -/
def IsEqN (g σ c γ : ℝ) (b x0 : H → ℝ) (N : ℕ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t < N, x (t + 1) = T g σ c (savN γ b N Q t) (x t) ∧
    Q t = 1 / B (savN γ b N Q t) (x t)

/-! ## The saving rule -/

/-- **The rule meets the budget constraint and the Euler equation.** With wealth `W`, consumption
`W / (1 + F)`, next wealth `Q (W − c)` and next consumption `W' / (1 + F')`, next consumption is
`b Q ^ (1 / γ)` times current consumption, i.e. `(β Q) ^ (1 / γ)`. -/
theorem euler (γ b R W F' : ℝ) (hγ : γ ≠ 0) (hR : 0 < R) (hb : 0 ≤ b) (hF' : 0 ≤ F') :
    R * (W - W / (1 + b * R ^ ex γ * (1 + F'))) / (1 + F') =
      b * R ^ (1 / γ) * (W / (1 + b * R ^ ex γ * (1 + F'))) := by
  have e : 1 / γ = 1 + ex γ := by unfold ex; field_simp; ring
  rw [e, Real.rpow_add hR, Real.rpow_one]
  have hq : 0 ≤ R ^ ex γ := Real.rpow_nonneg hR.le _
  have h1 : 0 < 1 + b * R ^ ex γ * (1 + F') := by
    have := mul_nonneg (mul_nonneg hb hq) (by linarith : (0:ℝ) ≤ 1 + F')
    linarith
  have h2 : 0 < 1 + F' := by linarith
  field_simp
  ring

omit [Fintype H] in
/-- **At the last date the household consumes everything.** -/
theorem terminal (γ : ℝ) (b : H → ℝ) (N : ℕ) (Q : ℕ → ℝ) (h : H) : savN γ b N Q N h = 0 := by
  simp [savN, F]

theorem F_nonneg (b : ℝ) (hb : 0 ≤ b) (r : ℕ → ℝ) (hr : ∀ t, 0 ≤ r t) :
    ∀ k t, 0 ≤ F b r k t := by
  intro k
  induction k with
  | zero => intro t; show (0:ℝ) ≤ 0; exact le_rfl
  | succ k ih =>
    intro t
    show 0 ≤ b * r t * (1 + F b r k (t + 1))
    exact mul_nonneg (mul_nonneg hb (hr t)) (by linarith [ih (t + 1)])

theorem F_ge (b : ℝ) (hb : 0 ≤ b) (r : ℕ → ℝ) (hr : ∀ t, 0 ≤ r t) (k t : ℕ) :
    b * r t ≤ F b r (k + 1) t := by
  show b * r t ≤ b * r t * (1 + F b r k (t + 1))
  have := F_nonneg b hb r hr k (t + 1)
  have := mul_nonneg hb (hr t)
  nlinarith

theorem frac_mono (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) : u / (1 + u) ≤ v / (1 + v) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

omit [Fintype H] in
theorem sav_pos {N : ℕ} (γ : ℝ) (b : H → ℝ) (hb0 : ∀ h, 0 < b h) (Q : ℕ → ℝ)
    (hQ : ∀ t, 0 < Q t) (t : ℕ) (ht : t < N) (h : H) : 0 < savN γ b N Q t h := by
  obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
  have hr : ∀ i, 0 ≤ rr γ Q i := fun i => Real.rpow_nonneg (hQ i).le _
  have hF := F_ge (b h) (hb0 h).le (rr γ Q) hr k t
  have hp : 0 < b h * rr γ Q t := mul_pos (hb0 h) (Real.rpow_pos_of_pos (hQ t) _)
  unfold savN
  rw [hk]
  exact div_pos (by linarith) (by linarith)

omit [Fintype H] in
theorem sav_le_one {N : ℕ} (γ : ℝ) (b : H → ℝ) (hb0 : ∀ h, 0 ≤ b h) (Q : ℕ → ℝ)
    (hQ : ∀ t, 0 ≤ Q t) (t : ℕ) (h : H) : savN γ b N Q t h ≤ 1 := by
  have hF := F_nonneg (b h) (hb0 h) (rr γ Q) (fun i => Real.rpow_nonneg (hQ i) _) (N - t) t
  unfold savN
  rw [div_le_one (by linarith)]
  linarith

omit [Fintype H] in
theorem sav_lower {N : ℕ} (γ : ℝ) (b : H → ℝ) (bmin m : ℝ) (hbmin : 0 < bmin)
    (hb : ∀ h, bmin ≤ b h) (hm : 0 < m) (Q : ℕ → ℝ) (hQ : ∀ t, 0 < Q t)
    (hmQ : ∀ t, m ≤ rr γ Q t) (t : ℕ) (ht : t < N) (h : H) :
    bmin * m / (1 + bmin * m) ≤ savN γ b N Q t h := by
  obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
  have hr : ∀ i, 0 ≤ rr γ Q i := fun i => Real.rpow_nonneg (hQ i).le _
  have hbh : 0 < b h := lt_of_lt_of_le hbmin (hb h)
  have hF := F_ge (b h) hbh.le (rr γ Q) hr k t
  have h1 : bmin * m ≤ b h * rr γ Q t := mul_le_mul (hb h) (hmQ t) hm.le hbh.le
  unfold savN
  rw [hk]
  exact frac_mono _ _ (mul_pos hbmin hm).le (h1.trans hF)

/-! ## The issuance step -/

theorem B_pos [Nonempty H] (s x : H → ℝ) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) :
    0 < B s x :=
  Finset.sum_pos (fun h _ => mul_pos (hs h) (hx h)) Finset.univ_nonempty

theorem amp_pos (g σ : ℝ) (hg : 0 < g) (hσ1 : σ ≤ 1) : 0 < amp g σ := by
  unfold amp; nlinarith [mul_nonneg hg.le (sub_nonneg.2 hσ1)]

theorem T_pos [Nonempty H] (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hs : ∀ h, 0 < s h) (hx : ∀ h, 0 < x h) (h : H) : 0 < T g σ c s x h := by
  unfold T
  have h1 := mul_pos (amp_pos g σ hg hσ1) (div_pos (mul_pos (hs h) (hx h)) (B_pos s x hs hx))
  have h2 : 0 ≤ g * σ * c := mul_nonneg (mul_nonneg hg.le hσ0) hc0
  exact div_pos (by linarith) (by linarith)

theorem T_sum (g σ c : ℝ) (s x : H → ℝ) (hg : 0 < g) (hB : B s x ≠ 0)
    (hc : (Fintype.card H : ℝ) * c = 1) : ∑ h, T g σ c s x h = 1 := by
  unfold T
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e : ∑ h, s h * x h = B s x := rfl
  rw [e, div_self hB, div_eq_one_iff_eq (by linarith)]
  unfold amp
  linear_combination g * σ * hc

/-! ## Continuity -/

theorem cont_B {X : Type*} [TopologicalSpace X] (s x : X → H → ℝ)
    (hs : ∀ k, Continuous fun p => s p k) (hx : ∀ k, Continuous fun p => x p k) :
    Continuous fun p => B (s p) (x p) := by
  unfold B
  exact continuous_finsetSum _ fun k _ => (hs k).mul (hx k)

theorem cont_T {X : Type*} [TopologicalSpace X] (g σ c : ℝ) (s x : X → H → ℝ)
    (hs : ∀ k, Continuous fun p => s p k) (hx : ∀ k, Continuous fun p => x p k)
    (hB : ∀ p, B (s p) (x p) ≠ 0) (h : H) : Continuous fun p => T g σ c (s p) (x p) h := by
  have hB' := cont_B s x hs hx
  unfold T
  exact ((continuous_const.mul (((hs h).mul (hx h)).div hB' hB)).add continuous_const).div_const _

theorem cont_F {X : Type*} [TopologicalSpace X] (b : ℝ) (r : X → ℕ → ℝ)
    (hr : ∀ i, Continuous fun p => r p i) : ∀ k t, Continuous fun p => F b (r p) k t := by
  intro k
  induction k with
  | zero => intro t; show Continuous fun _ : X => (0:ℝ); exact continuous_const
  | succ k ih =>
    intro t
    show Continuous fun p => b * r p t * (1 + F b (r p) k (t + 1))
    exact (continuous_const.mul (hr t)).mul (continuous_const.add (ih (t + 1)))

/-! ## The return-path map -/

/-- A candidate return path, clamped to `[1, M]` (the clamp is inactive at the fixed point). -/
def clampQ (M : ℝ) {N : ℕ} (R : Fin N → ℝ) (t : ℕ) : ℝ :=
  if h : t < N then max 1 (min M (R ⟨t, h⟩)) else 1

/-- The distribution path generated by a candidate return path. -/
def xP (g σ c γ M : ℝ) (b x0 : H → ℝ) {N : ℕ} (R : Fin N → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | t + 1 => T g σ c (savN γ b N (clampQ M R) t) (xP g σ c γ M b x0 R t)

/-- The returns that the generated path implies. -/
def Phi (g σ c γ M : ℝ) (b x0 : H → ℝ) {N : ℕ} (R : Fin N → ℝ) (i : Fin N) : ℝ :=
  max 1 (min M (1 / B (savN γ b N (clampQ M R) i) (xP g σ c γ M b x0 R i)))

theorem clamp_mem (M : ℝ) {N : ℕ} (hM : 1 ≤ M) (R : Fin N → ℝ) (t : ℕ) :
    1 ≤ clampQ M R t ∧ clampQ M R t ≤ M := by
  unfold clampQ
  split_ifs with h
  · exact ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩
  · exact ⟨le_rfl, hM⟩

theorem cont_clamp (M : ℝ) {N : ℕ} (t : ℕ) : Continuous fun R : Fin N → ℝ => clampQ M R t := by
  by_cases h : t < N
  · have e : (fun R : Fin N → ℝ => clampQ M R t) = fun R => max 1 (min M (R ⟨t, h⟩)) :=
      funext fun R => by simp only [clampQ, h, ↓reduceDIte]
    rw [e]
    exact continuous_const.max (continuous_const.min (continuous_apply _))
  · have e : (fun R : Fin N → ℝ => clampQ M R t) = fun _ => 1 :=
      funext fun R => by simp only [clampQ, h, ↓reduceDIte]
    rw [e]
    exact continuous_const

omit [Fintype H] in
theorem cont_sav (γ M : ℝ) (b : H → ℝ) {N : ℕ} (hM : 1 ≤ M) (hb0 : ∀ h, 0 ≤ b h) (t : ℕ)
    (h : H) : Continuous fun R : Fin N → ℝ => savN γ b N (clampQ M R) t h := by
  have hr : ∀ i, Continuous fun R : Fin N → ℝ => rr γ (clampQ M R) i := fun i =>
    (cont_clamp M i).rpow_const fun R =>
      Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (clamp_mem M hM R i).1))
  have hF := cont_F (b h) (fun R : Fin N → ℝ => rr γ (clampQ M R)) hr (N - t) t
  have hF0 : ∀ R : Fin N → ℝ, 0 ≤ F (b h) (rr γ (clampQ M R)) (N - t) t := fun R =>
    F_nonneg _ (hb0 h) _
      (fun i => Real.rpow_nonneg (le_trans zero_le_one (clamp_mem M hM R i).1) _) _ _
  show Continuous fun R : Fin N → ℝ =>
    F (b h) (rr γ (clampQ M R)) (N - t) t / (1 + F (b h) (rr γ (clampQ M R)) (N - t) t)
  exact hF.div (continuous_const.add hF) fun R => (by linarith [hF0 R] : (0:ℝ) < 1 + _).ne'

/-! ## Existence -/

/-- **Existence of a finite-horizon equilibrium path**, given a box `[1, M]` for returns that
the saving rule maps into itself. -/
theorem exists_finite_equilibrium (N : ℕ) (g σ c γ M m bmin : ℝ) (b x0 : H → ℝ)
    (hg : 0 < g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c)
    (hc : (Fintype.card H : ℝ) * c = 1) (hbmin : 0 < bmin) (hb : ∀ h, bmin ≤ b h)
    (hm : 0 < m) (hM : 1 ≤ M) (hmQ : ∀ q, 1 ≤ q → q ≤ M → m ≤ q ^ ex γ)
    (hcond : 1 + bmin * m ≤ M * (bmin * m))
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) :
    ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ), IsEqN g σ c γ b x0 N x Q ∧ ∀ t, 1 ≤ Q t ∧ Q t ≤ M := by
  have hb0 : ∀ h, 0 < b h := fun h => lt_of_lt_of_le hbmin (hb h)
  have hne : Nonempty H := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hx01
  have hQ : ∀ (R : Fin N → ℝ) t, 0 < clampQ M R t := fun R t =>
    lt_of_lt_of_le one_pos (clamp_mem M hM R t).1
  have hmQ' : ∀ (R : Fin N → ℝ) t, m ≤ rr γ (clampQ M R) t := fun R t =>
    hmQ _ (clamp_mem M hM R t).1 (clamp_mem M hM R t).2
  have hpos : ∀ (R : Fin N → ℝ) t, t ≤ N →
      (∀ h, 0 < xP g σ c γ M b x0 R t h) ∧ ∑ h, xP g σ c γ M b x0 R t h = 1 := by
    intro R t
    induction t with
    | zero => exact fun _ => ⟨hx0, hx01⟩
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hs : ∀ k, 0 < savN γ b N (clampQ M R) t k :=
        fun k => sav_pos γ b hb0 _ (hQ R) t (by omega) k
      exact ⟨fun h => T_pos g σ c _ _ hg hσ0 hσ1 hc0 hs ih'.1 h,
        T_sum g σ c _ _ hg (B_pos _ _ hs ih'.1).ne' hc⟩
  have hBnd : ∀ (R : Fin N → ℝ) t, t < N →
      1 / M ≤ B (savN γ b N (clampQ M R) t) (xP g σ c γ M b x0 R t) ∧
      B (savN γ b N (clampQ M R) t) (xP g σ c γ M b x0 R t) ≤ 1 := by
    intro R t ht
    obtain ⟨hxp, hxs⟩ := hpos R t ht.le
    have hbm : 0 < bmin * m := mul_pos hbmin hm
    have hlow : 1 / M ≤ bmin * m / (1 + bmin * m) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    constructor
    · unfold B
      calc 1 / M = ∑ k, 1 / M * xP g σ c γ M b x0 R t k := by
            rw [← Finset.mul_sum, hxs, mul_one]
        _ ≤ ∑ k, savN γ b N (clampQ M R) t k * xP g σ c γ M b x0 R t k :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (hlow.trans (sav_lower γ b bmin m hbmin hb hm _ (hQ R) (hmQ' R) t ht k)) (hxp k).le
    · unfold B
      calc ∑ k, savN γ b N (clampQ M R) t k * xP g σ c γ M b x0 R t k ≤
            ∑ k, xP g σ c γ M b x0 R t k :=
          Finset.sum_le_sum fun k _ => by
            have := sav_le_one (N := N) γ b (fun h => (hb0 h).le) (clampQ M R)
              (fun i => (hQ R i).le) t k
            nlinarith [hxp k]
        _ = 1 := hxs
  have hcs : ∀ t k, Continuous fun R : Fin N → ℝ => savN γ b N (clampQ M R) t k :=
    fun t k => cont_sav γ M b hM (fun h => (hb0 h).le) t k
  have hcx : ∀ t, t ≤ N → ∀ h, Continuous fun R : Fin N → ℝ => xP g σ c γ M b x0 R t h := by
    intro t
    induction t with
    | zero => exact fun _ h => continuous_const
    | succ t ih =>
      intro ht h
      exact cont_T g σ c (fun R => savN γ b N (clampQ M R) t) (fun R => xP g σ c γ M b x0 R t)
        (hcs t) (ih (by omega)) (fun R => (B_pos _ _
          (fun k => sav_pos γ b hb0 _ (hQ R) t (by omega) k) (hpos R t (by omega)).1).ne') h
  have hΦ : Continuous (Phi g σ c γ M b x0 : (Fin N → ℝ) → Fin N → ℝ) := by
    refine continuous_pi fun i => ?_
    have hB := cont_B (fun R : Fin N → ℝ => savN γ b N (clampQ M R) i)
      (fun R => xP g σ c γ M b x0 R i) (hcs i) (hcx i i.2.le)
    exact continuous_const.max (continuous_const.min (continuous_const.div hB fun R =>
      (B_pos _ _ (fun k => sav_pos γ b hb0 _ (hQ R) i i.2 k) (hpos R i i.2.le).1).ne'))
  let S : Set (Fin N → ℝ) := Set.Icc (fun _ => 1) (fun _ => M)
  have hmaps : ∀ R, Phi g σ c γ M b x0 R ∈ S := fun R =>
    ⟨fun i => le_max_left _ _, fun i => max_le hM (min_le_left _ _)⟩
  let f : C(S, S) := ⟨fun p => ⟨Phi g σ c γ M b x0 p.1, hmaps p.1⟩,
    (hΦ.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨p, hp⟩ := brouwer_fixed_point S (convex_Icc _ _) isCompact_Icc
    ⟨fun _ => 1, fun _ => le_rfl, fun _ => hM⟩ f
  have hfix : Phi g σ c γ M b x0 p.1 = p.1 := congrArg Subtype.val hp
  refine ⟨xP g σ c γ M b x0 p.1, clampQ M p.1, ⟨rfl, fun t ht => ⟨rfl, ?_⟩⟩,
    fun t => clamp_mem M hM p.1 t⟩
  have h1 : 1 ≤ p.1 ⟨t, ht⟩ := p.2.1 ⟨t, ht⟩
  have h2 : p.1 ⟨t, ht⟩ ≤ M := p.2.2 ⟨t, ht⟩
  obtain ⟨hl, hu⟩ := hBnd p.1 t ht
  have hBpos : 0 < B (savN γ b N (clampQ M p.1) t) (xP g σ c γ M b x0 p.1 t) :=
    lt_of_lt_of_le (div_pos one_pos (by linarith)) hl
  have hB1 : 1 ≤ 1 / B (savN γ b N (clampQ M p.1) t) (xP g σ c γ M b x0 p.1 t) := by
    rw [le_div_iff₀ hBpos]; linarith
  have hB2 : 1 / B (savN γ b N (clampQ M p.1) t) (xP g σ c γ M b x0 p.1 t) ≤ M := by
    rw [div_le_iff₀ hBpos]
    rw [div_le_iff₀ (by linarith)] at hl
    nlinarith
  calc clampQ M p.1 t = p.1 ⟨t, ht⟩ := by
        simp only [clampQ, ht, ↓reduceDIte]; rw [min_eq_right h2, max_eq_right h1]
    _ = Phi g σ c γ M b x0 p.1 ⟨t, ht⟩ := (congrFun hfix _).symm
    _ = 1 / B (savN γ b N (clampQ M p.1) t) (xP g σ c γ M b x0 p.1 t) := by
        show max 1 (min M (1 / B (savN γ b N (clampQ M p.1) t) (xP g σ c γ M b x0 p.1 t))) = _
        rw [min_eq_right hB2, max_eq_right hB1]

/-- **For every curvature `γ > 0` and every horizon `N`, a perfect-foresight equilibrium path
exists**, with all returns in `[1, M]` for an `M` that does not depend on `N`. -/
theorem finite_equilibrium (g σ c γ : ℝ) (b x0 : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hγ : 0 < γ)
    (hb0 : ∀ h, 0 < b h) (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ N : ℕ, ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ),
      IsEqN g σ c γ b x0 N x Q ∧ ∀ t, 1 ≤ Q t ∧ Q t ≤ M := by
  have hne : Nonempty H := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hx01
  obtain ⟨bmin, hbmin, hb⟩ : ∃ bmin : ℝ, 0 < bmin ∧ ∀ h, bmin ≤ b h :=
    ⟨Finset.univ.inf' Finset.univ_nonempty b, (Finset.lt_inf'_iff _).2 fun h _ => hb0 h,
      fun h => Finset.inf'_le _ (Finset.mem_univ h)⟩
  have hq : 1 ≤ (1 + bmin) / bmin := by rw [le_div_iff₀ hbmin]; linarith
  have hqb : (1 + bmin) / bmin * bmin = 1 + bmin := div_mul_cancel₀ _ hbmin.ne'
  rcases le_or_gt γ 1 with hγ1 | hγ1
  · have hex : 0 ≤ ex γ := div_nonneg (by linarith) hγ.le
    refine ⟨(1 + bmin) / bmin, hq, fun N => ?_⟩
    exact exists_finite_equilibrium N g σ c γ _ 1 bmin b x0 hg hσ0 hσ1 hc0 hc hbmin hb one_pos hq
      (fun q hq1 _ => Real.one_le_rpow hq1 hex) (le_of_eq (by rw [mul_one, hqb])) hx0 hx01
  · have hex : ex γ ≤ 0 := (div_neg_of_neg_of_pos (by linarith) hγ).le
    have hq0 : 0 < (1 + bmin) / bmin := by linarith
    have hM : 1 ≤ ((1 + bmin) / bmin) ^ γ := Real.one_le_rpow hq hγ.le
    have hm : 0 < (((1 + bmin) / bmin) ^ γ) ^ ex γ := Real.rpow_pos_of_pos (by linarith) _
    have hm1 : (((1 + bmin) / bmin) ^ γ) ^ ex γ ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hM hex
    have hMm : ((1 + bmin) / bmin) ^ γ * (((1 + bmin) / bmin) ^ γ) ^ ex γ = (1 + bmin) / bmin := by
      rw [← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
      have e : γ + γ * ex γ = 1 := by unfold ex; field_simp; ring
      rw [e, Real.rpow_one]
    refine ⟨_, hM, fun N => ?_⟩
    refine exists_finite_equilibrium N g σ c γ _ _ bmin b x0 hg hσ0 hσ1 hc0 hc hbmin hb hm hM
      (fun q hq1 hqM => Real.rpow_le_rpow_of_nonpos (by linarith) hqM hex) ?_ hx0 hx01
    have e2 : ((1 + bmin) / bmin) ^ γ * (bmin * (((1 + bmin) / bmin) ^ γ) ^ ex γ) = 1 + bmin := by
      rw [show ((1 + bmin) / bmin) ^ γ * (bmin * (((1 + bmin) / bmin) ^ γ) ^ ex γ) =
        ((1 + bmin) / bmin) ^ γ * (((1 + bmin) / bmin) ^ γ) ^ ex γ * bmin by ring, hMm, hqb]
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left hm1 hbmin.le]


/-! ## The infinite horizon: the limit `N → ∞`

For `γ ≥ 1` and patience factors `b h < 1`, the infinite-horizon saving rule is
`F t = ∑ j, ∏ i ≤ j, b r (t + i)`, a convergent series. The finite-horizon equilibria have
returns in `[1, M]` for an `M` that does not depend on `N`; a cluster point of them in the
compact box `[1, M] ^ ℕ` (Tychonoff) is an infinite-horizon equilibrium. To make the limit
argument go through, the horizon is encoded as a cutoff vector `e ∈ [0, 1] ^ ℕ` (`e j = 1` before
the horizon, `0` after), so that the finite and infinite rules are one jointly continuous map. -/

/-- The horizon-`N` cutoff vector. -/
def eN (N : ℕ) (j : ℕ) : ℝ := if j < N then 1 else 0

def ce (e : ℝ) : ℝ := max 0 (min 1 e)

def cl (M q : ℝ) : ℝ := max 1 (min M q)

def rc (M γ : ℝ) (Q : ℕ → ℝ) (i : ℕ) : ℝ := cl M (Q i) ^ ex γ

/-- The saving rule with a cutoff vector `e`: the first term is always present. -/
def Fc (b : ℝ) (e r : ℕ → ℝ) (t : ℕ) : ℝ :=
  b * r t + ∑' j : ℕ, (∏ i ∈ range (j + 1 + 1), b * r (t + i)) * ce (e (t + j + 1))

def savC (γ M : ℝ) (b : H → ℝ) (e Q : ℕ → ℝ) (t : ℕ) (h : H) : ℝ :=
  Fc (b h) e (rc M γ Q) t / (1 + Fc (b h) e (rc M γ Q) t)

def xC (g σ c γ M : ℝ) (b x0 : H → ℝ) (e Q : ℕ → ℝ) : ℕ → H → ℝ
  | 0 => x0
  | t + 1 => T g σ c (savC γ M b e Q t) (xC g σ c γ M b x0 e Q t)

/-- The infinite-horizon planned future-to-present consumption ratio. -/
def FInf (b : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, ∏ i ∈ range (j + 1), b * r (t + i)

def savInf (γ : ℝ) (b : H → ℝ) (Q : ℕ → ℝ) (t : ℕ) (h : H) : ℝ :=
  FInf (b h) (rr γ Q) t / (1 + FInf (b h) (rr γ Q) t)

/-- A perfect-foresight equilibrium path over infinitely many dates. -/
def IsEqInf (g σ c γ : ℝ) (b x0 : H → ℝ) (x : ℕ → H → ℝ) (Q : ℕ → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t, x (t + 1) = T g σ c (savInf γ b Q t) (x t) ∧
    Q t = 1 / B (savInf γ b Q t) (x t)

theorem F_sum (b : ℝ) (r : ℕ → ℝ) :
    ∀ k t, F b r k t = ∑ j ∈ range k, ∏ i ∈ range (j + 1), b * r (t + i) := by
  intro k
  induction k with
  | zero => intro t; simp [F]
  | succ k ih =>
    intro t
    show b * r t * (1 + F b r k (t + 1)) = _
    rw [ih (t + 1), Finset.sum_range_succ', mul_add, mul_one, Finset.mul_sum, add_comm (b * r t)]
    simp only [zero_add, Finset.prod_range_one, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_range_succ' _ (j + 1), add_zero, mul_comm (b * r t)]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [show t + 1 + i = t + (i + 1) by omega]

theorem term_bound (b bmax R : ℝ) (r e : ℕ → ℝ) (hb : 0 ≤ b) (hbm : b * R ≤ bmax)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ R) (t j : ℕ) :
    0 ≤ (∏ i ∈ range (j + 1 + 1), b * r (t + i)) * ce (e (t + j + 1)) ∧
      (∏ i ∈ range (j + 1 + 1), b * r (t + i)) * ce (e (t + j + 1)) ≤ bmax ^ 2 * bmax ^ j := by
  have hc0 : 0 ≤ ce (e (t + j + 1)) := le_max_left _ _
  have hc1 : ce (e (t + j + 1)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hp0 : 0 ≤ ∏ i ∈ range (j + 1 + 1), b * r (t + i) :=
    Finset.prod_nonneg fun i _ => mul_nonneg hb (hr0 _)
  have hp1 : ∏ i ∈ range (j + 1 + 1), b * r (t + i) ≤ bmax ^ 2 * bmax ^ j := by
    calc ∏ i ∈ range (j + 1 + 1), b * r (t + i) ≤ ∏ _i ∈ range (j + 1 + 1), bmax :=
          Finset.prod_le_prod₀ (fun i _ => mul_nonneg hb (hr0 _))
            fun i _ => (mul_le_mul_of_nonneg_left (hr1 _) hb).trans hbm
      _ = bmax ^ 2 * bmax ^ j := by rw [Finset.prod_const, Finset.card_range]; ring
  exact ⟨mul_nonneg hp0 hc0, (mul_le_of_le_one_right hp0 hc1).trans hp1⟩

theorem FInf_summable (b bmax R : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) (hbm0 : 0 ≤ bmax)
    (hbm : b * R ≤ bmax) (hbm1 : bmax < 1) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ R) (t : ℕ) :
    Summable fun j : ℕ => ∏ i ∈ range (j + 1), b * r (t + i) := by
  refine Summable.of_nonneg_of_le (fun j => Finset.prod_nonneg fun i _ => mul_nonneg hb (hr0 _))
    (fun j => ?_) ((summable_geometric_of_lt_one hbm0 hbm1).mul_left bmax)
  calc ∏ i ∈ range (j + 1), b * r (t + i) ≤ ∏ _i ∈ range (j + 1), bmax :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg hb (hr0 _))
          fun i _ => (mul_le_mul_of_nonneg_left (hr1 _) hb).trans hbm
    _ = bmax * bmax ^ j := by rw [Finset.prod_const, Finset.card_range, pow_succ]; ring

/-- **The infinite-horizon rule satisfies the same recursion** `F t = b r t (1 + F (t + 1))`, so
`euler` applies to it at every date. -/
theorem FInf_rec (b bmax R : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) (hbm0 : 0 ≤ bmax)
    (hbm : b * R ≤ bmax) (hbm1 : bmax < 1) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ R) (t : ℕ) :
    FInf b r t = b * r t * (1 + FInf b r (t + 1)) := by
  have hs := FInf_summable b bmax R r hb hbm0 hbm hbm1 hr0 hr1 t
  have e : ∀ j : ℕ, ∏ i ∈ range (j + 1 + 1), b * r (t + i) =
      (∏ i ∈ range (j + 1), b * r (t + 1 + i)) * (b * r t) := by
    intro j
    rw [Finset.prod_range_succ' _ (j + 1), add_zero]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [show t + 1 + i = t + (i + 1) by omega]
  unfold FInf
  rw [hs.tsum_eq_zero_add]
  simp only [e, tsum_mul_right, zero_add, Finset.prod_range_one, add_zero]
  ring

theorem Fc_nonneg (b : ℝ) (e r : ℕ → ℝ) (hb : 0 ≤ b) (hr0 : ∀ i, 0 ≤ r i) (t : ℕ) :
    b * r t ≤ Fc b e r t := by
  unfold Fc
  have : 0 ≤ ∑' j : ℕ, (∏ i ∈ range (j + 1 + 1), b * r (t + i)) * ce (e (t + j + 1)) :=
    tsum_nonneg fun j => mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg hb (hr0 _))
      (le_max_left _ _)
  linarith

/-- With the horizon-`N` cutoff, the cutoff rule is exactly the finite-horizon rule. -/
theorem Fc_trunc (b : ℝ) (r : ℕ → ℝ) (N t : ℕ) (ht : t < N) :
    Fc b (eN N) r t = F b r (N - t) t := by
  obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
  rw [hk, F_sum]
  simp only [Finset.sum_range_succ', zero_add, Finset.prod_range_one, add_zero]
  unfold Fc
  rw [tsum_eq_sum (s := range k) ?_]
  · rw [add_comm (b * r t)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have : ce (eN N (t + j + 1)) = 1 := by
      simp [ce, eN, show t + j + 1 < N by omega]
    rw [this, mul_one]
  · intro j hj
    rw [Finset.mem_range] at hj
    have : ce (eN N (t + j + 1)) = 0 := by
      simp [ce, eN, show ¬ (t + j + 1 < N) by omega]
    rw [this, mul_zero]

/-- With the cutoff all ones, the cutoff rule is the infinite-horizon rule. -/
theorem Fc_one (b bmax R : ℝ) (r : ℕ → ℝ) (hb : 0 ≤ b) (hbm0 : 0 ≤ bmax)
    (hbm : b * R ≤ bmax) (hbm1 : bmax < 1) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ R) (t : ℕ) :
    Fc b (fun _ => 1) r t = FInf b r t := by
  have hs := FInf_summable b bmax R r hb hbm0 hbm hbm1 hr0 hr1 t
  have hce : ce 1 = 1 := by unfold ce; norm_num
  unfold Fc FInf
  rw [hs.tsum_eq_zero_add]
  simp only [hce, mul_one, zero_add, Finset.prod_range_one, add_zero]

theorem cont_Fc {X : Type*} [TopologicalSpace X] (b bmax R : ℝ) (hb : 0 ≤ b) (hbm0 : 0 ≤ bmax)
    (hbm : b * R ≤ bmax) (hbm1 : bmax < 1) (e r : X → ℕ → ℝ) (he : ∀ i, Continuous fun p => e p i)
    (hr : ∀ i, Continuous fun p => r p i) (hr0 : ∀ p i, 0 ≤ r p i) (hr1 : ∀ p i, r p i ≤ R)
    (t : ℕ) : Continuous fun p => Fc b (e p) (r p) t := by
  show Continuous fun p => b * r p t +
    ∑' j : ℕ, (∏ i ∈ range (j + 1 + 1), b * r p (t + i)) * ce (e p (t + j + 1))
  refine (continuous_const.mul (hr t)).add (continuous_tsum (u := fun j => bmax ^ 2 * bmax ^ j)
    (fun j => ?_) ((summable_geometric_of_lt_one hbm0 hbm1).mul_left _) fun j p => ?_)
  · exact (continuous_finsetProd _ fun i _ => continuous_const.mul (hr _)).mul
      (continuous_const.max (continuous_const.min (he _)))
  · obtain ⟨h0, h1⟩ := term_bound b bmax R (r p) (e p) hb hbm (hr0 p) (hr1 p) t j
    rw [Real.norm_of_nonneg h0]
    exact h1

/-- **The limit step.** If the finite-horizon equilibria all have returns in `[1, M]`, and on
`[1, M]` the discounted growth factor `b h q ^ ((1 − γ) / γ)` stays below `bmax < 1`, then a
cluster point of the finite-horizon equilibria is an infinite-horizon equilibrium. -/
theorem infinite_equilibrium_of [Nonempty H] (g σ c γ M R bmax : ℝ) (b x0 : H → ℝ) (hg : 0 < g)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hb0 : ∀ h, 0 < b h) (hx0 : ∀ h, 0 < x0 h)
    (hM : 1 ≤ M) (hR : ∀ q, 1 ≤ q → q ≤ M → q ^ ex γ ≤ R) (hbm0 : 0 ≤ bmax)
    (hbb : ∀ h, b h * R ≤ bmax) (hbm1 : bmax < 1)
    (hfin : ∀ N : ℕ, ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ),
      IsEqN g σ c γ b x0 N x Q ∧ ∀ t, 1 ≤ Q t ∧ Q t ≤ M) :
    ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ), IsEqInf g σ c γ b x0 x Q ∧ ∀ t, 1 ≤ Q t ∧ Q t ≤ M := by
  choose xs Qs hEq hQb using hfin
  have hrc : ∀ (Q : ℕ → ℝ) i, 0 < rc M γ Q i ∧ rc M γ Q i ≤ R := fun Q i =>
    ⟨Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _,
      hR _ (le_max_left _ _) (max_le hM (min_le_left _ _))⟩
  have hrc_eq : ∀ Q : ℕ → ℝ, (∀ i, 1 ≤ Q i ∧ Q i ≤ M) → rc M γ Q = rr γ Q := fun Q hQ =>
    funext fun i => by
      unfold rc rr cl; rw [min_eq_right (hQ i).2, max_eq_right (hQ i).1]
  have hsp : ∀ e Q t h, 0 < savC γ M b e Q t h := by
    intro e Q t h
    have := Fc_nonneg (b h) e (rc M γ Q) (hb0 h).le (fun i => (hrc Q i).1.le) t
    have := mul_pos (hb0 h) (hrc Q t).1
    unfold savC
    exact div_pos (by linarith) (by linarith)
  have hxp : ∀ e Q t h, 0 < xC g σ c γ M b x0 e Q t h := by
    intro e Q t
    induction t with
    | zero => exact hx0
    | succ t ih => exact T_pos g σ c _ _ hg hσ0 hσ1 hc0 (hsp e Q t) ih
  let X := (ℕ → ℝ) × (ℕ → ℝ)
  have hcs : ∀ t h, Continuous fun p : X => savC γ M b p.1 p.2 t h := by
    intro t h
    have hrcc : ∀ i, Continuous fun p : X => rc M γ p.2 i := fun i =>
      (continuous_const.max (continuous_const.min ((continuous_apply i).comp continuous_snd))).rpow_const
        fun p => Or.inl (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    have hF := cont_Fc (b h) bmax R (hb0 h).le hbm0 (hbb h) hbm1 (fun p : X => p.1) (fun p => rc M γ p.2)
      (fun i => (continuous_apply i).comp continuous_fst) hrcc (fun p i => (hrc p.2 i).1.le)
      (fun p i => (hrc p.2 i).2) t
    have hF0 : ∀ p : X, 0 ≤ Fc (b h) p.1 (rc M γ p.2) t := fun p =>
      le_trans (mul_nonneg (hb0 h).le (hrc p.2 t).1.le)
        (Fc_nonneg (b h) p.1 (rc M γ p.2) (hb0 h).le (fun i => (hrc p.2 i).1.le) t)
    exact hF.div (continuous_const.add hF) fun p => (by linarith [hF0 p] : (0:ℝ) < 1 + _).ne'
  have hcx : ∀ t h, Continuous fun p : X => xC g σ c γ M b x0 p.1 p.2 t h := by
    intro t
    induction t with
    | zero => exact fun h => continuous_const
    | succ t ih =>
      intro h
      exact cont_T g σ c (fun p : X => savC γ M b p.1 p.2 t)
        (fun p => xC g σ c γ M b x0 p.1 p.2 t) (hcs t) ih
        (fun p => (B_pos _ _ (hsp p.1 p.2 t) (hxp p.1 p.2 t)).ne') h
  have htr : ∀ N t, t < N → savC γ M b (eN N) (Qs N) t = savN γ b N (Qs N) t := by
    intro N t ht
    funext h
    unfold savC savN
    rw [hrc_eq (Qs N) (hQb N), Fc_trunc _ _ N t ht]
  have hmatch : ∀ N t, t ≤ N → xC g σ c γ M b x0 (eN N) (Qs N) t = xs N t := by
    intro N t
    induction t with
    | zero => intro _; exact (hEq N).1.symm
    | succ t ih =>
      intro ht
      rw [((hEq N).2 t (by omega)).1]
      show T g σ c (savC γ M b (eN N) (Qs N) t) (xC g σ c γ M b x0 (eN N) (Qs N) t) = _
      rw [ih (by omega), htr N t (by omega)]
  let u : ℕ → X := fun N => (eN N, Qs N)
  let K : Set X := (Set.univ.pi fun _ : ℕ => Set.Icc (0:ℝ) 1) ×ˢ
    (Set.univ.pi fun _ : ℕ => Set.Icc 1 M)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have huK : Filter.map u Filter.atTop ≤ Filter.principal K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    refine Filter.univ_mem' fun N => ⟨fun j _ => ?_, fun t _ => hQb N t⟩
    show (0:ℝ) ≤ eN N j ∧ eN N j ≤ 1
    unfold eN; split_ifs <;> norm_num
  obtain ⟨p, hpK, hp⟩ := hK.exists_clusterPt huK
  have key : ∀ S : Set X, IsClosed S → (∀ᶠ N in Filter.atTop, u N ∈ S) → p ∈ S := by
    intro S hS hev
    by_contra hpS
    have h1 : ∃ᶠ N in Filter.atTop, u N ∈ Sᶜ :=
      (show MapClusterPt p Filter.atTop u from hp).frequently (hS.isOpen_compl.mem_nhds hpS)
    obtain ⟨N, hN⟩ := (h1.and_eventually hev).exists
    exact hN.1 hN.2
  have he : p.1 = fun _ => 1 := funext fun j =>
    key {q : X | q.1 j = 1} (isClosed_eq ((continuous_apply j).comp continuous_fst)
      continuous_const) (Filter.eventually_atTop.2 ⟨j + 1, fun N hN => by
        show eN N j = 1
        simp [eN, show j < N by omega]⟩)
  have hQ : ∀ t, p.2 t * B (savC γ M b p.1 p.2 t) (xC g σ c γ M b x0 p.1 p.2 t) = 1 := fun t =>
    key {q : X | q.2 t * B (savC γ M b q.1 q.2 t) (xC g σ c γ M b x0 q.1 q.2 t) = 1}
      (isClosed_eq (((continuous_apply t).comp continuous_snd).mul
        (cont_B _ _ (hcs t) (hcx t))) continuous_const)
      (Filter.eventually_atTop.2 ⟨t + 1, fun N hN => by
        show Qs N t * B (savC γ M b (eN N) (Qs N) t) (xC g σ c γ M b x0 (eN N) (Qs N) t) = 1
        have e1 := ((hEq N).2 t (by omega)).2
        rw [hmatch N t (by omega), htr N t (by omega)]
        have hB : B (savN γ b N (Qs N) t) (xs N t) ≠ 0 := fun h0 => by
          rw [h0, div_zero] at e1; linarith [(hQb N t).1]
        rw [e1, one_div, inv_mul_cancel₀ hB]⟩)
  have hpQ : ∀ t, 1 ≤ p.2 t ∧ p.2 t ≤ M := fun t => hpK.2 t (Set.mem_univ t)
  have hsI : ∀ t, savC γ M b p.1 p.2 t = savInf γ b p.2 t := fun t => by
    rw [he]
    funext h
    unfold savC savInf
    rw [hrc_eq p.2 hpQ, Fc_one (b h) bmax R _ (hb0 h).le hbm0 (hbb h) hbm1
      (fun i => by rw [← hrc_eq p.2 hpQ]; exact (hrc p.2 i).1.le)
      (fun i => by rw [← hrc_eq p.2 hpQ]; exact (hrc p.2 i).2)]
  refine ⟨xC g σ c γ M b x0 p.1 p.2, p.2, ⟨rfl, fun t => ⟨?_, ?_⟩⟩, hpQ⟩
  · rw [← hsI t]; rfl
  · rw [← hsI t, eq_div_iff (B_pos _ _ (hsp p.1 p.2 t) (hxp p.1 p.2 t)).ne']
    exact hQ t


/-- **Existence of an infinite-horizon equilibrium path, `γ ≥ 1`.** For curvature `γ ≥ 1` (log
utility included) and patience factors `b h < 1`, a perfect-foresight equilibrium path over
infinitely many dates exists, with returns in `[1, M]`. -/
theorem infinite_equilibrium (g σ c γ : ℝ) (b x0 : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hγ : 1 ≤ γ)
    (hb0 : ∀ h, 0 < b h) (hb1 : ∀ h, b h < 1) (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ),
      IsEqInf g σ c γ b x0 x Q ∧ ∀ t, 1 ≤ Q t ∧ Q t ≤ M := by
  obtain ⟨M, hM, hfin⟩ :=
    finite_equilibrium g σ c γ b x0 hg hσ0 hσ1 hc0 hc (by linarith) hb0 hx0 hx01
  have hne : Nonempty H := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hx01
  have hex : ex γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  refine ⟨M, hM, infinite_equilibrium_of g σ c γ M 1 (Finset.univ.sup' Finset.univ_nonempty b)
    b x0 hg hσ0 hσ1 hc0 hb0 hx0 hM
    (fun q hq1 _ => Real.rpow_le_one_of_one_le_of_nonpos hq1 hex)
    ((hb0 hne.some).le.trans (Finset.le_sup' b (Finset.mem_univ _)))
    (fun h => by rw [mul_one]; exact Finset.le_sup' b (Finset.mem_univ h))
    ((Finset.sup'_lt_iff _).2 fun h _ => hb1 h) hfin⟩

/-- **Existence of an infinite-horizon equilibrium path, `γ ≤ 1`.** With `bmin ≤ b h` and the
condition `b h · q ^ ((1 − γ) / γ) < 1` at `q = (1 + bmin) / bmin` (patience low enough that the
infinite-horizon plan has finite value at the highest possible return), a perfect-foresight
equilibrium path over infinitely many dates exists. -/
theorem infinite_equilibrium_low (g σ c γ bmin : ℝ) (b x0 : H → ℝ) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hc : (Fintype.card H : ℝ) * c = 1) (hγ0 : 0 < γ)
    (hγ : γ ≤ 1) (hbmin : 0 < bmin) (hb : ∀ h, bmin ≤ b h)
    (hcond : ∀ h, b h * ((1 + bmin) / bmin) ^ ex γ < 1)
    (hx0 : ∀ h, 0 < x0 h) (hx01 : ∑ h, x0 h = 1) :
    ∃ (x : ℕ → H → ℝ) (Q : ℕ → ℝ), IsEqInf g σ c γ b x0 x Q ∧
      ∀ t, 1 ≤ Q t ∧ Q t ≤ (1 + bmin) / bmin := by
  have hne : Nonempty H := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hx01
  have hb0 : ∀ h, 0 < b h := fun h => lt_of_lt_of_le hbmin (hb h)
  have hex : 0 ≤ ex γ := div_nonneg (by linarith) hγ0.le
  have hq : 1 ≤ (1 + bmin) / bmin := by rw [le_div_iff₀ hbmin]; linarith
  have hqb : (1 + bmin) / bmin * bmin = 1 + bmin := div_mul_cancel₀ _ hbmin.ne'
  have hfin := fun N => exists_finite_equilibrium N g σ c γ _ 1 bmin b x0 hg hσ0 hσ1 hc0 hc
    hbmin hb one_pos hq (fun q hq1 _ => Real.one_le_rpow hq1 hex)
    (le_of_eq (by rw [mul_one, hqb])) hx0 hx01
  let f : H → ℝ := fun h => b h * ((1 + bmin) / bmin) ^ ex γ
  exact infinite_equilibrium_of g σ c γ _ _ (Finset.univ.sup' Finset.univ_nonempty f) b x0 hg
    hσ0 hσ1 hc0 hb0 hx0 hq
    (fun q hq1 hqM => Real.rpow_le_rpow (by linarith) hqM hex)
    ((mul_nonneg (hb0 hne.some).le (Real.rpow_nonneg (by linarith) _)).trans
      (Finset.le_sup' f (Finset.mem_univ _)))
    (fun h => Finset.le_sup' f (Finset.mem_univ h))
    ((Finset.sup'_lt_iff _).2 fun h _ => hcond h) hfin

end FiniteHorizonPath

end

#print axioms FiniteHorizonPath.euler
#print axioms FiniteHorizonPath.terminal
#print axioms FiniteHorizonPath.sav_lower
#print axioms FiniteHorizonPath.T_sum
#print axioms FiniteHorizonPath.cont_sav
#print axioms FiniteHorizonPath.exists_finite_equilibrium
#print axioms FiniteHorizonPath.finite_equilibrium
#print axioms FiniteHorizonPath.F_sum
#print axioms FiniteHorizonPath.FInf_rec
#print axioms FiniteHorizonPath.Fc_trunc
#print axioms FiniteHorizonPath.cont_Fc
#print axioms FiniteHorizonPath.infinite_equilibrium_of
#print axioms FiniteHorizonPath.infinite_equilibrium
#print axioms FiniteHorizonPath.infinite_equilibrium_low
