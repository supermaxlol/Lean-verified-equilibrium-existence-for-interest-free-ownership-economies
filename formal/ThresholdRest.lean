import Mathlib

/-!
# Stage 368: long-run distributions under threshold (discontinuous) access

Stage 365 proved that a long-run distribution exists when saving and access rules are
continuous in the distribution, using Brouwer's theorem. All-or-nothing access rules (a
household gets new units pro rata only once its share reaches a threshold `θb`, stage 356) are
discontinuous, so that argument does not apply. This file treats them with an order argument
instead of a topological one, for two households.

Setup (stage 365, two households): household 1 holds the share `x`, household 2 holds `1 − x`.
Saving rates `s1, s2 > 0` are fixed, so household 1's share of saved ownership is
`p x = s1 x / (s1 x + s2 (1 − x))`. New units are issued at rate `g ≥ 0`: a fraction `σ ∈ [0, 1]`
equally (`1/2` each), the rest pro rata to saved ownership weighted by an access intensity
`a` read off the household's own current share. Household 1's next share is
`F x = (p x + g (σ / 2 + (1 − σ) U x / (U x + V x))) / (1 + g)` with `U x = a x · p x` and
`V x = a (1 − x) · (1 − p x)` (`F2` is household 2's share; `F_add_F2`: they sum to one).

* `fixed_greatest`, `fixed_least`: any nondecreasing self-map of `[0, 1]`, continuous or not,
  has a greatest and a least fixed point (Knaster–Tarski, proved directly with suprema).
* `F_mono`: if `a` is nondecreasing and non-negative on `[0, 1]` (it may jump), `F` is
  nondecreasing.
* **`exists_rest_monotone`**: under those conditions, and as long as some saved ownership has
  access (`U x + V x > 0`), a long-run distribution exists; there is a least and a greatest one
  and every other lies between them. `rest_floor`: in every long-run distribution each household
  holds at least `g σ / (2 (1 + g))`.
* **`exists_rest_threshold`**: the threshold rule `thr θb α0` (full access at a share of at least
  `θb`, intensity `α0 ∈ (0, 1]` below it) has a long-run distribution for any saving rates.
* **`exists_rest_all_or_nothing`**: the strict all-or-nothing rule (`α0 = 0`, no pro-rata units
  at all below the threshold) with equal saving rates and `θb ≤ 1/2`.
* **A poverty trap** (`two_rest_threshold`): with `g = 1`, `σ = 1/2`, equal saving, threshold
  `1/2` and intensity `2/5` below it, the shares `1/3`, `1/2` and `2/3` are all long-run
  distributions. At `1/3` household 1 stays below the threshold for ever, though the equal
  distribution is also a rest point.

Limits: two households only; saving rates do not depend on wealth (wealth-dependent patience is
covered, for continuous rules, by stage 365); the access intensity depends on the household's own
share and must be nondecreasing in it. Existence only: which rest point is reached, and whether
the iteration converges to one, is not proved (for a discontinuous map the limit of the
iteration need not be a rest point). The many-household case is not covered: there the update is
not monotone in any obvious order, and the argument does not extend directly.
-/

noncomputable section

open Set

namespace ThresholdRest

/-! ## Knaster–Tarski on `[0, 1]` -/

/-- **A nondecreasing self-map of `[0, 1]` has a greatest fixed point.** No continuity needed. -/
theorem fixed_greatest (f : ℝ → ℝ) (hmap : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn f (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = x ∧ ∀ y ∈ Icc (0 : ℝ) 1, f y = y → y ≤ x := by
  set A := {x | x ∈ Icc (0 : ℝ) 1 ∧ x ≤ f x} with hA
  have h0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, zero_le_one⟩, (hmap 0 ⟨le_rfl, zero_le_one⟩).1⟩
  have bdd : BddAbove A := ⟨1, fun x hx => hx.1.2⟩
  set s := sSup A with hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨le_csSup bdd h0, csSup_le ⟨0, h0⟩ fun x hx => hx.1.2⟩
  have hsf : s ≤ f s :=
    csSup_le ⟨0, h0⟩ fun x hx => hx.2.trans (hmono hx.1 hsI (le_csSup bdd hx))
  have hfA : f s ∈ A := ⟨hmap s hsI, hmono hsI (hmap s hsI) hsf⟩
  exact ⟨s, hsI, le_antisymm (le_csSup bdd hfA) hsf, fun y hy hfy =>
    le_csSup bdd ⟨hy, hfy.ge⟩⟩

/-- **A nondecreasing self-map of `[0, 1]` has a least fixed point.** -/
theorem fixed_least (f : ℝ → ℝ) (hmap : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc (0 : ℝ) 1)
    (hmono : MonotoneOn f (Icc 0 1)) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x = x ∧ ∀ y ∈ Icc (0 : ℝ) 1, f y = y → x ≤ y := by
  set A := {x | x ∈ Icc (0 : ℝ) 1 ∧ f x ≤ x} with hA
  have h1 : (1 : ℝ) ∈ A := ⟨⟨zero_le_one, le_rfl⟩, (hmap 1 ⟨zero_le_one, le_rfl⟩).2⟩
  have bdd : BddBelow A := ⟨0, fun x hx => hx.1.1⟩
  set s := sInf A with hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨le_csInf ⟨1, h1⟩ fun x hx => hx.1.1, csInf_le bdd h1⟩
  have hfs : f s ≤ s :=
    le_csInf ⟨1, h1⟩ fun x hx => (hmono hsI hx.1 (csInf_le bdd hx)).trans hx.2
  have hfA : f s ∈ A := ⟨hmap s hsI, hmono (hmap s hsI) hsI hfs⟩
  exact ⟨s, hsI, le_antisymm hfs (csInf_le bdd hfA), fun y hy hfy =>
    csInf_le bdd ⟨hy, hfy.le⟩⟩

/-! ## The two-household issuance step -/

/-- Household 1's share of saved ownership. -/
def p (s1 s2 x : ℝ) : ℝ := s1 * x / (s1 * x + s2 * (1 - x))

def U (a : ℝ → ℝ) (s1 s2 x : ℝ) : ℝ := a x * p s1 s2 x

def V (a : ℝ → ℝ) (s1 s2 x : ℝ) : ℝ := a (1 - x) * (1 - p s1 s2 x)

/-- Household 1's share after one period of issuance. -/
def F (g σ : ℝ) (a : ℝ → ℝ) (s1 s2 x : ℝ) : ℝ :=
  (p s1 s2 x + g * (σ / 2 + (1 - σ) * (U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x)))) / (1 + g)

/-- Household 2's share after one period of issuance. -/
def F2 (g σ : ℝ) (a : ℝ → ℝ) (s1 s2 x : ℝ) : ℝ :=
  ((1 - p s1 s2 x) + g * (σ / 2 + (1 - σ) * (V a s1 s2 x / (U a s1 s2 x + V a s1 s2 x)))) /
    (1 + g)

theorem F_add_F2 (g σ : ℝ) (a : ℝ → ℝ) (s1 s2 x : ℝ) (hg : 0 ≤ g)
    (hW : 0 < U a s1 s2 x + V a s1 s2 x) : F g σ a s1 s2 x + F2 g σ a s1 s2 x = 1 := by
  have h1 : 1 + g ≠ 0 := by linarith
  have h2 := hW.ne'
  unfold F F2
  field_simp
  ring

theorem den_pos (s1 s2 x : ℝ) (hs1 : 0 < s1) (hs2 : 0 < s2) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < s1 * x + s2 * (1 - x) := by
  rcases le_or_gt x (1 / 2) with h | h
  · nlinarith [mul_nonneg hs1.le hx.1]
  · nlinarith [mul_nonneg hs2.le (sub_nonneg.2 hx.2)]

theorem p_mem (s1 s2 x : ℝ) (hs1 : 0 < s1) (hs2 : 0 < s2) (hx : x ∈ Icc (0 : ℝ) 1) :
    p s1 s2 x ∈ Icc (0 : ℝ) 1 := by
  have hd := den_pos s1 s2 x hs1 hs2 hx
  refine ⟨div_nonneg (mul_nonneg hs1.le hx.1) hd.le, ?_⟩
  rw [p, div_le_one hd]
  nlinarith [mul_nonneg hs2.le (sub_nonneg.2 hx.2)]

theorem p_mono (s1 s2 : ℝ) (hs1 : 0 < s1) (hs2 : 0 < s2) :
    MonotoneOn (p s1 s2) (Icc 0 1) := by
  intro x hx y hy hxy
  have hdx := den_pos s1 s2 x hs1 hs2 hx
  have hdy := den_pos s1 s2 y hs1 hs2 hy
  rw [p, p, div_le_div_iff₀ hdx hdy]
  have := mul_le_mul_of_nonneg_left hxy (mul_pos hs1 hs2).le
  nlinarith

/-- `u / (u + v)` rises with `u` and falls with `v`. -/
theorem ratio_mono (u v u' v' : ℝ) (hu : 0 ≤ u) (hv' : 0 ≤ v') (huu : u ≤ u') (hvv : v' ≤ v)
    (h1 : 0 < u + v) (h2 : 0 < u' + v') : u / (u + v) ≤ u' / (u' + v') := by
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul huu hvv hv' (hu.trans huu)]

/-- Assumptions on the saving rates and the access rule. -/
structure Good (g σ : ℝ) (a : ℝ → ℝ) (s1 s2 : ℝ) : Prop where
  hg : 0 ≤ g
  hσ0 : 0 ≤ σ
  hσ1 : σ ≤ 1
  hs1 : 0 < s1
  hs2 : 0 < s2
  ha0 : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ a z
  hamono : MonotoneOn a (Icc 0 1)
  hW : ∀ x ∈ Icc (0 : ℝ) 1, 0 < U a s1 s2 x + V a s1 s2 x

theorem one_sub_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 1 - x ∈ Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.2 hx.2, by linarith [hx.1]⟩

theorem U_nonneg {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ U a s1 s2 x :=
  mul_nonneg (G.ha0 x hx) (p_mem s1 s2 x G.hs1 G.hs2 hx).1

theorem V_nonneg {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ V a s1 s2 x :=
  mul_nonneg (G.ha0 _ (one_sub_mem hx)) (sub_nonneg.2 (p_mem s1 s2 x G.hs1 G.hs2 hx).2)

theorem ratio_mem {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x) ∈ Icc (0 : ℝ) 1 := by
  have hW := G.hW x hx
  refine ⟨div_nonneg (U_nonneg G hx) hW.le, ?_⟩
  rw [div_le_one hW]
  linarith [V_nonneg G hx]

theorem F_mem {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) : F g σ a s1 s2 x ∈ Icc (0 : ℝ) 1 := by
  have hp := p_mem s1 s2 x G.hs1 G.hs2 hx
  have hr := ratio_mem G hx
  have h1g : 0 < 1 + g := by linarith [G.hg]
  have hq0 : 0 ≤ (1 - σ) * (U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x)) :=
    mul_nonneg (by linarith [G.hσ1]) hr.1
  have hq1 : (1 - σ) * (U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x)) ≤ 1 - σ :=
    mul_le_of_le_one_right (by linarith [G.hσ1]) hr.2
  have hm : g * (σ / 2 + (1 - σ) * (U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x))) ≤ g :=
    mul_le_of_le_one_right G.hg (by linarith [G.hσ0])
  refine ⟨div_nonneg (add_nonneg hp.1 (mul_nonneg G.hg (by linarith [G.hσ0]))) h1g.le, ?_⟩
  rw [F, div_le_one h1g]
  linarith [hp.2]

/-- **The update is nondecreasing** whenever access is nondecreasing in the household's share,
however it jumps. -/
theorem F_mono {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) :
    MonotoneOn (F g σ a s1 s2) (Icc 0 1) := by
  intro x hx y hy hxy
  have hpx := p_mem s1 s2 x G.hs1 G.hs2 hx
  have hpy := p_mem s1 s2 y G.hs1 G.hs2 hy
  have hp : p s1 s2 x ≤ p s1 s2 y := p_mono s1 s2 G.hs1 G.hs2 hx hy hxy
  have hU : U a s1 s2 x ≤ U a s1 s2 y :=
    mul_le_mul (G.hamono hx hy hxy) hp hpx.1 (G.ha0 y hy)
  have hV : V a s1 s2 y ≤ V a s1 s2 x :=
    mul_le_mul (G.hamono (one_sub_mem hy) (one_sub_mem hx) (by linarith))
      (by linarith) (by linarith [hpy.2]) (G.ha0 _ (one_sub_mem hx))
  have hr := ratio_mono _ _ _ _ (U_nonneg G hx) (V_nonneg G hy) hU hV (G.hW x hx) (G.hW y hy)
  have hq := mul_le_mul_of_nonneg_left hr (by linarith [G.hσ1] : (0 : ℝ) ≤ 1 - σ)
  have hgq := mul_le_mul_of_nonneg_left (by linarith : σ / 2 + (1 - σ) *
    (U a s1 s2 x / (U a s1 s2 x + V a s1 s2 x)) ≤ σ / 2 + (1 - σ) *
    (U a s1 s2 y / (U a s1 s2 y + V a s1 s2 y))) G.hg
  exact div_le_div_of_nonneg_right (by linarith) (by linarith [G.hg])

/-- **Existence of a long-run distribution** under a nondecreasing (possibly discontinuous)
access rule: a least and a greatest rest point, with every rest point between them. -/
theorem exists_rest_monotone {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) :
    ∃ xl ∈ Icc (0 : ℝ) 1, ∃ xh ∈ Icc (0 : ℝ) 1,
      F g σ a s1 s2 xl = xl ∧ F g σ a s1 s2 xh = xh ∧
      ∀ y ∈ Icc (0 : ℝ) 1, F g σ a s1 s2 y = y → xl ≤ y ∧ y ≤ xh := by
  obtain ⟨xl, hl, hfl, hlmin⟩ := fixed_least _ (F_mem G) (F_mono G)
  obtain ⟨xh, hh, hfh, hhmax⟩ := fixed_greatest _ (F_mem G) (F_mono G)
  exact ⟨xl, hl, xh, hh, hfl, hfh, fun y hy hfy => ⟨hlmin y hy hfy, hhmax y hy hfy⟩⟩

/-- In every long-run distribution each household holds at least `g σ / (2 (1 + g))`. -/
theorem rest_floor {g σ : ℝ} {a : ℝ → ℝ} {s1 s2 : ℝ} (G : Good g σ a s1 s2) (y : ℝ)
    (hy : y ∈ Icc (0 : ℝ) 1) (hfy : F g σ a s1 s2 y = y) :
    g * σ / (2 * (1 + g)) ≤ y ∧ g * σ / (2 * (1 + g)) ≤ 1 - y := by
  have hp := p_mem s1 s2 y G.hs1 G.hs2 hy
  have hr := ratio_mem G hy
  have h1g : 0 < 1 + g := by linarith [G.hg]
  have hq0 : 0 ≤ (1 - σ) * (U a s1 s2 y / (U a s1 s2 y + V a s1 s2 y)) :=
    mul_nonneg (by linarith [G.hσ1]) hr.1
  have hq1 : (1 - σ) * (U a s1 s2 y / (U a s1 s2 y + V a s1 s2 y)) ≤ 1 - σ :=
    mul_le_of_le_one_right (by linarith [G.hσ1]) hr.2
  have e : y * (1 + g) = p s1 s2 y + g * (σ / 2 + (1 - σ) *
      (U a s1 s2 y / (U a s1 s2 y + V a s1 s2 y))) := by
    have e0 := hfy
    unfold F at e0
    rw [div_eq_iff h1g.ne'] at e0
    linarith
  rw [div_le_iff₀ (by linarith), div_le_iff₀ (by linarith)]
  constructor
  · nlinarith [mul_nonneg G.hg hq0, hp.1]
  · nlinarith [mul_le_mul_of_nonneg_left hq1 G.hg, hp.2]

/-! ## Threshold access -/

/-- Full access at a share of at least `θb`, intensity `α0` below it. -/
def thr (θb α0 z : ℝ) : ℝ := if θb ≤ z then 1 else α0

theorem thr_mono (θb α0 : ℝ) (hα1 : α0 ≤ 1) : Monotone (thr θb α0) := by
  intro x y hxy
  unfold thr
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact hα1
  · exact le_rfl

theorem thr_ge (θb α0 z : ℝ) (hα1 : α0 ≤ 1) : α0 ≤ thr θb α0 z := by
  unfold thr
  split_ifs <;> linarith

/-- **The threshold rule has a long-run distribution** for any positive saving rates and any
intensity `α0 ∈ (0, 1]` below the threshold. -/
theorem exists_rest_threshold (g σ θb α0 s1 s2 : ℝ) (hg : 0 ≤ g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hs1 : 0 < s1) (hs2 : 0 < s2) (hα0 : 0 < α0) (hα1 : α0 ≤ 1) :
    ∃ xl ∈ Icc (0 : ℝ) 1, ∃ xh ∈ Icc (0 : ℝ) 1,
      F g σ (thr θb α0) s1 s2 xl = xl ∧ F g σ (thr θb α0) s1 s2 xh = xh ∧
      ∀ y ∈ Icc (0 : ℝ) 1, F g σ (thr θb α0) s1 s2 y = y → xl ≤ y ∧ y ≤ xh := by
  refine exists_rest_monotone ⟨hg, hσ0, hσ1, hs1, hs2,
    fun z _ => hα0.le.trans (thr_ge θb α0 z hα1), (thr_mono θb α0 hα1).monotoneOn _,
    fun x hx => ?_⟩
  have hp := p_mem s1 s2 x hs1 hs2 hx
  have h1 := mul_le_mul_of_nonneg_right (thr_ge θb α0 x hα1) hp.1
  have h2 := mul_le_mul_of_nonneg_right (thr_ge θb α0 (1 - x) hα1) (sub_nonneg.2 hp.2)
  unfold U V
  nlinarith

theorem p_eq (s x : ℝ) (hs : 0 < s) : p s s x = x := by
  unfold p
  rw [show s * x + s * (1 - x) = s by ring]
  field_simp

/-- **Strict all-or-nothing access** (`α0 = 0`): with equal saving rates and a threshold of at
most one half (so one of the two always qualifies), a long-run distribution exists. -/
theorem exists_rest_all_or_nothing (g σ θb s : ℝ) (hg : 0 ≤ g) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hs : 0 < s) (hθ : θb ≤ 1 / 2) :
    ∃ xl ∈ Icc (0 : ℝ) 1, ∃ xh ∈ Icc (0 : ℝ) 1,
      F g σ (thr θb 0) s s xl = xl ∧ F g σ (thr θb 0) s s xh = xh ∧
      ∀ y ∈ Icc (0 : ℝ) 1, F g σ (thr θb 0) s s y = y → xl ≤ y ∧ y ≤ xh := by
  refine exists_rest_monotone ⟨hg, hσ0, hσ1, hs, hs,
    fun z _ => le_trans le_rfl (thr_ge θb 0 z zero_le_one), (thr_mono θb 0 zero_le_one).monotoneOn _,
    fun x hx => ?_⟩
  unfold U V
  rw [p_eq s x hs]
  rcases le_or_gt (1 / 2) x with h | h
  · have ha : thr θb 0 x = 1 := by
      unfold thr
      split_ifs with h'
      · rfl
      · exact absurd (by linarith) h'
    rw [ha]
    nlinarith [mul_nonneg (thr_ge θb 0 (1 - x) zero_le_one) (sub_nonneg.2 hx.2)]
  · have ha : thr θb 0 (1 - x) = 1 := by
      unfold thr
      split_ifs with h'
      · rfl
      · exact absurd (by linarith) h'
    rw [ha]
    nlinarith [mul_nonneg (thr_ge θb 0 x zero_le_one) hx.1]

/-- **A poverty trap.** With issuance rate one, half of new units shared equally, equal saving,
threshold `1/2` and intensity `2/5` below it, the shares `1/3`, `1/2` and `2/3` are all long-run
distributions. -/
theorem two_rest_threshold :
    F 1 (1 / 2) (thr (1 / 2) (2 / 5)) 1 1 (1 / 3) = 1 / 3 ∧
    F 1 (1 / 2) (thr (1 / 2) (2 / 5)) 1 1 (1 / 2) = 1 / 2 ∧
    F 1 (1 / 2) (thr (1 / 2) (2 / 5)) 1 1 (2 / 3) = 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [F, U, V, p, thr]

end ThresholdRest

end

#print axioms ThresholdRest.fixed_greatest
#print axioms ThresholdRest.fixed_least
#print axioms ThresholdRest.F_add_F2
#print axioms ThresholdRest.F_mono
#print axioms ThresholdRest.exists_rest_monotone
#print axioms ThresholdRest.rest_floor
#print axioms ThresholdRest.exists_rest_threshold
#print axioms ThresholdRest.exists_rest_all_or_nothing
#print axioms ThresholdRest.two_rest_threshold
