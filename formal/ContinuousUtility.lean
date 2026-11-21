import Mathlib

/-!
# Stage 379: a continuous, monotone, quasi-concave utility for each Debreu consumer, for
# continuous excess demand

Stage 372 decomposed a continuous Walras excess demand into `n` trades `x_k` (the Debreu
decomposition) and stage 374 rationalised each trade by a monotone, quasi-concave utility
whose continuity was left open. This file closes that gap: the utility is continuous (indeed
Lipschitz in the bundle), for every continuous excess demand, not only Lipschitz ones.

Setup: prices are unit vectors `p · p = 1` with every coordinate at least `ε > 0` (`Peps ε`).
`z` is continuous on `Peps ε`, bounded by `M`, and satisfies Walras' law `p · z p = 0`.
With `A = M / ε + 1`, consumer `k`'s trade is `x_k(p) = w_k(p) (e_k − p_k p)` with weight
`w_k(p) = A p_k + z_k(p) ≥ ε`.

Construction: for a level `c`, a "piece" is any bundle within `(c − s) / K` in every coordinate
of the stage-374 upper set at an admissible level `s ≤ c`; `W_c` is the convex hull of the
pieces; `τ(y) = inf {c | y ∈ W_c}` capped at `2`; the utility is `u = −τ`, with
`K = 2 (n + 1) / ε`.

* `tau2_lip`, `util2_continuous`: `τ(y') ≤ τ(y) + K · dist y y'`, so `u` is continuous.
* `monotone_util2`: `u` is non-decreasing in every good.
* `quasiconcave2`: `u` is quasi-concave (each `W_c` is convex, `W_mono`).
* `W_below`, `tau2_trade`, `optimal2`: `u (x_k p) = −p_k` and `x_k(p)` maximises `u` on the
  budget `p · y ≤ 0`.
* `coord_ge2`, `unique2`: every other affordable bundle is strictly worse (uses only continuity
  of `x_k` at `p`).
* **`continuous_mantel_utility`**: `z = Σ_k x_k` on `Peps ε`, and each `x_k(p)` is the unique
  maximiser on `{p · y ≤ 0}` of a continuous, non-decreasing, quasi-concave utility.
* **`continuous_mantel_endowments`**: the same with endowments and non-negative consumption.
  Every consumer is endowed with `B = (M / ε + 1) + M` of every good and consumes
  `c_k(p) = B + x_k(p) ≥ 0` on `Peps ε`; then `z = Σ_k (c_k − B)` and `c_k(p)` is the unique
  maximiser of a continuous, non-decreasing, quasi-concave utility of consumption on the
  budget `p · y ≤ p · B`. This is the standard SMD set-up of individual demands from
  endowments, restricted to prices in `Peps ε` as in the textbook statement.

Honest limits (what this is NOT):
* Preferences are weakly, not strictly, monotone and not strictly convex; uniqueness of the
  maximiser holds at each `p` in `Peps ε` but comes from the construction, not from strict
  convexity of preferences.
* In `continuous_mantel_utility` bundles are net trades in `ℝ^n` with budget `p · y ≤ 0`.
  `continuous_mantel_endowments` adds endowments and shows consumption is non-negative at
  every price in `Peps ε`, but the utility is defined on all of `ℝ^n` and the maximum is over
  all of the budget set; it is in particular the maximum over non-negative bundles. The
  endowment `B` is common to all consumers and depends on `M` and `ε`.
* Prices are restricted to `Peps ε` (bounded away from the boundary); nothing is said about
  behaviour as prices approach the boundary.
* So this is a continuous-utility version of the Debreu decomposition with weak regularity, not
  the full Sonnenschein–Mantel–Debreu theorem with strictly monotone, strictly convex
  preferences. What is missing relative to that theorem is the strictness of preferences.
-/

noncomputable section

open Finset

namespace ContinuousUtility


variable {S : Type*} [Fintype S] [DecidableEq S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- The direction `e_k − p_k p`. -/
def dirk (k : S) (p : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - p k * p s

/-- Consumer `k`'s trade at price `p`, with weight `w`. -/
def trade (w : (S → ℝ) → ℝ) (k : S) (p : S → ℝ) (s : S) : ℝ := w p * dirk k p s

/-- The unit price set with positive coordinates. -/
def Cap : Set (S → ℝ) := {p | dot p p = 1 ∧ ∀ s, 0 < p s}

/-- The unit prices with every coordinate at least `ε`. -/
def Peps (ε : ℝ) : Set (S → ℝ) := {p | p ∈ Cap ∧ ∀ s, ε ≤ p s}

omit [DecidableEq S] in
theorem sq_dist (p q : S → ℝ) (hp : dot p p = 1) (hq : dot q q = 1) :
    ∑ s, (p s - q s) ^ 2 = 2 - 2 * dot p q := by
  have e : ∀ s, (p s - q s) ^ 2 = p s * p s + q s * q s - 2 * (p s * q s) := fun s => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold dot at hp hq ⊢
  rw [hp, hq]
  ring

omit [DecidableEq S] in
theorem dot_le_one (p q : S → ℝ) (hp : dot p p = 1) (hq : dot q q = 1) : dot p q ≤ 1 := by
  have h := sq_dist p q hp hq
  have h0 : 0 ≤ ∑ s, (p s - q s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  linarith

omit [DecidableEq S] in
theorem dot_nonneg_cap (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ)))
    (hq : q ∈ (Cap : Set (S → ℝ))) : 0 ≤ dot p q :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hp.2 s).le (hq.2 s).le

theorem dot_dirk (k : S) (p q : S → ℝ) : dot q (dirk k p) = q k - p k * dot q p := by
  unfold dot dirk
  have e : ∀ s, q s * ((if s = k then 1 else 0) - p k * p s) =
      (if s = k then q s else 0) - p k * (q s * p s) := fun s => by split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum]

theorem dot_trade (w : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) :
    dot q (trade w k p) = w p * (q k - p k * dot q p) := by
  rw [← dot_dirk]
  unfold dot trade
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Each consumer exhausts the budget. -/
theorem budget (w : (S → ℝ) → ℝ) (k : S) (p : S → ℝ) (hp : dot p p = 1) :
    dot p (trade w k p) = 0 := by
  rw [dot_trade, hp]
  ring

/-- Debreu's decomposition. -/
theorem decomp (A : ℝ) (z : (S → ℝ) → S → ℝ) (p : S → ℝ) (hp : dot p p = 1)
    (hw : dot p (z p) = 0) (s : S) :
    z p s = ∑ k, trade (fun q => A * q k + z q k) k p s := by
  unfold trade dirk
  have hp' : ∑ k, p k ^ 2 = 1 := by
    unfold dot at hp
    rw [← hp]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1 : ∑ k, A * p k ^ 2 = A := by rw [← Finset.mul_sum, hp', mul_one]
  have h2 : ∑ k, p k * z p k = 0 := hw
  have hs : ∑ k, (A * p k ^ 2 + p k * z p k) = A := by
    rw [Finset.sum_add_distrib, h1, h2]
    ring
  have e : ∀ k, (A * p k + z p k) * ((if s = k then 1 else 0) - p k * p s) =
      (if s = k then A * p k + z p k else 0) - p s * (A * p k ^ 2 + p k * z p k) := by
    intro k
    split_ifs with h
    · subst h
      ring
    · ring
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, hs]
  ring

omit [Fintype S] in
theorem trade_continuousOn (A : ℝ) (z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (k : S)
    (hz : ContinuousOn z P) :
    ContinuousOn (fun p => trade (fun q => A * q k + z q k) k p) P := by
  have hzk : ContinuousOn (fun q => z q k) P := (continuous_apply k).comp_continuousOn hz
  refine continuousOn_pi.2 fun s => ?_
  unfold trade dirk
  exact ((continuousOn_const.mul (continuous_apply k).continuousOn).add hzk).mul
    (continuousOn_const.sub ((continuous_apply k).continuousOn.mul
      (continuous_apply s).continuousOn))

omit [DecidableEq S] in
theorem coord_le_one (p : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (s : S) : p s ≤ 1 := by
  have h1 : p s * p s ≤ ∑ j, p j * p j :=
    Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg (p j))
      (Finset.mem_univ s)
  have h2 : ∑ j, p j * p j = 1 := hp.1
  nlinarith [hp.2 s]

theorem trade_abs (w : (S → ℝ) → ℝ) (k : S) (q : S → ℝ) (hq : q ∈ (Cap : Set (S → ℝ)))
    (W : ℝ) (hw0 : 0 ≤ w q) (hwW : w q ≤ W) (s : S) : |trade w k q s| ≤ W := by
  have hk := coord_le_one q hq k
  have hs := coord_le_one q hq s
  have hk0 := hq.2 k
  have hs0 := hq.2 s
  have hm : q k * q s ≤ 1 := by nlinarith
  have hm0 : 0 < q k * q s := mul_pos hk0 hs0
  have hd : |dirk k q s| ≤ 1 := by
    unfold dirk
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  unfold trade
  rw [abs_mul, abs_of_nonneg hw0]
  calc w q * |dirk k q s| ≤ w q * 1 := mul_le_mul_of_nonneg_left hd hw0
    _ ≤ W := by linarith

omit [DecidableEq S] in
theorem dot_ge (ν x : S → ℝ) (hν : ∀ s, 0 ≤ ν s) (W : ℝ) (hx : ∀ s, |x s| ≤ W) :
    -(W * ∑ s, ν s) ≤ dot ν x := by
  unfold dot
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 : -W ≤ x s := by linarith [(abs_le.1 (hx s)).1]
  have h2 := mul_le_mul_of_nonneg_left h1 (hν s)
  linarith

omit [DecidableEq S] in
theorem dot_mono (ν y y' : S → ℝ) (hν : ∀ s, 0 ≤ ν s) (h : ∀ s, y s ≤ y' s) :
    dot ν y ≤ dot ν y' :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hν s)

theorem dot_bump (p x : S → ℝ) (j : S) (c : ℝ) :
    dot (fun s => p s + c * (if s = j then 1 else 0)) x = dot p x + c * x j := by
  unfold dot
  have e : ∀ s, (p s + c * (if s = j then 1 else 0)) * x s =
      p s * x s + (if s = j then c * x s else 0) := by
    intro s
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib]
  simp


omit [DecidableEq S] in
theorem dot_comb (ν y1 y2 : S → ℝ) (a b : ℝ) :
    dot ν (a • y1 + b • y2) = a * dot ν y1 + b * dot ν y2 := by
  unfold dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

omit [DecidableEq S] in
/-- Half-spaces `{v : b ≤ ν · v}` are convex. -/
theorem half_convex (ν : S → ℝ) (b : ℝ) : Convex ℝ {v : S → ℝ | b ≤ dot ν v} := by
  intro y1 h1 y2 h2 a c ha hc hac
  show b ≤ dot ν (a • y1 + c • y2)
  rw [dot_comb]
  have h1' : b ≤ dot ν y1 := h1
  have h2' : b ≤ dot ν y2 := h2
  have e : a * b + c * b = b := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1' ha, mul_le_mul_of_nonneg_left h2' hc]

omit [DecidableEq S] in
theorem dot_split (ν v z : S → ℝ) : dot ν v = dot ν z + dot ν (fun i => v i - z i) := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq S] in
theorem sum_le_card (p : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) :
    ∑ s, p s ≤ (Fintype.card S : ℝ) := by
  calc ∑ s, p s ≤ ∑ _s : S, (1 : ℝ) := Finset.sum_le_sum fun s _ => coord_le_one p hp s
    _ = (Fintype.card S : ℝ) := by simp

theorem sum_bump (p : S → ℝ) (j : S) (c : ℝ) :
    ∑ s, (p s + c * (if s = j then 1 else 0)) = ∑ s, p s + c := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem box_bound (N K wmin d : ℝ) (hK0 : 0 < K) (hK : 2 * (N + 1) ≤ K * wmin) (hd : 0 ≤ d) :
    d / K * (N + 1) ≤ d * wmin / 2 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK0]
  nlinarith [mul_le_mul_of_nonneg_left hK hd]

/-! ## The upper contour sets of stage 374 -/

/-- The lowest value of `ν · x(q)` over the prices with `q_k ≤ t`. -/
def mval (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (t : ℝ) (ν : S → ℝ) : ℝ :=
  sInf ((fun q => dot ν (trade w k q)) '' {q | q ∈ P ∧ q k ≤ t})

/-- The smallest upper contour set at level `t` (stage 374). -/
def Up (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (t : ℝ) : Set (S → ℝ) :=
  {y | ∀ ν : S → ℝ, (∀ s, 0 ≤ ν s) → mval P w k t ν ≤ dot ν y}

/-! ## The thickened family and the continuous utility -/

/-- Pieces at level `c`: points within `(c − s) / K` (in every coordinate) of the stage-374 set
at an admissible level `s ≤ c`. Moving away from `C_s` costs level at the fixed rate `K`. -/
def Piece (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (K c : ℝ) : Set (S → ℝ) :=
  {y | ∃ s, (∃ q ∈ P, q k ≤ s) ∧ s ≤ c ∧ ∃ z ∈ Up P w k s, ∀ i, |y i - z i| ≤ (c - s) / K}

/-- The upper contour set at level `c`: the convex hull of the pieces. -/
def Wc (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (K c : ℝ) : Set (S → ℝ) :=
  convexHull ℝ (Piece P w k K c)

/-- The levels a bundle reaches. -/
def Lev (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (K : ℝ) (y : S → ℝ) : Set ℝ :=
  {c | y ∈ Wc P w k K c}

/-- The least level of a bundle, capped at `2`. -/
def tau2 (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (K : ℝ) (y : S → ℝ) : ℝ :=
  sInf (insert (2 : ℝ) (Lev P w k K y))

/-- The utility. -/
def util2 (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (K : ℝ) (y : S → ℝ) : ℝ :=
  -tau2 P w k K y

section Generic

variable (P : Set (S → ℝ)) (hP : P ⊆ Cap) (w : (S → ℝ) → ℝ) (wmin wmax : ℝ)
  (hwmin : 0 < wmin) (hw : ∀ q ∈ P, wmin ≤ w q ∧ w q ≤ wmax) (k : S) (K : ℝ) (hK0 : 0 < K)
  (hK : 2 * ((Fintype.card S : ℝ) + 1) ≤ K * wmin)

include hP hwmin hw in
theorem bdd (t : ℝ) (ν : S → ℝ) (hν : ∀ s, 0 ≤ ν s) :
    BddBelow ((fun q => dot ν (trade w k q)) '' {q | q ∈ P ∧ q k ≤ t}) := by
  refine ⟨-(wmax * ∑ s, ν s), ?_⟩
  rintro _ ⟨q, ⟨hqP, -⟩, rfl⟩
  exact dot_ge ν _ hν wmax fun s =>
    trade_abs w k q (hP hqP) wmax (by linarith [(hw q hqP).1]) (hw q hqP).2 s

theorem le_mval (t : ℝ) (ν : S → ℝ) (b : ℝ) (q0 : S → ℝ) (hq0 : q0 ∈ P) (hq0t : q0 k ≤ t)
    (h : ∀ q ∈ P, q k ≤ t → b ≤ dot ν (trade w k q)) : b ≤ mval P w k t ν := by
  unfold mval
  apply le_csInf
    ((Set.nonempty_of_mem (show q0 ∈ {q | q ∈ P ∧ q k ≤ t} from ⟨hq0, hq0t⟩)).image _)
  rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
  exact h q hq hqt

include hP hwmin hw in
theorem mem_Up_self (p : S → ℝ) (hp : p ∈ P) : trade w k p ∈ Up P w k (p k) :=
  fun ν hν => csInf_le (bdd P hP w wmin wmax hwmin hw k (p k) ν hν) ⟨p, ⟨hp, le_rfl⟩, rfl⟩

theorem dot_lower (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (hq : q ∈ (Cap : Set (S → ℝ)))
    (hw0 : 0 ≤ w q) : w q * (p k - q k) ≤ dot p (trade w k q) := by
  rw [dot_trade]
  have hc := dot_le_one p q hp.1 hq.1
  have hqk := hq.2 k
  have h1 : q k * dot p q ≤ q k := mul_le_of_le_one_right hqk.le hc
  exact mul_le_mul_of_nonneg_left (by linarith) hw0

/-- A two-sided lower bound for `p · x(q)` when `q_k ≤ s ≤ p_k + δ`. -/
theorem dot_lower3 (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (hq : q ∈ (Cap : Set (S → ℝ)))
    (s δ : ℝ) (hqs : q k ≤ s) (hsp : s ≤ p k + δ) (hδ : 0 ≤ δ) (hwq : wmin ≤ w q)
    (hwq' : w q ≤ wmax) (hwmin' : 0 ≤ wmin) :
    wmin * p k * (1 - dot p q) / 2 + wmin * (p k - s) / 2 - wmax * δ ≤ dot p (trade w k q) := by
  rw [dot_trade]
  have hc1 := dot_le_one p q hp.1 hq.1
  have hc0 := dot_nonneg_cap p q hp hq
  have hpk := hp.2 k
  have hqk := hq.2 k
  set c := dot p q
  have hw0 : 0 ≤ w q := by linarith
  have hA : 0 ≤ p k * (1 - c) := mul_nonneg hpk.le (by linarith)
  rcases le_total (q k) (p k) with h | h
  · have h1 : p k * (1 - c) ≤ p k - q k * c := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.2 h)]
    have h2 : p k - s ≤ p k - q k * c := by
      nlinarith [mul_le_mul_of_nonneg_left hc1 hqk.le]
    have hB : 0 ≤ p k - q k * c := by linarith
    have e1 := mul_le_mul_of_nonneg_right hwq hB
    have e2 := mul_le_mul_of_nonneg_left h1 hwmin'
    have e3 := mul_le_mul_of_nonneg_left h2 hwmin'
    have e4 : 0 ≤ wmax * δ := mul_nonneg (by linarith) hδ
    nlinarith
  · have hD0 : 0 ≤ c * (q k - p k) := mul_nonneg hc0 (by linarith)
    have hD : c * (q k - p k) ≤ δ := by
      nlinarith [mul_le_mul_of_nonneg_right hc1 (sub_nonneg.2 h)]
    have e1 := mul_le_mul_of_nonneg_right hwq hA
    have e2 : w q * (c * (q k - p k)) ≤ wmax * δ := mul_le_mul hwq' hD hD0 (by linarith)
    have e3 : wmin * (p k - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hwmin' (by linarith)
    have e4 : 0 ≤ wmin * (p k * (1 - c)) := mul_nonneg hwmin' hA
    have e5 : w q * (p k - q k * c) = w q * (p k * (1 - c)) - w q * (c * (q k - p k)) := by ring
    nlinarith

omit [DecidableEq S] in
/-- Far from `p`, the angle gap is at least quadratic in the distance. -/
theorem gap (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (hq : q ∈ (Cap : Set (S → ℝ))) (r : ℝ)
    (hr : 0 < r) (h : r ≤ dist q p) : r ^ 2 / 2 ≤ 1 - dot p q := by
  have hs := sq_dist p q hp.1 hq.1
  obtain ⟨s, hs'⟩ : ∃ s, r ≤ dist (q s) (p s) := by
    by_contra hc
    push Not at hc
    exact absurd ((dist_pi_lt_iff hr).2 hc) (not_lt.2 h)
  rw [Real.dist_eq, abs_sub_comm] at hs'
  have h1 : (p s - q s) ^ 2 ≤ ∑ j, (p j - q j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (p j - q j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ s)
  have h3 := mul_le_mul hs' hs' hr.le (abs_nonneg _)
  rw [abs_mul_abs_self] at h3
  nlinarith

include hP in
/-- Every level reached is non-negative. -/
theorem W_nonneg (c : ℝ) (y : S → ℝ) (hy : y ∈ Wc P w k K c) : 0 ≤ c := by
  have hsub : Piece P w k K c ⊆ {_u | 0 ≤ c} := by
    rintro v ⟨s, ⟨q0, hq0, hq0s⟩, hsc, -⟩
    show 0 ≤ c
    linarith [(hP hq0).2 k]
  have hconv : Convex ℝ {_u : S → ℝ | 0 ≤ c} := by
    intro _ h _ _ _ _ _ _ _
    exact h
  exact convexHull_min hsub hconv hy

include hP in
theorem lev_bdd (y : S → ℝ) : BddBelow (insert (2 : ℝ) (Lev P w k K y)) := by
  refine ⟨0, ?_⟩
  rintro t (rfl | ht)
  · norm_num
  · exact W_nonneg P hP w k K t y ht

include hP in
theorem tau2_le_of_mem (y : S → ℝ) (c : ℝ) (hc : y ∈ Wc P w k K c) : tau2 P w k K y ≤ c :=
  csInf_le (lev_bdd P hP w k K y) (Set.mem_insert_of_mem _ hc)

include hP in
theorem tau2_le_two (y : S → ℝ) : tau2 P w k K y ≤ 2 :=
  csInf_le (lev_bdd P hP w k K y) (Set.mem_insert _ _)

include hK0 in
/-- **The family grows with the level.** -/
theorem W_mono (c c' : ℝ) (h : c ≤ c') : Wc P w k K c ⊆ Wc P w k K c' := by
  apply convexHull_mono
  rintro v ⟨s, hq, hsc, z, hz, hvz⟩
  exact ⟨s, hq, hsc.trans h, z, hz, fun i =>
    (hvz i).trans (div_le_div_of_nonneg_right (by linarith) hK0.le)⟩

/-- **Each upper contour set is convex.** -/
theorem W_convex (c : ℝ) : Convex ℝ (Wc P w k K c) := convex_convexHull ℝ _

/-- Moving every piece by `v` moves the whole hull by `v`. -/
theorem W_shift (c c' : ℝ) (v : S → ℝ)
    (h : ∀ u ∈ Piece P w k K c, u + v ∈ Piece P w k K c') (y : S → ℝ)
    (hy : y ∈ Wc P w k K c) : y + v ∈ Wc P w k K c' := by
  have hconv : Convex ℝ {u : S → ℝ | u + v ∈ Wc P w k K c'} := by
    intro u1 h1 u2 h2 a b ha hb hab
    have e : a • u1 + b • u2 + v = a • (u1 + v) + b • (u2 + v) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -(v i) * hab
    show a • u1 + b • u2 + v ∈ Wc P w k K c'
    rw [e]
    exact (convex_convexHull ℝ _) h1 h2 ha hb hab
  have hsub : Piece P w k K c ⊆ {u : S → ℝ | u + v ∈ Wc P w k K c'} :=
    fun u hu => subset_convexHull ℝ _ (h u hu)
  exact convexHull_min hsub hconv hy

include hK0 in
/-- A move of at most `d` in every coordinate raises the level by at most `K d`. -/
theorem W_move (c d : ℝ) (hd : 0 ≤ d) (v : S → ℝ) (hv : ∀ i, |v i| ≤ d) (y : S → ℝ)
    (hy : y ∈ Wc P w k K c) : y + v ∈ Wc P w k K (c + K * d) := by
  refine W_shift P w k K c _ v (fun u hu => ?_) y hy
  obtain ⟨s, hq, hsc, z, hz, huz⟩ := hu
  have hKd : 0 ≤ K * d := mul_nonneg hK0.le hd
  have e : (c + K * d - s) / K = (c - s) / K + d := by
    rw [show c + K * d - s = (c - s) + K * d by ring, add_div, mul_div_cancel_left₀ _ hK0.ne']
  refine ⟨s, hq, by linarith, z, hz, fun i => ?_⟩
  rw [e]
  have a1 := abs_le.1 (huz i)
  have a2 := abs_le.1 (hv i)
  rw [abs_le]
  simp only [Pi.add_apply]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

include hP hK0 in
/-- **The level is Lipschitz.** -/
theorem tau2_lip (y y' : S → ℝ) : tau2 P w k K y' ≤ tau2 P w k K y + K * dist y y' := by
  have hd0 : 0 ≤ dist y y' := dist_nonneg
  have hKd : 0 ≤ K * dist y y' := mul_nonneg hK0.le hd0
  have hv : ∀ i, |(y' - y) i| ≤ dist y y' := fun i => by
    have := dist_le_pi_dist y' y i
    rw [Real.dist_eq, dist_comm] at this
    simpa using this
  have key : tau2 P w k K y' - K * dist y y' ≤ tau2 P w k K y := by
    apply le_csInf ⟨2, Set.mem_insert _ _⟩
    rintro a (rfl | ha)
    · linarith [tau2_le_two P hP w k K y']
    · have hm := W_move P w k K hK0 a (dist y y') hd0 (y' - y) hv y ha
      rw [show y + (y' - y) = y' by abel] at hm
      linarith [tau2_le_of_mem P hP w k K y' _ hm]
  linarith

include hP hK0 in
/-- **The utility is continuous** (indeed `K`-Lipschitz). -/
theorem util2_continuous : Continuous (util2 P w k K) := by
  rw [Metric.continuous_iff]
  intro b γ hγ
  refine ⟨γ / K, div_pos hγ hK0, fun a hab => ?_⟩
  have h1 := tau2_lip P hP w k K hK0 a b
  have h2 := tau2_lip P hP w k K hK0 b a
  rw [dist_comm] at h2
  have h3 : K * dist a b < γ := by
    have := mul_lt_mul_of_pos_left hab hK0
    rwa [mul_div_cancel₀ _ hK0.ne'] at this
  rw [Real.dist_eq]
  unfold util2
  rw [abs_lt]
  constructor <;> linarith

include hP in
/-- **The utility is non-decreasing in every good.** -/
theorem monotone_util2 (y y' : S → ℝ) (h : ∀ s, y s ≤ y' s) :
    util2 P w k K y ≤ util2 P w k K y' := by
  have hsub : Lev P w k K y ⊆ Lev P w k K y' := by
    intro c hc
    have hm := W_shift P w k K c c (y' - y) (fun u hu => ?_) y hc
    · show y' ∈ Wc P w k K c
      rwa [show y + (y' - y) = y' by abel] at hm
    obtain ⟨s, hq, hsc, z, hz, huz⟩ := hu
    refine ⟨s, hq, hsc, z + (y' - y), fun ν hν => ?_, fun i => ?_⟩
    · exact (hz ν hν).trans (dot_mono ν z _ hν fun i => by
        simp only [Pi.add_apply, Pi.sub_apply]
        linarith [h i])
    · have e : (u + (y' - y)) i - (z + (y' - y)) i = u i - z i := by
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [e]
      exact huz i
  have : tau2 P w k K y' ≤ tau2 P w k K y :=
    csInf_le_csInf (lev_bdd P hP w k K y') ⟨2, Set.mem_insert _ _⟩
      (Set.insert_subset_insert hsub)
  unfold util2
  linarith

include hP hK0 in
/-- **The utility is quasi-concave**: the preference is convex. -/
theorem quasiconcave2 : QuasiconcaveOn ℝ Set.univ (util2 P w k K) := by
  intro r y1 h1 y2 h2 a b ha hb hab
  refine ⟨Set.mem_univ _, ?_⟩
  have h1' : tau2 P w k K y1 ≤ -r := by
    have := h1.2
    unfold util2 at this
    linarith
  have h2' : tau2 P w k K y2 ≤ -r := by
    have := h2.2
    unfold util2 at this
    linarith
  suffices hs : tau2 P w k K (a • y1 + b • y2) ≤ -r by
    show r ≤ util2 P w k K (a • y1 + b • y2)
    unfold util2
    linarith
  by_contra hc
  push Not at hc
  set s' := (-r + tau2 P w k K (a • y1 + b • y2)) / 2 with hs'
  have hs1 : tau2 P w k K y1 < s' := by rw [hs']; linarith
  have hs2 : tau2 P w k K y2 < s' := by rw [hs']; linarith
  have hlt : s' < tau2 P w k K (a • y1 + b • y2) := by rw [hs']; linarith
  obtain ⟨a1, ha1, ha1s⟩ := exists_lt_of_csInf_lt ⟨2, Set.mem_insert _ _⟩ hs1
  obtain ⟨a2, ha2, ha2s⟩ := exists_lt_of_csInf_lt ⟨2, Set.mem_insert _ _⟩ hs2
  have htwo := tau2_le_two P hP w k K (a • y1 + b • y2)
  rcases ha1 with rfl | hy1
  · linarith
  rcases ha2 with rfl | hy2
  · linarith
  have hm : a • y1 + b • y2 ∈ Wc P w k K (max a1 a2) :=
    W_convex P w k K (max a1 a2) (W_mono P w k K hK0 a1 _ (le_max_left _ _) hy1)
      (W_mono P w k K hK0 a2 _ (le_max_right _ _) hy2) ha hb hab
  have := tau2_le_of_mem P hP w k K _ _ hm
  have := max_lt ha1s ha2s
  linarith

include hP hwmin hw hK0 hK in
/-- **Below a price's own level nothing affordable is reached**, uniformly: every point of
`W_c` with `c < p_k` lies in the half-space `p · v ≥ wmin (p_k − c) / 2`. -/
theorem W_below (p : S → ℝ) (hp : p ∈ P) (c : ℝ) (hcp : c < p k) :
    Wc P w k K c ⊆ {v | wmin * (p k - c) / 2 ≤ dot p v} := by
  apply convexHull_min _ (half_convex p _)
  rintro v ⟨s, ⟨q0, hq0, hq0s⟩, hsc, z, hz, hvz⟩
  have hpC := hP hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hpC.2 i).le
  have hm : wmin * (p k - s) ≤ mval P w k s p := by
    refine le_mval P w k s p _ q0 hq0 hq0s fun q hq hqs => ?_
    have hw' := hw q hq
    have h1 := dot_lower w k p q hpC (hP hq) (by linarith)
    have h2 : wmin * (p k - s) ≤ w q * (p k - q k) :=
      mul_le_mul hw'.1 (by linarith) (by linarith) (by linarith)
    linarith
  have hzp := hz p hp0
  have hsplit := dot_split p v z
  have hbox := dot_ge p (fun i => v i - z i) hp0 ((c - s) / K) hvz
  have hsum := sum_le_card p hpC
  have hb1 : (c - s) / K * ∑ i, p i ≤ (c - s) / K * ((Fintype.card S : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hK0.le)
  have hb2 := box_bound (Fintype.card S : ℝ) K wmin (c - s) hK0 hK (by linarith)
  have hb3 : wmin * (c - s) ≤ wmin * (p k - s) := mul_le_mul_of_nonneg_left (by linarith) hwmin.le
  show wmin * (p k - c) / 2 ≤ dot p v
  nlinarith

include hP hwmin hw hK0 hK in
/-- An affordable bundle has level at least `p_k`. -/
theorem tau2_ge (p : S → ℝ) (hp : p ∈ P) (y : S → ℝ) (hy : dot p y ≤ 0) :
    p k ≤ tau2 P w k K y := by
  apply le_csInf ⟨2, Set.mem_insert _ _⟩
  rintro t (rfl | ht)
  · linarith [coord_le_one p (hP hp) k]
  · by_contra h
    push Not at h
    have h2 : wmin * (p k - t) / 2 ≤ dot p y :=
      W_below P hP w wmin wmax hwmin hw k K hK0 hK p hp t h ht
    nlinarith [mul_pos hwmin (sub_pos.2 h)]

include hP hwmin hw in
theorem trade_mem_W (p : S → ℝ) (hp : p ∈ P) : trade w k p ∈ Wc P w k K (p k) :=
  subset_convexHull ℝ _ ⟨p k, ⟨p, hp, le_rfl⟩, le_rfl, trade w k p,
    mem_Up_self P hP w wmin wmax hwmin hw k p hp, fun i => by simp⟩

include hP hwmin hw hK0 hK in
/-- **The level of a chosen trade is its own price coordinate.** -/
theorem tau2_trade (p : S → ℝ) (hp : p ∈ P) : tau2 P w k K (trade w k p) = p k :=
  le_antisymm (tau2_le_of_mem P hP w k K _ _ (trade_mem_W P hP w wmin wmax hwmin hw k K p hp))
    (tau2_ge P hP w wmin wmax hwmin hw k K hK0 hK p hp _ (le_of_eq (budget w k p (hP hp).1)))

include hP hwmin hw hK0 hK in
/-- **Each trade maximises the utility on its budget.** -/
theorem optimal2 (p : S → ℝ) (hp : p ∈ P) (y : S → ℝ) (hy : dot p y ≤ 0) :
    util2 P w k K y ≤ util2 P w k K (trade w k p) := by
  unfold util2
  rw [tau2_trade P hP w wmin wmax hwmin hw k K hK0 hK p hp]
  linarith [tau2_ge P hP w wmin wmax hwmin hw k K hK0 hK p hp y hy]

set_option maxHeartbeats 1000000 in
include hP hwmin hw hK0 hK in
/-- **The tilt argument, through the hull.** If `p · y ≤ 0` and `y` has level at most `p_k`,
then `σ y_j ≥ σ x_j(p)` for `σ = ±1`. Only continuity of `x` at `p` is used. -/
theorem coord_ge2 (p : S → ℝ) (hp : p ∈ P)
    (hc : ContinuousWithinAt (fun q => trade w k q) P p) (y : S → ℝ) (hy : dot p y ≤ 0)
    (ht : tau2 P w k K y ≤ p k) (j : S) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    σ * trade w k p j ≤ σ * y j := by
  have hpC := hP hp
  have hpk : 0 < p k := hpC.2 k
  have hpj : 0 < p j := hpC.2 j
  have hpj1 := coord_le_one p hpC j
  have hwp := hw p hp
  have hwmax : 0 < wmax := by linarith
  refine le_of_forall_pos_le_add fun γ hγ => ?_
  obtain ⟨r, hr, hcont⟩ := Metric.continuousWithinAt_iff.1 hc (γ / 2) (by positivity)
  set η := min (p j / 2) (wmin * p k * r ^ 2 / (16 * (wmax + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ p j / 2 := min_le_left _ _
  have hη2 : η ≤ wmin * p k * r ^ 2 / (16 * (wmax + 1)) := min_le_right _ _
  set δ := min (1 / 2) (η * γ / (2 * (wmax + wmin + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ η * γ / (2 * (wmax + wmin + 1)) := min_le_right _ _
  have hδ3 : δ * (2 * (wmax + wmin + 1)) ≤ η * γ := by
    rw [le_div_iff₀ (by positivity)] at hδ2
    exact hδ2
  have hpk1 := coord_le_one p hpC k
  obtain ⟨c, hcI, hcs⟩ := exists_lt_of_csInf_lt (s := insert (2 : ℝ) (Lev P w k K y))
    ⟨2, Set.mem_insert _ _⟩ (show tau2 P w k K y < p k + δ by linarith)
  rcases hcI with rfl | hyW
  · linarith
  -- the tilted normal
  set ν : S → ℝ := fun s => p s + (η * σ) * (if s = j then 1 else 0) with hν
  have hν0 : ∀ s, 0 ≤ ν s := by
    intro s
    show 0 ≤ p s + (η * σ) * (if s = j then 1 else 0)
    split_ifs with h
    · subst h
      rcases hσ with rfl | rfl <;> nlinarith
    · simp only [mul_zero, add_zero]
      exact (hpC.2 s).le
  have hνsum : ∑ s, ν s ≤ (Fintype.card S : ℝ) + 1 := by
    show ∑ s, (p s + (η * σ) * (if s = j then 1 else 0)) ≤ _
    rw [sum_bump]
    have := sum_le_card p hpC
    have : η * σ ≤ 1 := by rcases hσ with rfl | rfl <;> linarith
    linarith
  have hxpj : |trade w k p j| ≤ wmax :=
    trade_abs w k p hpC wmax (by linarith) hwp.2 j
  -- every piece lies in one half-space
  have hH : Piece P w k K c ⊆ {v | η * σ * trade w k p j - η * γ ≤ dot ν v} := by
    rintro v ⟨s, ⟨q0, hq0, hq0s⟩, hsc, z, hz, hvz⟩
    have hm : wmin * (p k - s) / 2 - wmax * δ + η * σ * trade w k p j - η * (γ / 2) ≤
        mval P w k s ν := by
      refine le_mval P w k s ν _ q0 hq0 hq0s fun q hq hqs => ?_
      have hqC := hP hq
      have hwq := hw q hq
      rw [hν, dot_bump]
      have hL := dot_lower3 w wmin wmax k p q hpC hqC s δ hqs (by linarith) hδ0.le hwq.1 hwq.2
        hwmin.le
      have hc1 := dot_le_one p q hpC.1 hqC.1
      by_cases hd : dist q p < r
      · have h1 := hcont hq hd
        have h2 : |trade w k q j - trade w k p j| < γ / 2 := by
          have := (dist_le_pi_dist (trade w k q) (trade w k p) j).trans_lt h1
          rwa [Real.dist_eq] at this
        have h3 : σ * trade w k p j - γ / 2 ≤ σ * trade w k q j := by
          rcases hσ with rfl | rfl
          · linarith [(abs_lt.1 h2).1]
          · linarith [(abs_lt.1 h2).2]
        have h4 : 0 ≤ wmin * p k * (1 - dot p q) :=
          mul_nonneg (mul_nonneg hwmin.le hpk.le) (by linarith)
        have h5 := mul_le_mul_of_nonneg_left h3 hη0.le
        linarith
      · push Not at hd
        have hg := gap p q hpC hqC r hr hd
        have hxq : |trade w k q j| ≤ wmax :=
          trade_abs w k q hqC wmax (by linarith) hwq.2 j
        have h1 : -wmax ≤ σ * trade w k q j := by
          rcases hσ with rfl | rfl
          · linarith [(abs_le.1 hxq).1]
          · linarith [(abs_le.1 hxq).2]
        have h2 : σ * trade w k p j ≤ wmax := by
          rcases hσ with rfl | rfl
          · linarith [(abs_le.1 hxpj).2]
          · linarith [(abs_le.1 hxpj).1]
        have h3 : wmin * p k * (r ^ 2 / 2) ≤ wmin * p k * (1 - dot p q) :=
          mul_le_mul_of_nonneg_left hg (mul_nonneg hwmin.le hpk.le)
        have h4 : η * (16 * (wmax + 1)) ≤ wmin * p k * r ^ 2 := by
          rw [le_div_iff₀ (by positivity)] at hη2
          exact hη2
        have h5 := mul_le_mul_of_nonneg_left h1 hη0.le
        have h6 := mul_le_mul_of_nonneg_left h2 hη0.le
        have h7 := mul_pos hη0 hγ
        have hA : wmin * p k * r ^ 2 / 4 ≤ wmin * p k * (1 - dot p q) / 2 := by
          linarith [h3]
        have hB : 2 * (η * wmax) + 4 * η ≤ wmin * p k * r ^ 2 / 4 := by
          nlinarith [h4, mul_nonneg hη0.le hwmax.le]
        have hD : -2 * (η * wmax) ≤ η * (σ * trade w k q j) - η * (σ * trade w k p j) := by
          linarith [h5, h6]
        linarith [hA, hB, hD, h7, hη0.le]
    have hzν := hz ν hν0
    have hsplit := dot_split ν v z
    have hbox := dot_ge ν (fun i => v i - z i) hν0 ((c - s) / K) hvz
    have hb1 : (c - s) / K * ∑ i, ν i ≤ (c - s) / K * ((Fintype.card S : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hνsum (div_nonneg (by linarith) hK0.le)
    have hb2 := box_bound (Fintype.card S : ℝ) K wmin (c - s) hK0 hK (by linarith)
    have hb3 : wmin * (c - p k) ≤ wmin * δ := mul_le_mul_of_nonneg_left (by linarith) hwmin.le
    have hb4 : wmax * δ + wmin * δ / 2 ≤ η * γ / 2 := by
      linarith [mul_nonneg hwmin.le hδ0.le, hδ0]
    show η * σ * trade w k p j - η * γ ≤ dot ν v
    linarith
  have hyH : η * σ * trade w k p j - η * γ ≤ dot ν y := convexHull_min hH (half_convex ν _) hyW
  rw [hν, dot_bump] at hyH
  have key : η * (σ * trade w k p j) ≤ η * (σ * y j + γ) := by linarith
  exact le_of_mul_le_mul_left key hη0

include hP hwmin hw hK0 hK in
/-- **The trade is the unique maximiser.** If `x` is continuous within `P` at `p`, every
affordable bundle other than `x(p)` has strictly lower utility. -/
theorem unique2 (p : S → ℝ) (hp : p ∈ P)
    (hc : ContinuousWithinAt (fun q => trade w k q) P p) (y : S → ℝ) (hy : dot p y ≤ 0)
    (hne : y ≠ trade w k p) : util2 P w k K y < util2 P w k K (trade w k p) := by
  rcases lt_or_eq_of_le (optimal2 P hP w wmin wmax hwmin hw k K hK0 hK p hp y hy) with h | h
  · exact h
  exfalso
  apply hne
  have ht : tau2 P w k K y ≤ p k := by
    have := tau2_trade P hP w wmin wmax hwmin hw k K hK0 hK p hp
    unfold util2 at h
    linarith
  funext j
  have a := coord_ge2 P hP w wmin wmax hwmin hw k K hK0 hK p hp hc y hy ht j 1 (Or.inl rfl)
  have b := coord_ge2 P hP w wmin wmax hwmin hw k K hK0 hK p hp hc y hy ht j (-1) (Or.inr rfl)
  linarith

end Generic

/-! ## Assembly -/

/-- **A continuous, monotone, quasi-concave utility for each Debreu consumer, for continuous
`z`.** Let `z` be Walras on the unit prices with every coordinate at least `ε`, continuous and
bounded by `M` there. With `A = M / ε + 1`, `z` is the sum of the `n` trades `x_k`, and for each
`k` there is a real-valued utility that is continuous, non-decreasing in every good and
quasi-concave, such that at every such price `p`, `x_k(p)` maximises it on the budget
`p · y ≤ 0` and every other affordable bundle is strictly worse. -/
theorem continuous_mantel_utility (z : (S → ℝ) → S → ℝ) (ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hW : ∀ p ∈ (Peps ε : Set (S → ℝ)), dot p (z p) = 0)
    (hz : ∀ k, ∀ q ∈ (Peps ε : Set (S → ℝ)), |z q k| ≤ M)
    (hzc : ContinuousOn z (Peps ε)) :
    let x : S → (S → ℝ) → S → ℝ := fun k => trade (fun q => (M / ε + 1) * q k + z q k) k
    (∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ s, z p s = ∑ k, x k p s) ∧
    ∀ k, ∃ u : (S → ℝ) → ℝ,
      Continuous u ∧
      (∀ y y' : S → ℝ, (∀ s, y s ≤ y' s) → u y ≤ u y') ∧
      QuasiconcaveOn ℝ Set.univ u ∧
      ∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ y, dot p y ≤ 0 →
        u y ≤ u (x k p) ∧ (y ≠ x k p → u y < u (x k p)) := by
  intro x
  have hPC : (Peps ε : Set (S → ℝ)) ⊆ Cap := fun p hp => hp.1
  refine ⟨fun p hp s => decomp (M / ε + 1) z p hp.1.1 (hW p hp) s, fun k => ?_⟩
  set w : (S → ℝ) → ℝ := fun q => (M / ε + 1) * q k + z q k with hw
  have hA : 0 < M / ε + 1 := by positivity
  have hwb : ∀ q ∈ (Peps ε : Set (S → ℝ)), ε ≤ w q ∧ w q ≤ (M / ε + 1) + M := by
    intro q hq
    have hqk := hq.2 k
    have hq1 := coord_le_one q hq.1 k
    have hzq := abs_le.1 (hz k q hq)
    have e : M / ε * ε = M := div_mul_cancel₀ M hε.ne'
    refine ⟨?_, ?_⟩
    · have : (M / ε + 1) * ε ≤ (M / ε + 1) * q k := mul_le_mul_of_nonneg_left hqk hA.le
      rw [hw]
      nlinarith
    · have : (M / ε + 1) * q k ≤ (M / ε + 1) * 1 := mul_le_mul_of_nonneg_left hq1 hA.le
      rw [hw]
      linarith
  set K : ℝ := 2 * ((Fintype.card S : ℝ) + 1) / ε with hKdef
  have hK0 : 0 < K := by positivity
  have hK : 2 * ((Fintype.card S : ℝ) + 1) ≤ K * ε := le_of_eq (div_mul_cancel₀ _ hε.ne').symm
  refine ⟨util2 (Peps ε) w k K, util2_continuous (Peps ε) hPC w k K hK0,
    fun y y' h => monotone_util2 (Peps ε) hPC w k K y y' h,
    quasiconcave2 (Peps ε) hPC w k K hK0, fun p hp y hy => ⟨?_, fun hne => ?_⟩⟩
  · exact optimal2 (Peps ε) hPC w ε _ hε hwb k K hK0 hK p hp y hy
  · exact unique2 (Peps ε) hPC w ε _ hε hwb k K hK0 hK p hp
      (trade_continuousOn (M / ε + 1) z (Peps ε) k hzc p hp) y hy hne

/-- **Endowments and nonnegative consumption.** Give every household the endowment `B` of every
good, with `B = (M / ε + 1) + M`. Household `k` consumes `c k p = B + x k p`, which is
nonnegative at every price in `Peps ε`; the economy's excess demand is `z`; and `c k p` is the
unique maximiser of a continuous, monotone, quasiconcave utility of consumption on the budget
set `p · y ≤ p · B`. -/
theorem continuous_mantel_endowments (z : (S → ℝ) → S → ℝ) (ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hW : ∀ p ∈ (Peps ε : Set (S → ℝ)), dot p (z p) = 0)
    (hz : ∀ k, ∀ q ∈ (Peps ε : Set (S → ℝ)), |z q k| ≤ M)
    (hzc : ContinuousOn z (Peps ε)) :
    let B : ℝ := (M / ε + 1) + M
    let x : S → (S → ℝ) → S → ℝ := fun k => trade (fun q => (M / ε + 1) * q k + z q k) k
    let c : S → (S → ℝ) → S → ℝ := fun k p s => B + x k p s
    (∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ s, z p s = ∑ k, (c k p s - B)) ∧
    (∀ k, ∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ s, 0 ≤ c k p s) ∧
    ∀ k, ∃ U : (S → ℝ) → ℝ,
      Continuous U ∧
      (∀ y y' : S → ℝ, (∀ s, y s ≤ y' s) → U y ≤ U y') ∧
      QuasiconcaveOn ℝ Set.univ U ∧
      ∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ y, dot p y ≤ dot p (fun _ => B) →
        U y ≤ U (c k p) ∧ (y ≠ c k p → U y < U (c k p)) := by
  intro B x c
  obtain ⟨hdec, hu⟩ := continuous_mantel_utility z ε M hε hM hW hz hzc
  have hcx : ∀ k p, (fun s => c k p s - B) = x k p := by
    intro k p; funext s; simp only [c]; ring
  refine ⟨fun p hp s => by simp only [c, add_sub_cancel_left]; exact hdec p hp s, ?_, ?_⟩
  · intro k p hp s
    have hA : 0 < M / ε + 1 := by positivity
    have hqk := hp.2 k
    have hq1 := coord_le_one p hp.1 k
    have hzq := abs_le.1 (hz k p hp)
    have e : M / ε * ε = M := div_mul_cancel₀ M hε.ne'
    have h1 : (M / ε + 1) * ε ≤ (M / ε + 1) * p k := mul_le_mul_of_nonneg_left hqk hA.le
    have h2 : (M / ε + 1) * p k ≤ (M / ε + 1) * 1 := mul_le_mul_of_nonneg_left hq1 hA.le
    have hb := trade_abs (fun q => (M / ε + 1) * q k + z q k) k p hp.1 B
      (by nlinarith) (by simp only [B]; linarith) s
    have := (abs_le.1 hb).1
    simp only [c, x]
    linarith
  · intro k
    obtain ⟨u, huc, hum, huq, huo⟩ := hu k
    have hsc : Continuous fun y : S → ℝ => fun s => y s - B :=
      continuous_pi fun s => (continuous_apply s).sub continuous_const
    refine ⟨fun y => u (fun s => y s - B), huc.comp hsc, fun y y' h => hum _ _ fun s => by
      have := h s; linarith, ?_, ?_⟩
    · intro r y1 hy1 y2 hy2 a b ha hb hab
      have := huq r ⟨Set.mem_univ _, hy1.2⟩ ⟨Set.mem_univ _, hy2.2⟩ ha hb hab
      refine ⟨Set.mem_univ _, ?_⟩
      convert this.2 using 2
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination B * hab
    · intro p hp y hy
      have hy' : dot p (fun s => y s - B) ≤ 0 := by
        have : dot p (fun s => y s - B) = dot p y - dot p (fun _ => B) := by
          simp only [dot, mul_sub, Finset.sum_sub_distrib]
        linarith
      obtain ⟨h1, h2⟩ := huo p hp _ hy'
      simp only [hcx]
      refine ⟨h1, fun hne => h2 fun he => hne ?_⟩
      funext s
      have := congrFun he s
      simp only [c]
      linarith

end ContinuousUtility

end

#print axioms ContinuousUtility.decomp
#print axioms ContinuousUtility.W_convex
#print axioms ContinuousUtility.W_mono
#print axioms ContinuousUtility.W_below
#print axioms ContinuousUtility.tau2_lip
#print axioms ContinuousUtility.util2_continuous
#print axioms ContinuousUtility.tau2_trade
#print axioms ContinuousUtility.optimal2
#print axioms ContinuousUtility.monotone_util2
#print axioms ContinuousUtility.quasiconcave2
#print axioms ContinuousUtility.coord_ge2
#print axioms ContinuousUtility.unique2
#print axioms ContinuousUtility.continuous_mantel_utility
#print axioms ContinuousUtility.continuous_mantel_endowments
