import Mathlib

/-!
# Stage 374: a monotone, quasi-concave utility for each Debreu consumer, for continuous
# excess demand

Stage 372 splits a continuous Walras excess demand `z` on unit prices into `n` trades
`x_k(p) = (A p_k + z_k(p)) (e_k − p_k p)` and shows each is the unique best choice for some
complete, transitive preference (a linear order), with no regularity. This file replaces the
linear order by a real-valued utility function with two of the regularity properties of the
classical statement, still with no Lipschitz bound on `z`.

The construction is an explicit family of upper contour sets. Write `P` for the price set,
`w` for the weight and `x(q) = w(q) (e_k − q_k q)` for the trade. For a level `t` let

  `m_t(ν) = inf {ν · x(q) : q ∈ P, q_k ≤ t}`  and  `C_t = {y : ν · y ≥ m_t(ν) for all ν ≥ 0}`,

the smallest closed convex upward-closed set containing every trade chosen at a price with
`q_k ≤ t` and described by non-negative normals. The utility is `u(y) = −τ(y)`, where `τ(y)` is
the least level `t` with `y ∈ C_t` (and `2` if there is none).

* `Up_convex`, `Up_mono`: each `C_t` is convex, and the family grows with `t`.
* `not_mem_below`: if `p · y ≤ 0` then `y ∉ C_t` for every `t < p_k`. This is the only place the
  shape of the trades enters: for `q_k ≤ t < p_k`, `p · x(q) = w(q)(p_k − q_k p·q) ≥ w_min (p_k − t)`.
* `tau_trade`: `τ(x(p)) = p_k`, so `u(x(p)) = −p_k`.
* **`optimal`**: `x(p)` maximises `u` on the budget `{y : p · y ≤ 0}`.
* **`unique`**: if `x` is continuous (within `P`) at `p`, then `x(p)` is the *only* maximiser:
  every other affordable bundle has strictly lower utility. The proof tilts the normal `p` to
  `p ± η e_j` and uses only the modulus of continuity of `x` at `p` and the quadratic gap
  `1 − p·q ≥ dist(p,q)² / 2`; no Lipschitz constant appears.
* **`monotone_util`**: `u` is non-decreasing in every good.
* **`quasiconcave`**: `u` is quasi-concave (its upper level sets are convex), so the preference
  is convex.
* **`continuous_mantel_utility`**: for a Walras `z` that is continuous and bounded on the prices
  with every coordinate at least `ε` (`Peps`), `z` is the sum of the `n` trades, and each trade
  is, at every such price, the unique maximiser on its budget of a real-valued, non-decreasing,
  quasi-concave utility.

Reading: with only continuity of `z`, each Debreu consumer is represented by a utility function
that is monotone and gives convex preferences, and demand is the unique maximiser. Compared with
stage 372, the linear order is replaced by a utility with these two regularity properties.

Limits: the utility is **not shown to be continuous**, and in general this particular
construction is not: `C_t` is the smallest admissible upper contour set, and when
`t ↦ m_t(ν)` is flat for some normal `ν` (which can happen for a non-smooth weight) the family
does not grow there and `u` jumps. The preference is convex but not shown to be strictly
convex, and `u` is non-decreasing but not shown to be strictly increasing; utility values lie
in `[−2, 0]`. Debreu's and Mantel's theorems give continuous, strictly monotone, strictly convex
preferences; for continuous, non-Lipschitz `z` that full statement is still not proved in this
program, and the remaining step is continuity of the utility. Trades are on the unit sphere,
the budget is `p · y ≤ 0`, and consumption is not required to be non-negative (as in stages 353
and 372).
-/

noncomputable section

open Finset

namespace ContinuousRationalisation

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

/-! ## The upper contour sets and the utility -/

/-- The lowest value of `ν · x(q)` over the prices with `q_k ≤ t`. -/
def mval (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (t : ℝ) (ν : S → ℝ) : ℝ :=
  sInf ((fun q => dot ν (trade w k q)) '' {q | q ∈ P ∧ q k ≤ t})

/-- The upper contour set at level `t`. -/
def Up (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (t : ℝ) : Set (S → ℝ) :=
  {y | ∀ ν : S → ℝ, (∀ s, 0 ≤ ν s) → mval P w k t ν ≤ dot ν y}

/-- The admissible levels of a bundle. -/
def Idx (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (y : S → ℝ) : Set ℝ :=
  {t | (∃ q ∈ P, q k ≤ t) ∧ y ∈ Up P w k t}

/-- The least level of a bundle (`2` if it has none). -/
def tau (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (y : S → ℝ) : ℝ :=
  sInf (insert (2 : ℝ) (Idx P w k y))

/-- The utility. -/
def util (P : Set (S → ℝ)) (w : (S → ℝ) → ℝ) (k : S) (y : S → ℝ) : ℝ := -tau P w k y

section Generic

variable (P : Set (S → ℝ)) (hP : P ⊆ Cap) (w : (S → ℝ) → ℝ) (wmin wmax : ℝ)
  (hwmin : 0 < wmin) (hw : ∀ q ∈ P, wmin ≤ w q ∧ w q ≤ wmax) (k : S)

include hP hwmin hw in
theorem bdd (t : ℝ) (ν : S → ℝ) (hν : ∀ s, 0 ≤ ν s) :
    BddBelow ((fun q => dot ν (trade w k q)) '' {q | q ∈ P ∧ q k ≤ t}) := by
  refine ⟨-(wmax * ∑ s, ν s), ?_⟩
  rintro _ ⟨q, ⟨hqP, -⟩, rfl⟩
  exact dot_ge ν _ hν wmax fun s =>
    trade_abs w k q (hP hqP) wmax (by linarith [(hw q hqP).1]) (hw q hqP).2 s

include hP hwmin hw in
theorem mval_le (t : ℝ) (ν : S → ℝ) (hν : ∀ s, 0 ≤ ν s) (q : S → ℝ) (hq : q ∈ P)
    (hqt : q k ≤ t) : mval P w k t ν ≤ dot ν (trade w k q) :=
  csInf_le (bdd P hP w wmin wmax hwmin hw k t ν hν) ⟨q, ⟨hq, hqt⟩, rfl⟩

theorem le_mval (t : ℝ) (ν : S → ℝ) (b : ℝ) (q0 : S → ℝ) (hq0 : q0 ∈ P) (hq0t : q0 k ≤ t)
    (h : ∀ q ∈ P, q k ≤ t → b ≤ dot ν (trade w k q)) : b ≤ mval P w k t ν := by
  unfold mval
  apply le_csInf
    ((Set.nonempty_of_mem (show q0 ∈ {q | q ∈ P ∧ q k ≤ t} from ⟨hq0, hq0t⟩)).image _)
  rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
  exact h q hq hqt

include hP hwmin hw in
/-- **The family grows with the level.** -/
theorem Up_mono (t t' : ℝ) (htt : t ≤ t') (q0 : S → ℝ) (hq0 : q0 ∈ P) (hq0t : q0 k ≤ t) :
    Up P w k t ⊆ Up P w k t' := by
  intro y hy ν hν
  refine le_trans ?_ (hy ν hν)
  unfold mval
  apply csInf_le_csInf (bdd P hP w wmin wmax hwmin hw k t' ν hν)
    ((Set.nonempty_of_mem (show q0 ∈ {q | q ∈ P ∧ q k ≤ t} from ⟨hq0, hq0t⟩)).image _)
  rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
  exact ⟨q, ⟨hq, hqt.trans htt⟩, rfl⟩

/-- **Each upper contour set is convex.** -/
theorem Up_convex (t : ℝ) : Convex ℝ (Up P w k t) := by
  intro y1 h1 y2 h2 a b ha hb hab ν hν
  have e : dot ν (a • y1 + b • y2) = a * dot ν y1 + b * dot ν y2 := by
    show ∑ s, ν s * (a • y1 + b • y2) s = a * ∑ s, ν s * y1 s + b * ∑ s, ν s * y2 s
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [e]
  have e1 := h1 ν hν
  have e2 := h2 ν hν
  have m1 := mul_le_mul_of_nonneg_left e1 ha
  have m2 := mul_le_mul_of_nonneg_left e2 hb
  have m3 : a * mval P w k t ν + b * mval P w k t ν = mval P w k t ν := by
    rw [← add_mul, hab, one_mul]
  linarith

include hP in
theorem idx_bdd (y : S → ℝ) : BddBelow (insert (2 : ℝ) (Idx P w k y)) := by
  refine ⟨0, ?_⟩
  rintro t (rfl | ⟨⟨q, hq, hqt⟩, -⟩)
  · norm_num
  · exact ((hP hq).2 k).le.trans hqt

include hP in
theorem tau_le (y : S → ℝ) (t : ℝ) (hy : y ∈ Up P w k t) (q : S → ℝ) (hq : q ∈ P)
    (hqt : q k ≤ t) : tau P w k y ≤ t :=
  csInf_le (idx_bdd P hP w k y) (Set.mem_insert_of_mem _ ⟨⟨q, hq, hqt⟩, hy⟩)

include hP in
theorem tau_le_two (y : S → ℝ) : tau P w k y ≤ 2 :=
  csInf_le (idx_bdd P hP w k y) (Set.mem_insert _ _)

theorem dot_lower (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (hq : q ∈ (Cap : Set (S → ℝ)))
    (hw0 : 0 ≤ w q) : w q * (p k - q k) ≤ dot p (trade w k q) := by
  rw [dot_trade]
  have hc := dot_le_one p q hp.1 hq.1
  have hqk := hq.2 k
  have h1 : q k * dot p q ≤ q k := mul_le_of_le_one_right hqk.le hc
  exact mul_le_mul_of_nonneg_left (by linarith) hw0

include hP hwmin hw in
/-- **Below the price's own level nothing affordable is reached.** -/
theorem not_mem_below (p : S → ℝ) (hp : p ∈ P) (y : S → ℝ) (hy : dot p y ≤ 0) (t : ℝ)
    (q0 : S → ℝ) (hq0 : q0 ∈ P) (hq0t : q0 k ≤ t) (htp : t < p k) : y ∉ Up P w k t := by
  intro hyU
  have hpos : wmin * (p k - t) ≤ mval P w k t p := by
    refine le_mval P w k t p _ q0 hq0 hq0t fun q hq hqt => ?_
    have hw' := hw q hq
    have h1 := dot_lower w k p q (hP hp) (hP hq) (by linarith)
    have h2 : wmin * (p k - t) ≤ w q * (p k - q k) :=
      mul_le_mul hw'.1 (by linarith) (by linarith) (by linarith)
    linarith
  have h3 := hyU p fun s => ((hP hp).2 s).le
  nlinarith [mul_pos hwmin (sub_pos.2 htp)]

include hP hwmin hw in
/-- An affordable bundle has level at least `p_k`. -/
theorem tau_ge (p : S → ℝ) (hp : p ∈ P) (y : S → ℝ) (hy : dot p y ≤ 0) : p k ≤ tau P w k y := by
  apply le_csInf ⟨2, Set.mem_insert _ _⟩
  rintro t (rfl | ⟨⟨q, hq, hqt⟩, hyU⟩)
  · linarith [coord_le_one p (hP hp) k]
  · by_contra h
    push Not at h
    exact not_mem_below P hP w wmin wmax hwmin hw k p hp y hy t q hq hqt h hyU

include hP hwmin hw in
theorem mem_Up_self (p : S → ℝ) (hp : p ∈ P) : trade w k p ∈ Up P w k (p k) :=
  fun ν hν => mval_le P hP w wmin wmax hwmin hw k (p k) ν hν p hp le_rfl

include hP hwmin hw in
/-- **The level of a chosen trade is its own price coordinate.** -/
theorem tau_trade (p : S → ℝ) (hp : p ∈ P) : tau P w k (trade w k p) = p k :=
  le_antisymm (tau_le P hP w k _ (p k) (mem_Up_self P hP w wmin wmax hwmin hw k p hp) p hp le_rfl)
    (tau_ge P hP w wmin wmax hwmin hw k p hp _ (le_of_eq (budget w k p (hP hp).1)))

include hP hwmin hw in
/-- **Each trade maximises the utility on its budget.** -/
theorem optimal (p : S → ℝ) (hp : p ∈ P) (y : S → ℝ) (hy : dot p y ≤ 0) :
    util P w k y ≤ util P w k (trade w k p) := by
  unfold util
  rw [tau_trade P hP w wmin wmax hwmin hw k p hp]
  linarith [tau_ge P hP w wmin wmax hwmin hw k p hp y hy]

include hP in
/-- **The utility is non-decreasing in every good.** -/
theorem monotone_util (y y' : S → ℝ) (h : ∀ s, y s ≤ y' s) :
    util P w k y ≤ util P w k y' := by
  unfold util tau
  have : sInf (insert (2 : ℝ) (Idx P w k y')) ≤ sInf (insert (2 : ℝ) (Idx P w k y)) := by
    apply csInf_le_csInf (idx_bdd P hP w k y') ⟨2, Set.mem_insert _ _⟩
    apply Set.insert_subset_insert
    rintro t ⟨hq, hyU⟩
    exact ⟨hq, fun ν hν => (hyU ν hν).trans (dot_mono ν y y' hν h)⟩
  linarith

include hP hwmin hw in
/-- **The utility is quasi-concave**: the preference is convex. -/
theorem quasiconcave : QuasiconcaveOn ℝ Set.univ (util P w k) := by
  intro r y1 h1 y2 h2 a b ha hb hab
  refine ⟨Set.mem_univ _, ?_⟩
  have h1' : tau P w k y1 ≤ -r := by
    have := h1.2
    unfold util at this
    linarith
  have h2' : tau P w k y2 ≤ -r := by
    have := h2.2
    unfold util at this
    linarith
  suffices hs : tau P w k (a • y1 + b • y2) ≤ -r by
    unfold util
    linarith
  by_contra hc
  push Not at hc
  set s' := (-r + tau P w k (a • y1 + b • y2)) / 2 with hs'
  have hlt : s' < tau P w k (a • y1 + b • y2) := by rw [hs']; linarith
  have hs1 : tau P w k y1 < s' := by rw [hs']; linarith
  have hs2 : tau P w k y2 < s' := by rw [hs']; linarith
  obtain ⟨a1, ha1, ha1s⟩ := exists_lt_of_csInf_lt ⟨2, Set.mem_insert _ _⟩ hs1
  obtain ⟨a2, ha2, ha2s⟩ := exists_lt_of_csInf_lt ⟨2, Set.mem_insert _ _⟩ hs2
  have htwo := tau_le_two P hP w k (a • y1 + b • y2)
  rcases ha1 with rfl | ⟨⟨q1, hq1, hq1t⟩, hy1⟩
  · linarith
  rcases ha2 with rfl | ⟨⟨q2, hq2, hq2t⟩, hy2⟩
  · linarith
  have hm : a • y1 + b • y2 ∈ Up P w k (max a1 a2) :=
    Up_convex P w k (max a1 a2)
      (Up_mono P hP w wmin wmax hwmin hw k a1 _ (le_max_left _ _) q1 hq1 hq1t hy1)
      (Up_mono P hP w wmin wmax hwmin hw k a2 _ (le_max_right _ _) q2 hq2 hq2t hy2) ha hb hab
  have := tau_le P hP w k _ (max a1 a2) hm q1 hq1 (hq1t.trans (le_max_left _ _))
  have := max_lt ha1s ha2s
  linarith

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

theorem dot_lower2 (p q : S → ℝ) (hp : p ∈ (Cap : Set (S → ℝ))) (hq : q ∈ (Cap : Set (S → ℝ)))
    (t : ℝ) (hqt : q k ≤ t) (hpt : p k ≤ t) (hwq : wmin ≤ w q) (hwq' : w q ≤ wmax)
    (hwmin' : 0 ≤ wmin) :
    wmin * p k * (1 - dot p q) - wmax * (t - p k) ≤ dot p (trade w k q) := by
  rw [dot_trade]
  have hc1 := dot_le_one p q hp.1 hq.1
  have hc0 := dot_nonneg_cap p q hp hq
  have hpk := hp.2 k
  set c := dot p q
  have hX : p k * (1 - c) - (t - p k) ≤ p k - q k * c := by
    have : c * (p k - t) ≥ -(t - p k) := by nlinarith
    nlinarith
  have hA : 0 ≤ p k * (1 - c) := mul_nonneg hpk.le (by linarith)
  have hw0 : 0 ≤ w q := by linarith
  have e1 := mul_le_mul_of_nonneg_left hX hw0
  have e2 := mul_le_mul_of_nonneg_right hwq hA
  have e3 := mul_le_mul_of_nonneg_right hwq' (show 0 ≤ t - p k by linarith)
  nlinarith

include hP hwmin hw in
/-- **The tilt argument.** If `p · y ≤ 0` and `y` has level at most `p_k`, then in every
coordinate `σ y_j ≥ σ x_j(p)` for `σ = ±1`. Only continuity of `x` at `p` is used. -/
theorem coord_ge (p : S → ℝ) (hp : p ∈ P)
    (hc : ContinuousWithinAt (fun q => trade w k q) P p) (y : S → ℝ) (hy : dot p y ≤ 0)
    (ht : tau P w k y ≤ p k) (j : S) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    σ * trade w k p j ≤ σ * y j := by
  have hpC := hP hp
  have hpk : 0 < p k := hpC.2 k
  have hpj : 0 < p j := hpC.2 j
  have hwp := hw p hp
  have hwmax : 0 < wmax := by linarith
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine le_of_forall_pos_le_add fun γ hγ => ?_
  obtain ⟨r, hr, hcont⟩ := Metric.continuousWithinAt_iff.1 hc (γ / 2) (by positivity)
  set η := min (p j / 2) (wmin * p k * r ^ 2 / (8 * (wmax + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ p j / 2 := min_le_left _ _
  have hη2 : η ≤ wmin * p k * r ^ 2 / (8 * (wmax + 1)) := min_le_right _ _
  set δ' := min (1 / 2) (η * γ / (2 * (wmax + 1))) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by norm_num) (by positivity)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_left _ _
  have hδ'2 : δ' ≤ η * γ / (2 * (wmax + 1)) := min_le_right _ _
  -- a level of `y` close to `p_k`
  obtain ⟨t, htI, hts⟩ := exists_lt_of_csInf_lt (s := insert (2 : ℝ) (Idx P w k y))
    ⟨2, Set.mem_insert _ _⟩ (show tau P w k y < p k + δ' by linarith)
  have hpk1 := coord_le_one p hpC k
  rcases htI with rfl | ⟨⟨q0, hq0, hq0t⟩, hyU⟩
  · linarith
  have htp : p k ≤ t := by
    by_contra h
    push Not at h
    exact not_mem_below P hP w wmin wmax hwmin hw k p hp y hy t q0 hq0 hq0t h hyU
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
  have hxp := fun s => trade_abs w k p hpC wmax (by linarith) hwp.2 s
  have hxpj : |trade w k p j| ≤ wmax := hxp j
  -- lower bound for every candidate
  have hlow : -(wmax * (t - p k)) + η * σ * trade w k p j - η * (γ / 2) ≤ mval P w k t ν := by
    refine le_mval P w k t ν _ q0 hq0 hq0t fun q hq hqt => ?_
    have hqC := hP hq
    have hwq := hw q hq
    rw [hν, dot_bump]
    have hL := dot_lower2 w wmin wmax k p q hpC hqC t hqt htp hwq.1 hwq.2 hwmin.le
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
      nlinarith
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
      have h4 : η * (8 * (wmax + 1)) ≤ wmin * p k * r ^ 2 := by
        rw [le_div_iff₀ (by positivity)] at hη2
        exact hη2
      have h5 := mul_le_mul_of_nonneg_left h1 hη0.le
      have h6 := mul_le_mul_of_nonneg_left h2 hη0.le
      nlinarith
  have hup := hyU ν hν0
  rw [hν, dot_bump] at hup
  have hδ : wmax * (t - p k) ≤ η * γ / 2 := by
    have : t - p k ≤ η * γ / (2 * (wmax + 1)) := by linarith
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have key : η * (σ * trade w k p j) ≤ η * (σ * y j + γ) := by nlinarith
  exact le_of_mul_le_mul_left key hη0

include hP hwmin hw in
/-- **The trade is the unique maximiser.** If `x` is continuous within `P` at `p`, every
affordable bundle other than `x(p)` has strictly lower utility. -/
theorem unique (p : S → ℝ) (hp : p ∈ P)
    (hc : ContinuousWithinAt (fun q => trade w k q) P p) (y : S → ℝ) (hy : dot p y ≤ 0)
    (hne : y ≠ trade w k p) : util P w k y < util P w k (trade w k p) := by
  rcases lt_or_eq_of_le (optimal P hP w wmin wmax hwmin hw k p hp y hy) with h | h
  · exact h
  exfalso
  apply hne
  have ht : tau P w k y ≤ p k := by
    have := tau_trade P hP w wmin wmax hwmin hw k p hp
    unfold util at h
    linarith
  funext j
  have a := coord_ge P hP w wmin wmax hwmin hw k p hp hc y hy ht j 1 (Or.inl rfl)
  have b := coord_ge P hP w wmin wmax hwmin hw k p hp hc y hy ht j (-1) (Or.inr rfl)
  linarith

end Generic

/-! ## Assembly -/

/-- **A monotone, quasi-concave utility for each Debreu consumer, for continuous `z`.** Let `z`
be Walras on the unit prices with every coordinate at least `ε`, continuous and bounded by `M`
there. With `A = M / ε + 1`, `z` is the sum of the `n` trades `x_k`, and for each `k` there is a
real-valued utility that is non-decreasing in every good and quasi-concave, such that at every
such price `p`, `x_k(p)` maximises it on the budget `p · y ≤ 0` and every other affordable
bundle is strictly worse. -/
theorem continuous_mantel_utility (z : (S → ℝ) → S → ℝ) (ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hW : ∀ p ∈ (Peps ε : Set (S → ℝ)), dot p (z p) = 0)
    (hz : ∀ k, ∀ q ∈ (Peps ε : Set (S → ℝ)), |z q k| ≤ M)
    (hzc : ContinuousOn z (Peps ε)) :
    let x : S → (S → ℝ) → S → ℝ := fun k => trade (fun q => (M / ε + 1) * q k + z q k) k
    (∀ p ∈ (Peps ε : Set (S → ℝ)), ∀ s, z p s = ∑ k, x k p s) ∧
    ∀ k, ∃ u : (S → ℝ) → ℝ,
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
  refine ⟨util (Peps ε) w k, fun y y' h => monotone_util (Peps ε) hPC w k y y' h,
    quasiconcave (Peps ε) hPC w ε _ hε hwb k, fun p hp y hy => ⟨?_, fun hne => ?_⟩⟩
  · exact optimal (Peps ε) hPC w ε _ hε hwb k p hp y hy
  · exact unique (Peps ε) hPC w ε _ hε hwb k p hp
      (trade_continuousOn (M / ε + 1) z (Peps ε) k hzc p hp) y hy hne

end ContinuousRationalisation

end

#print axioms ContinuousRationalisation.decomp
#print axioms ContinuousRationalisation.Up_convex
#print axioms ContinuousRationalisation.Up_mono
#print axioms ContinuousRationalisation.not_mem_below
#print axioms ContinuousRationalisation.tau_trade
#print axioms ContinuousRationalisation.optimal
#print axioms ContinuousRationalisation.monotone_util
#print axioms ContinuousRationalisation.quasiconcave
#print axioms ContinuousRationalisation.coord_ge
#print axioms ContinuousRationalisation.unique
#print axioms ContinuousRationalisation.continuous_mantel_utility
