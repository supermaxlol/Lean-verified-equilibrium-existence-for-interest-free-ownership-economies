import Mathlib

/-!
Stage 302: Mantel/Debreu on a continuum of prices.

Prices live on a set `P` of unit vectors with every coordinate at least `ε > 0` (the whole
compact set `S_ε`, not finitely many prices).  `Z` is any bounded function on `P` with
Walras' law.  Following Debreu (1974):

* Decomposition: with `α k p = Z p k + A * p k` for a large constant `A`, every `α k p > 0`,
  each consumer's net trade `x k p = α k p • (e_k − p_k p)` is budget-balanced at `p`, and
  `∑ k, x k p = Z p` for every `p ∈ P`.  `α` is continuous wherever `Z` is.
* Strict revealed preference: if `x k p` is affordable at another price `q ∈ P` then
  `q k < p k`.  So the revealed-preference relation strictly lowers the `k`-th price and has
  no cycles of any length (strong axiom, via transitive closure).
* Rationalization on the whole continuum: `u k y = −sup {q k | q ∈ P, q·y ≤ 0}` is weakly
  monotone and quasiconcave on all of `ℝ^S`, and for every `p ∈ P`, `x k p` maximizes `u k`
  on the budget `{y | p·y ≤ 0}`, with value `−p k`.
-/

noncomputable section

open Finset

namespace MantelFull

variable {S : Type*} [Fintype S] [DecidableEq S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- Direction of consumer `k`'s trade: `e_k − p_k p`. -/
def dir (k : S) (p : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - p k * p s

/-- Weight on consumer `k`. -/
def alpha (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ) : ℝ := Z p k + A * p k

/-- Consumer `k`'s net trade. -/
def xd (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ) (s : S) : ℝ :=
  alpha Z A k p * dir k p s

theorem dot_dir (k : S) (p q : S → ℝ) : dot q (dir k p) = q k - p k * dot q p := by
  have h : ∑ s, q s * dir k p s = ∑ s, (if s = k then q s else 0) - p k * ∑ s, q s * p s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      unfold dir; split_ifs <;> ring
  unfold dot
  rw [h, Finset.sum_ite_eq' univ k q]
  simp

theorem dot_xd (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p q : S → ℝ) :
    dot q (xd Z A k p) = alpha Z A k p * (q k - p k * dot q p) := by
  rw [← dot_dir]
  unfold dot xd
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq S] in
theorem dot_self (p : S → ℝ) : dot p p = ∑ s, p s ^ 2 :=
  Finset.sum_congr rfl fun s _ => by ring

/-- **Each consumer's trade is budget-balanced.** -/
theorem xd_budget (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p : S → ℝ)
    (hu : ∑ s, p s ^ 2 = 1) : dot p (xd Z A k p) = 0 := by
  rw [dot_xd, dot_self, hu]; ring

/-- **Decomposition.**  The individual trades add up to `Z p`, for any constant `A`. -/
theorem decomposition (Z : (S → ℝ) → S → ℝ) (A : ℝ) (p : S → ℝ) (hu : ∑ s, p s ^ 2 = 1)
    (hW : ∑ s, p s * Z p s = 0) (s : S) : ∑ k, xd Z A k p s = Z p s := by
  have h1 : ∑ k, xd Z A k p s =
      ∑ k, (if s = k then alpha Z A k p else 0) - p s * ∑ k, (p k * Z p k + A * p k ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      unfold xd dir alpha; split_ifs <;> ring
  rw [h1, Finset.sum_ite_eq univ s (fun k => alpha Z A k p), Finset.sum_add_distrib,
    ← Finset.mul_sum, hW, hu]
  simp [alpha]
  ring

omit [Fintype S] [DecidableEq S] in
/-- **Positive weights** once `A` is large. -/
theorem alpha_pos (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s) (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B)
    (k : S) (p : S → ℝ) (hp : p ∈ P) : 0 < alpha Z (B / ε + 1) k p := by
  have hA : 0 ≤ B / ε + 1 := by positivity
  have e : (B / ε + 1) * ε = B + ε := by rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul]
  have h1 : (B / ε + 1) * ε ≤ (B / ε + 1) * p k := mul_le_mul_of_nonneg_left (hpos p hp k) hA
  have h2 : -B ≤ Z p k := (abs_le.1 (hB p hp k)).1
  unfold alpha
  linarith

omit [Fintype S] [DecidableEq S] in
theorem alpha_continuousOn (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (hZ : ContinuousOn Z P)
    (A : ℝ) (k : S) : ContinuousOn (alpha Z A k) P :=
  ((continuous_apply k).comp_continuousOn hZ).add
    (continuousOn_const.mul (continuous_apply k).continuousOn)

omit [DecidableEq S] in
theorem dot_lt_one (p q : S → ℝ) (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1)
    (hne : p ≠ q) : dot q p < 1 := by
  obtain ⟨s, hs⟩ : ∃ s, p s ≠ q s := by
    by_contra h
    exact hne (funext fun s => not_not.1 fun h' => h ⟨s, h'⟩)
  have hpos : 0 < ∑ s, (p s - q s) ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨s, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hs)))⟩
  have e : ∑ s, (p s - q s) ^ 2 = ∑ s, p s ^ 2 + ∑ s, q s ^ 2 - 2 * dot q p := by
    unfold dot
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

/-- **Strict revealed preference.**  If consumer `k`'s choice at `p` is affordable at a
different price `q`, then good `k` is strictly cheaper at `q`. -/
theorem revealed_strict (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (p q : S → ℝ)
    (hp : ∑ s, p s ^ 2 = 1) (hq : ∑ s, q s ^ 2 = 1) (hne : p ≠ q) (hα : 0 < alpha Z A k p)
    (hpk : 0 < p k) (haff : dot q (xd Z A k p) ≤ 0) : q k < p k := by
  rw [dot_xd] at haff
  have h1 : q k - p k * dot q p ≤ 0 := by
    by_contra h
    exact absurd haff (not_le.2 (mul_pos hα (lt_of_not_ge h)))
  have h2 := dot_lt_one p q hp hq hne
  nlinarith

/-- Revealed preference on `P`: `p ≠ q` and the choice at `p` is affordable at `q`. -/
def RP (Z : (S → ℝ) → S → ℝ) (A : ℝ) (k : S) (P : Set (S → ℝ)) (p q : S → ℝ) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p ≠ q ∧ dot q (xd Z A k p) ≤ 0

/-- **Strong axiom.**  Chains of revealed preference strictly lower the `k`-th price, so the
transitive closure is irreflexive: no cycles of any length. -/
theorem strong_axiom (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s)
    (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B) (k : S) (p q : S → ℝ)
    (h : Relation.TransGen (RP Z (B / ε + 1) k P) p q) : q k < p k ∧ ¬ (p = q) := by
  have step : ∀ a b, RP Z (B / ε + 1) k P a b → b k < a k := fun a b ⟨ha, hb, hne, haff⟩ =>
    revealed_strict Z _ k a b (hu a ha) (hu b hb) hne
      (alpha_pos Z P ε B hε hB0 hpos hB k a ha) (lt_of_lt_of_le hε (hpos a ha k)) haff
  have key : q k < p k := by
    induction h with
    | single hab => exact step _ _ hab
    | tail _ hbc ih => exact lt_trans (step _ _ hbc) ih
  exact ⟨key, fun e => by rw [e] at key; exact lt_irrefl _ key⟩

/-- Prices in `P` at which `y` is affordable, recorded by their `k`-th coordinate. -/
def aff (P : Set (S → ℝ)) (k : S) (y : S → ℝ) : Set ℝ := {r | ∃ q ∈ P, dot q y ≤ 0 ∧ r = q k}

/-- Consumer `k`'s utility. -/
def u (P : Set (S → ℝ)) (k : S) (y : S → ℝ) : ℝ := -sSup (aff P k y)

omit [DecidableEq S] in
theorem aff_bdd (P : Set (S → ℝ)) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (k : S) (y : S → ℝ) :
    BddAbove (aff P k y) := by
  refine ⟨1, fun r ⟨q, hq, _, hr⟩ => ?_⟩
  have h : q k ^ 2 ≤ ∑ s, q s ^ 2 :=
    Finset.single_le_sum (f := fun s => q s ^ 2) (fun s _ => sq_nonneg _) (mem_univ k)
  rw [hu q hq] at h
  rw [hr]
  nlinarith

omit [DecidableEq S] in
theorem aff_nonneg (P : Set (S → ℝ)) (ε : ℝ) (hε : 0 < ε) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s)
    (k : S) (y : S → ℝ) : 0 ≤ sSup (aff P k y) :=
  Real.sSup_nonneg fun r ⟨q, hq, _, hr⟩ => by rw [hr]; linarith [hpos q hq k]

/-- **Rationalization on the continuum.**  For every `p ∈ P`, the trade `x k p` attains
utility `−p k`, and nothing affordable at `p` does better. -/
theorem rationalize (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s)
    (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B) (k : S) (p : S → ℝ) (hp : p ∈ P) :
    u P k (xd Z (B / ε + 1) k p) = -p k ∧
      ∀ y, dot p y ≤ 0 → u P k y ≤ u P k (xd Z (B / ε + 1) k p) := by
  have hself : p k ∈ aff P k (xd Z (B / ε + 1) k p) :=
    ⟨p, hp, le_of_eq (xd_budget Z _ k p (hu p hp)), rfl⟩
  have hsup : sSup (aff P k (xd Z (B / ε + 1) k p)) = p k := by
    refine le_antisymm (csSup_le ⟨_, hself⟩ fun r ⟨q, hq, hqa, hr⟩ => ?_)
      (le_csSup (aff_bdd P hu k _) hself)
    rw [hr]
    by_cases e : p = q
    · rw [e]
    · exact (revealed_strict Z _ k p q (hu p hp) (hu q hq) e
        (alpha_pos Z P ε B hε hB0 hpos hB k p hp) (lt_of_lt_of_le hε (hpos p hp k)) hqa).le
  have hval : u P k (xd Z (B / ε + 1) k p) = -p k := by unfold u; rw [hsup]
  refine ⟨hval, fun y hy => ?_⟩
  rw [hval]
  unfold u
  have : p k ≤ sSup (aff P k y) := le_csSup (aff_bdd P hu k y) ⟨p, hp, hy, rfl⟩
  linarith

omit [DecidableEq S] in
/-- **Monotone.** -/
theorem u_mono (P : Set (S → ℝ)) (ε : ℝ) (hε : 0 < ε) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1)
    (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s) (k : S) (y y' : S → ℝ) (hyy : ∀ s, y s ≤ y' s) :
    u P k y ≤ u P k y' := by
  unfold u
  rw [neg_le_neg_iff]
  by_cases hne : (aff P k y').Nonempty
  · refine csSup_le hne fun r ⟨q, hq, hqa, hr⟩ => le_csSup (aff_bdd P hu k y) ⟨q, hq, ?_, hr⟩
    have : dot q y ≤ dot q y' := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hyy s) (le_trans hε.le (hpos q hq s))
    linarith
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]
    exact aff_nonneg P ε hε hpos k y

omit [DecidableEq S] in
/-- **Quasiconcave.** -/
theorem u_quasiconcave (P : Set (S → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s) (k : S)
    (y1 y2 : S → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    min (u P k y1) (u P k y2) ≤ u P k (fun s => a * y1 s + b * y2 s) := by
  have m1 := aff_nonneg P ε hε hpos k y1
  have hsup : sSup (aff P k (fun s => a * y1 s + b * y2 s)) ≤
      max (sSup (aff P k y1)) (sSup (aff P k y2)) := by
    by_cases hne : (aff P k (fun s => a * y1 s + b * y2 s)).Nonempty
    · refine csSup_le hne fun r ⟨q, hq, hqa, hr⟩ => ?_
      have e : dot q (fun s => a * y1 s + b * y2 s) = a * dot q y1 + b * dot q y2 := by
        unfold dot
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e] at hqa
      by_cases h1 : dot q y1 ≤ 0
      · exact le_max_of_le_left (le_csSup (aff_bdd P hu k y1) ⟨q, hq, h1, hr⟩)
      · have h2 : dot q y2 ≤ 0 := by
          by_contra h2
          have := not_le.1 h1
          have := not_le.1 h2
          rcases ha.lt_or_eq with ha' | ha'
          · nlinarith
          · have hb1 : b = 1 := by linarith
            rw [← ha', hb1] at hqa
            linarith
        exact le_max_of_le_right (le_csSup (aff_bdd P hu k y2) ⟨q, hq, h2, hr⟩)
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]
      exact le_max_of_le_left m1
  unfold u
  rw [min_le_iff]
  rcases le_total (sSup (aff P k y1)) (sSup (aff P k y2)) with h | h
  · right; rw [max_eq_right h] at hsup; linarith
  · left; rw [max_eq_left h] at hsup; linarith

/-- **Mantel/Debreu on `S_ε`, weak form.**  Every bounded `Z` with Walras' law on `P` is the
sum of `|S|` budget-balanced trades, each of which is optimal for a monotone quasiconcave
utility at every price in `P`. -/
theorem mantel_full (Z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (ε B : ℝ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hu : ∀ p ∈ P, ∑ s, p s ^ 2 = 1) (hpos : ∀ p ∈ P, ∀ s, ε ≤ p s)
    (hB : ∀ p ∈ P, ∀ s, |Z p s| ≤ B) (hW : ∀ p ∈ P, ∑ s, p s * Z p s = 0) :
    ∃ x : S → (S → ℝ) → S → ℝ, ∀ p ∈ P,
      (∀ s, ∑ k, x k p s = Z p s) ∧
      (∀ k, dot p (x k p) = 0) ∧
      (∀ k y, dot p y ≤ 0 → u P k y ≤ u P k (x k p)) :=
  ⟨xd Z (B / ε + 1), fun p hp =>
    ⟨decomposition Z _ p (hu p hp) (hW p hp), fun k => xd_budget Z _ k p (hu p hp),
      fun k => (rationalize Z P ε B hε hB0 hu hpos hB k p hp).2⟩⟩

end MantelFull

end

#print axioms MantelFull.dot_dir
#print axioms MantelFull.xd_budget
#print axioms MantelFull.decomposition
#print axioms MantelFull.alpha_pos
#print axioms MantelFull.alpha_continuousOn
#print axioms MantelFull.dot_lt_one
#print axioms MantelFull.revealed_strict
#print axioms MantelFull.strong_axiom
#print axioms MantelFull.rationalize
#print axioms MantelFull.u_mono
#print axioms MantelFull.u_quasiconcave
#print axioms MantelFull.mantel_full
