import Mathlib

/-!
# Stage 372: Debreu's decomposition for continuous excess demand, with revealed-preference
# rationalisation of each consumer

Stage 353 writes a Walras excess demand `z` on unit prices as a sum of `n` consumers' trades
`x_k(p) = (A p_k + z_k(p)) (e_k − p_k p)` and shows that each consumer maximises a continuous,
concave, strictly monotone utility, when `z` is bounded and Lipschitz. Stage 355 shows that the
Lipschitz bound cannot be removed by approximation. Reading stage 353 again, the Lipschitz
hypothesis enters at exactly one place: the continuum Afriat inequalities (`debreu_delta`,
`debreu_weight_afriat`), which build the *utility*. The decomposition itself
(`debreu_decomp`) is algebra and needs nothing.

This file separates the two steps and proves the first in full for continuous `z`, and the
second in a weaker form.

* `dot_le_one`, `dot_eq_one`: for unit vectors, `p · q ≤ 1`, with equality only if `p = q`.
* `decomp`: for unit `p` with `p · z(p) = 0`, `z(p) = Σ_k x_k(p)` (any weights `A p_k + z_k`).
* `budget`: each consumer's trade is affordable and exhausts the budget, `p · x_k(p) = 0`.
* `trade_continuousOn`: if `z` is continuous on the price set, so is each `x_k`.
* `step_lt`: if `x_k(q)` is affordable at `p ≠ q` (that is, `p · x_k(q) ≤ 0`), then
  `p_k < q_k`. This holds for every positive weight, with no continuity at all.
* `warp`: each consumer satisfies the weak axiom of revealed preference.
* `trade_injOn`: different prices give different trades.
* `no_cycle`: each consumer satisfies the strong axiom: the transitive closure of strict
  revealed preference has no cycle (`p_k` strictly rises along any chain).
* **`rationalised`**: for each `k` there is a complete, transitive, antisymmetric preference
  (a linear order on bundles) for which, at every price in the set, `x_k(p)` is the unique best
  bundle in the budget `p · y ≤ 0`. This is Richter's route: the revealed-preference partial
  order is extended by the Szpilrajn theorem (Mathlib's `extend_partialOrder`).
* `positive_weight`: if `|z_k| ≤ M` and `p_k ≥ ε > 0`, then `A = M / ε + 1` makes every weight
  `A p_k + z_k` positive.
* **`continuous_decomposition`**: so a continuous (or merely bounded) Walras `z` on the
  `ε`-interior unit price set is the sum of `n` continuous trades, each exhausting its budget,
  satisfying the weak and strong axioms, and each the unique best choice for a complete,
  transitive preference.

Reading: the part of Debreu's theorem that is about *choice* (each piece is the demand of a
consistent chooser) holds for continuous excess demand with no Lipschitz bound. What stage 353
adds, and what is still open for continuous `z`, is the *regularity* of the preference.

Limits: the preference in `rationalised` is not shown to be continuous, monotone or convex, and
is not shown to be represented by a utility function. Debreu's and Mantel's theorems give
continuous, monotone, strictly convex preferences; for continuous, non-Lipschitz `z` that
stronger statement is not proved here and remains open in this program. Trades are on the
unit sphere with positive coordinates, the budget is `p · y ≤ 0`, and consumption is not
required to be non-negative (as in stage 353).
-/

noncomputable section

open Finset

namespace ContinuousMantel

variable {S : Type*} [Fintype S] [DecidableEq S]

def dot (p y : S → ℝ) : ℝ := ∑ s, p s * y s

/-- The direction `e_k − p_k p`. -/
def dirk (k : S) (p : S → ℝ) (s : S) : ℝ := (if s = k then 1 else 0) - p k * p s

/-- Consumer `k`'s trade at price `p`, with weight `w`. -/
def trade (w : (S → ℝ) → ℝ) (k : S) (p : S → ℝ) (s : S) : ℝ := w p * dirk k p s

/-- The unit price set with positive coordinates. -/
def Cap : Set (S → ℝ) := {p | dot p p = 1 ∧ ∀ s, 0 < p s}

omit [DecidableEq S] in
theorem dot_comm (p q : S → ℝ) : dot p q = dot q p := by
  unfold dot
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

omit [DecidableEq S] in
theorem sq_dist (p q : S → ℝ) (hp : dot p p = 1) (hq : dot q q = 1) :
    ∑ s, (p s - q s) ^ 2 = 2 - 2 * dot p q := by
  have e : ∀ s, (p s - q s) ^ 2 = p s * p s + q s * q s - 2 * (p s * q s) := fun s => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold dot at hp hq ⊢
  rw [hp, hq]
  ring

omit [DecidableEq S] in
/-- For unit vectors, `p · q ≤ 1`. -/
theorem dot_le_one (p q : S → ℝ) (hp : dot p p = 1) (hq : dot q q = 1) : dot p q ≤ 1 := by
  have h := sq_dist p q hp hq
  have h0 : 0 ≤ ∑ s, (p s - q s) ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  linarith

omit [DecidableEq S] in
/-- For unit vectors, `p · q = 1` only if `p = q`. -/
theorem dot_eq_one (p q : S → ℝ) (hp : dot p p = 1) (hq : dot q q = 1) (h : dot p q = 1) :
    p = q := by
  have hs := sq_dist p q hp hq
  rw [h] at hs
  have hz : ∀ s ∈ Finset.univ, (p s - q s) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun s _ => sq_nonneg _).1 (by linarith)
  funext s
  have := hz s (Finset.mem_univ s)
  have : p s - q s = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

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

/-- **Each consumer exhausts the budget.** -/
theorem budget (w : (S → ℝ) → ℝ) (k : S) (p : S → ℝ) (hp : dot p p = 1) :
    dot p (trade w k p) = 0 := by
  rw [dot_trade, hp]
  ring

/-- **Debreu's decomposition.** For unit `p` with `p · z = 0`, and any `A`,
`z = Σ_k (A p_k + z_k) (e_k − p_k p)`. -/
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
/-- **Continuity.** If `z` is continuous on the price set, so is each trade. -/
theorem trade_continuousOn (A : ℝ) (z : (S → ℝ) → S → ℝ) (P : Set (S → ℝ)) (k : S)
    (hz : ContinuousOn z P) :
    ContinuousOn (fun p => trade (fun q => A * q k + z q k) k p) P := by
  have hzk : ContinuousOn (fun q => z q k) P := (continuous_apply k).comp_continuousOn hz
  refine continuousOn_pi.2 fun s => ?_
  unfold trade dirk
  exact ((continuousOn_const.mul (continuous_apply k).continuousOn).add hzk).mul
    (continuousOn_const.sub ((continuous_apply k).continuousOn.mul
      (continuous_apply s).continuousOn))

/-- **The key inequality.** If `x_k(q)` is affordable at `p ≠ q`, then `p_k < q_k`. -/
theorem step_lt (w : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) (hp : p ∈ Cap) (hq : q ∈ Cap)
    (hw : 0 < w q) (hne : p ≠ q) (h : dot p (trade w k q) ≤ 0) : p k < q k := by
  rw [dot_trade] at h
  have h1 : p k - q k * dot p q ≤ 0 := by
    by_contra hc
    push Not at hc
    linarith [mul_pos hw hc]
  have hc1 : dot p q < 1 := lt_of_le_of_ne (dot_le_one p q hp.1 hq.1)
    fun he => hne (dot_eq_one p q hp.1 hq.1 he)
  have hqk := hq.2 k
  nlinarith

/-- **The weak axiom.** If `x_k(q)` is affordable at `p` and differs from `x_k(p)`, then
`x_k(p)` is not affordable at `q`. -/
theorem warp (w : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) (hp : p ∈ Cap) (hq : q ∈ Cap)
    (hwp : 0 < w p) (hwq : 0 < w q) (hne : trade w k q ≠ trade w k p)
    (h : dot p (trade w k q) ≤ 0) : 0 < dot q (trade w k p) := by
  have hpq : p ≠ q := fun he => hne (by rw [he])
  have h1 := step_lt w k p q hp hq hwq hpq h
  by_contra hc
  push Not at hc
  have h2 := step_lt w k q p hq hp hwp (Ne.symm hpq) hc
  linarith

/-- **Different prices give different trades.** -/
theorem trade_injOn (w : (S → ℝ) → ℝ) (k : S) (p q : S → ℝ) (hp : p ∈ Cap) (hq : q ∈ Cap)
    (hwp : 0 < w p) (hwq : 0 < w q) (he : trade w k p = trade w k q) : p = q := by
  by_contra hne
  have h1 : dot p (trade w k q) ≤ 0 := by rw [← he, budget w k p hp.1]
  have h2 : dot q (trade w k p) ≤ 0 := by rw [he, budget w k q hq.1]
  have a := step_lt w k p q hp hq hwq hne h1
  have b := step_lt w k q p hq hp hwp (Ne.symm hne) h2
  linarith

/-- Direct strict revealed preference of consumer `k`: `a` was chosen at some `p` in the price
set when `y ≠ a` was affordable. -/
def RP (w : (S → ℝ) → ℝ) (k : S) (a y : S → ℝ) : Prop :=
  ∃ p ∈ Cap, a = trade w k p ∧ dot p y ≤ 0 ∧ y ≠ a

/-- Along any chain of strict revealed preference, the price coordinate `p_k` strictly rises. -/
theorem chain_lt (w : (S → ℝ) → ℝ) (k : S) (hw : ∀ p ∈ Cap, 0 < w p) (a b : S → ℝ)
    (h : Relation.TransGen (RP w k) a b) :
    ∀ p ∈ Cap, ∀ q ∈ Cap, a = trade w k p → b = trade w k q → p k < q k := by
  induction h with
  | single hab =>
    intro p hp q hq ha hb
    obtain ⟨p0, hp0, ha0, hd, hne⟩ := hab
    have e : p = p0 := trade_injOn w k p p0 hp hp0 (hw p hp) (hw p0 hp0) (ha ▸ ha0)
    subst e
    have hpq : p ≠ q := fun he => hne (by rw [hb, ha0, he])
    exact step_lt w k p q hp hq (hw q hq) hpq (hb ▸ hd)
  | tail _ hmb ih =>
    intro p hp q hq ha hb
    obtain ⟨r, hr, hm, hd, hne⟩ := hmb
    have h1 := ih p hp r hr ha hm
    have hrq : r ≠ q := fun he => hne (by rw [hb, hm, he])
    exact h1.trans (step_lt w k r q hr hq (hw q hq) hrq (hb ▸ hd))

/-- **The strong axiom.** Strict revealed preference has no cycle. -/
theorem no_cycle (w : (S → ℝ) → ℝ) (k : S) (hw : ∀ p ∈ Cap, 0 < w p) (a : S → ℝ) :
    ¬ Relation.TransGen (RP w k) a a := by
  intro h
  obtain ⟨c, hac, -⟩ := Relation.TransGen.head'_iff.1 h
  obtain ⟨p, hp, ha, -, -⟩ := hac
  exact lt_irrefl _ (chain_lt w k hw a a h p hp p hp ha ha)

/-- Weak revealed preference: equal, or strictly revealed preferred through a chain. -/
def WR (w : (S → ℝ) → ℝ) (k : S) (a b : S → ℝ) : Prop := a = b ∨ Relation.TransGen (RP w k) a b

theorem WR_partialOrder (w : (S → ℝ) → ℝ) (k : S) (hw : ∀ p ∈ Cap, 0 < w p) :
    IsPartialOrder (S → ℝ) (WR w k) where
  refl a := Or.inl rfl
  trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    exact Or.inr (hab.trans hbc)
  antisymm a b hab hba := by
    rcases hab with h | hab
    · exact h
    rcases hba with h | hba
    · exact h.symm
    exact absurd (hab.trans hba) (no_cycle w k hw a)

/-- **Rationalisation by a complete, transitive preference.** For each consumer there is a
linear order on bundles under which, at every price in the set, the trade `x_k(p)` is at least
as good as every affordable bundle, and strictly better than every other affordable bundle. -/
theorem rationalised (w : (S → ℝ) → ℝ) (k : S) (hw : ∀ p ∈ Cap, 0 < w p) :
    ∃ R : (S → ℝ) → (S → ℝ) → Prop, IsLinearOrder (S → ℝ) R ∧
      ∀ p ∈ Cap, ∀ y, dot p y ≤ 0 → R (trade w k p) y ∧ (y ≠ trade w k p → ¬ R y (trade w k p)) := by
  have := WR_partialOrder w k hw
  obtain ⟨R, hR, hle⟩ := extend_partialOrder (WR w k)
  refine ⟨R, hR, fun p hp y hy => ?_⟩
  by_cases hyx : y = trade w k p
  · subst hyx
    exact ⟨hR.refl _, fun h => absurd rfl h⟩
  have hr : R (trade w k p) y :=
    hle _ _ (Or.inr (Relation.TransGen.single ⟨p, hp, rfl, hy, hyx⟩))
  exact ⟨hr, fun _ hyr => hyx (hR.antisymm _ _ hyr hr)⟩

omit [Fintype S] [DecidableEq S] in
/-- **A large enough scale makes every weight positive.** -/
theorem positive_weight (z : (S → ℝ) → S → ℝ) (k : S) (ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (P : Set (S → ℝ)) (hz : ∀ q ∈ P, |z q k| ≤ M) (hpk : ∀ q ∈ P, ε ≤ q k) :
    ∀ q ∈ P, 0 < (M / ε + 1) * q k + z q k := by
  intro q hq
  have h1 := hz q hq
  have h2 := hpk q hq
  have h3 : M ≤ M / ε * q k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  have h4 := neg_abs_le (z q k)
  nlinarith

/-- **Debreu's decomposition for continuous excess demand.** Let `z` be Walras (`p · z(p) = 0`)
on the unit prices with every coordinate at least `ε`, continuous and bounded by `M` there.
With `A = M / ε + 1`, `z` is the sum of `n` continuous trades; each trade exhausts its budget,
satisfies the weak and strong axioms of revealed preference, and is the unique best affordable
bundle for some complete, transitive preference. -/
theorem continuous_decomposition (z : (S → ℝ) → S → ℝ) (ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hW : ∀ p ∈ (Cap : Set (S → ℝ)), dot p (z p) = 0)
    (hz : ∀ k, ∀ q ∈ (Cap : Set (S → ℝ)), |z q k| ≤ M)
    (hpk : ∀ k, ∀ q ∈ (Cap : Set (S → ℝ)), ε ≤ q k) :
    let x : S → (S → ℝ) → S → ℝ := fun k => trade (fun q => (M / ε + 1) * q k + z q k) k
    (∀ p ∈ (Cap : Set (S → ℝ)), ∀ s, z p s = ∑ k, x k p s) ∧
    (∀ k, ∀ p ∈ (Cap : Set (S → ℝ)), dot p (x k p) = 0) ∧
    (ContinuousOn z Cap → ∀ k, ContinuousOn (x k) Cap) ∧
    (∀ k, ∀ p ∈ (Cap : Set (S → ℝ)), ∀ q ∈ (Cap : Set (S → ℝ)), x k q ≠ x k p →
      dot p (x k q) ≤ 0 → 0 < dot q (x k p)) ∧
    (∀ k a, ¬ Relation.TransGen
      (RP (fun q => (M / ε + 1) * q k + z q k) k) a a) ∧
    (∀ k, ∃ R : (S → ℝ) → (S → ℝ) → Prop, IsLinearOrder (S → ℝ) R ∧
      ∀ p ∈ (Cap : Set (S → ℝ)), ∀ y, dot p y ≤ 0 →
        R (x k p) y ∧ (y ≠ x k p → ¬ R y (x k p))) := by
  intro x
  have hw : ∀ k, ∀ q ∈ (Cap : Set (S → ℝ)), 0 < (M / ε + 1) * q k + z q k := fun k =>
    positive_weight z k ε M hε hM Cap (hz k) (hpk k)
  refine ⟨fun p hp s => decomp (M / ε + 1) z p hp.1 (hW p hp) s,
    fun k p hp => budget _ k p hp.1, fun hc k => trade_continuousOn _ z Cap k hc,
    fun k p hp q hq hne h => warp _ k p q hp hq (hw k p hp) (hw k q hq) hne h,
    fun k a => no_cycle _ k (hw k) a, fun k => rationalised _ k (hw k)⟩

end ContinuousMantel

end

#print axioms ContinuousMantel.dot_le_one
#print axioms ContinuousMantel.dot_eq_one
#print axioms ContinuousMantel.decomp
#print axioms ContinuousMantel.budget
#print axioms ContinuousMantel.trade_continuousOn
#print axioms ContinuousMantel.step_lt
#print axioms ContinuousMantel.warp
#print axioms ContinuousMantel.trade_injOn
#print axioms ContinuousMantel.no_cycle
#print axioms ContinuousMantel.rationalised
#print axioms ContinuousMantel.positive_weight
#print axioms ContinuousMantel.continuous_decomposition
