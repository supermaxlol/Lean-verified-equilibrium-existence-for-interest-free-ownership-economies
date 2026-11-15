import Mathlib

/-!
Stage 256: the Debreu decomposition (first half of Sonnenschein–Mantel–Debreu surjectivity).

At a price `p`, let `proj p i` be the projection of the `i`-th unit vector onto the budget
hyperplane `p · x = 0`.  Then any vector `z` with `p · z = 0` is

  `z = ∑ i, (z i + lam * p i) • proj p i`     for every `lam`,

each summand has zero value at `p` (it obeys Walras' law on its own), and at a strictly
positive price the coefficients can be made strictly positive.  So every Walrasian excess
demand splits into one "agent" per good, each demanding a positive multiple of the
budget-feasible direction of its own good.

Not proved here: that each summand is the demand of a fixed preference relation.  That
construction is the remaining half of Mantel surjectivity.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

namespace DebreuDecomposition

variable {S : Type*} [Fintype S] [DecidableEq S]

def nsq (p : S → ℝ) : ℝ := ∑ s, p s ^ 2

/-- Projection of the unit vector of good `i` onto the hyperplane orthogonal to `p`. -/
def proj (p : S → ℝ) (i : S) : S → ℝ :=
  fun s => (if s = i then 1 else 0) - p i / nsq p * p s

theorem nsq_pos (p : S → ℝ) (t : S) (hp : ∀ s, 0 < p s) : 0 < nsq p := by
  unfold nsq
  have h1 : p t ^ 2 ≤ ∑ s, p s ^ 2 :=
    Finset.single_le_sum (f := fun s => p s ^ 2) (fun s _ => sq_nonneg (p s))
      (Finset.mem_univ t)
  have h2 : 0 < p t ^ 2 := pow_pos (hp t) 2
  linarith

/-- Each projected direction has zero value: the agent obeys Walras' law individually. -/
theorem proj_walras (p : S → ℝ) (hp : nsq p ≠ 0) (i : S) :
    ∑ s, p s * proj p i s = 0 := by
  have h1 : ∀ s, p s * proj p i s
      = (if s = i then p s else 0) - p i / nsq p * p s ^ 2 := by
    intro s
    unfold proj
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  have h2 : p i / nsq p * ∑ s, p s ^ 2 = p i := by
    show p i / nsq p * nsq p = p i
    field_simp
  rw [h2, sub_self]

/-- **Debreu decomposition.** -/
theorem decomposition (p z : S → ℝ) (hp : nsq p ≠ 0) (hwal : ∑ s, p s * z s = 0)
    (lam : ℝ) (t : S) :
    ∑ i, (z i + lam * p i) * proj p i t = z t := by
  have h1 : ∀ i, (z i + lam * p i) * proj p i t
      = (if t = i then z i + lam * p i else 0)
        - p t / nsq p * (p i * z i + lam * p i ^ 2) := by
    intro i
    unfold proj
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hwal]
  simp only [Finset.mem_univ, ite_true]
  have h2 : p t / nsq p * (0 + lam * ∑ i, p i ^ 2) = lam * p t := by
    show p t / nsq p * (0 + lam * nsq p) = lam * p t
    field_simp
    ring
  rw [h2]
  ring

/-- At a strictly positive price the coefficients can be chosen strictly positive. -/
theorem exists_positive_coeff (p z : S → ℝ) (hp : ∀ s, 0 < p s) :
    ∃ lam : ℝ, ∀ i, 0 < z i + lam * p i := by
  refine ⟨∑ i, |z i| / p i + 1, fun i => ?_⟩
  have h1 : |z i| / p i ≤ ∑ j, |z j| / p j :=
    Finset.single_le_sum (f := fun j => |z j| / p j)
      (fun j _ => div_nonneg (abs_nonneg _) (hp j).le) (Finset.mem_univ i)
  have h2 : (|z i| / p i + 1) * p i ≤ (∑ j, |z j| / p j + 1) * p i :=
    mul_le_mul_of_nonneg_right (by linarith) (hp i).le
  have h3 : (|z i| / p i + 1) * p i = |z i| + p i := by
    have := (hp i).ne'
    field_simp
  have h4 := neg_abs_le (z i)
  have h5 := hp i
  linarith

/-- **Positive decomposition into individually Walrasian agents.** -/
theorem positive_decomposition [Nonempty S] (p z : S → ℝ) (hp : ∀ s, 0 < p s)
    (hwal : ∑ s, p s * z s = 0) :
    ∃ β : S → ℝ, (∀ i, 0 < β i) ∧ (∀ t, ∑ i, β i * proj p i t = z t) ∧
      (∀ i, ∑ s, p s * (β i * proj p i s) = 0) := by
  obtain ⟨lam, hlam⟩ := exists_positive_coeff p z hp
  have hn : nsq p ≠ 0 := (nsq_pos p (Classical.arbitrary S) hp).ne'
  refine ⟨fun i => z i + lam * p i, hlam, fun t => decomposition p z hn hwal lam t,
    fun i => ?_⟩
  have h : ∑ s, p s * ((z i + lam * p i) * proj p i s)
      = (z i + lam * p i) * ∑ s, p s * proj p i s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h, proj_walras p hn i, mul_zero]

end DebreuDecomposition

end


/-!
Stage 262: Sonnenschein–Mantel–Debreu in revealed-preference form.

For each good `i` there is a fixed utility `util i` on net trades such that ANY function `z`
obeying Walras' law on strictly positive prices is, at every such price, the sum of one net
trade per agent, where agent `i`'s net trade

* lies on the budget hyperplane,
* maximises `util i` over the budget set `p · w ≤ 0`, and
* is strictly better than every net trade costing strictly less.

So individual rationality with non-satiated preferences places no restriction on aggregate
excess demand beyond Walras' law.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators DebreuDecomposition

namespace Mantel

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Share of good `i` in the squared length of the price vector. -/
def level (i : S) (q : S → ℝ) : ℝ := q i ^ 2 / nsq q

/-- Strictly positive prices at which the net trade `w` is affordable. -/
def afford (w : S → ℝ) : Set (S → ℝ) := {q | (∀ s, 0 < q s) ∧ ∑ s, q s * w s ≤ 0}

/-- Utility of agent `i` over net trades. -/
def util (i : S) (w : S → ℝ) : ℝ := - sSup (level i '' afford w)

theorem dot_proj (p q : S → ℝ) (i : S) :
    ∑ s, q s * proj p i s = q i - p i / nsq p * ∑ s, q s * p s := by
  have h1 : ∀ s, q s * proj p i s
      = (if s = i then q s else 0) - p i / nsq p * (q s * p s) := by
    intro s
    unfold proj
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq',
    ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]

theorem sq_le_nsq (q : S → ℝ) (i : S) : q i ^ 2 ≤ nsq q :=
  Finset.single_le_sum (f := fun s => q s ^ 2) (fun s _ => sq_nonneg (q s))
    (Finset.mem_univ i)

theorem level_le_one (i : S) (q : S → ℝ) (hq : ∀ s, 0 < q s) : level i q ≤ 1 :=
  (div_le_one (nsq_pos q i hq)).2 (sq_le_nsq q i)

theorem bdd (i : S) (w : S → ℝ) : BddAbove (level i '' afford w) :=
  ⟨1, by rintro _ ⟨q, hq, rfl⟩; exact level_le_one i q hq.1⟩

theorem scaled_walras (p : S → ℝ) (hp : ∀ s, 0 < p s) (i : S) (β : ℝ) :
    ∑ s, p s * (β * proj p i s) = 0 := by
  have h : ∑ s, p s * (β * proj p i s) = β * ∑ s, p s * proj p i s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h, proj_walras p (nsq_pos p i hp).ne' i, mul_zero]

/-- **Revealed preference lowers the level.** If agent `i`'s net trade at `p` is affordable
at `q`, then `q` has a weakly smaller level than `p`. -/
theorem rp_level (p q : S → ℝ) (hp : ∀ s, 0 < p s) (hq : ∀ s, 0 < q s) (i : S) (β : ℝ)
    (hβ : 0 < β) (h : ∑ s, q s * (β * proj p i s) ≤ 0) : level i q ≤ level i p := by
  have hNp := nsq_pos p i hp
  have hNq := nsq_pos q i hq
  have hD : 0 ≤ ∑ s, q s * p s :=
    Finset.sum_nonneg (fun s _ => (mul_pos (hq s) (hp s)).le)
  have h' : ∑ s, q s * (β * proj p i s) = β * ∑ s, q s * proj p i s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [h', dot_proj] at h
  have hx : q i - p i / nsq p * ∑ s, q s * p s ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hβ hc
    linarith
  have hmul : p i / nsq p * (∑ s, q s * p s) * nsq p = p i * ∑ s, q s * p s := by
    have := hNp.ne'
    field_simp
  have hA : q i * nsq p ≤ p i * ∑ s, q s * p s := by
    have h2 : q i * nsq p ≤ p i / nsq p * (∑ s, q s * p s) * nsq p :=
      mul_le_mul_of_nonneg_right (by linarith) hNp.le
    linarith
  have hCS : (∑ s, q s * p s) ^ 2 ≤ nsq q * nsq p :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q p
  have h1 : (q i * nsq p) ^ 2 ≤ (p i * ∑ s, q s * p s) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (hq i).le hNp.le) hA 2
  have h2 : (p i * ∑ s, q s * p s) ^ 2 ≤ p i ^ 2 * (nsq q * nsq p) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
  have e1 : (q i * nsq p) ^ 2 = q i ^ 2 * nsq p * nsq p := by ring
  have e2 : p i ^ 2 * (nsq q * nsq p) = p i ^ 2 * nsq q * nsq p := by ring
  have h3 : q i ^ 2 * nsq p * nsq p ≤ p i ^ 2 * nsq q * nsq p := by linarith
  have h4 : q i ^ 2 * nsq p ≤ p i ^ 2 * nsq q := le_of_mul_le_mul_right h3 hNp
  show q i ^ 2 / nsq q ≤ p i ^ 2 / nsq p
  rw [div_le_div_iff₀ hNq hNp]
  exact h4

/-- A net trade costing strictly less than zero at `p` is affordable at a price with a
strictly higher level. -/
theorem exists_higher (p w : S → ℝ) (hp : ∀ s, 0 < p s) (i j : S) (hj : j ≠ i)
    (hw : ∑ s, p s * w s < 0) :
    ∃ q : S → ℝ, q ∈ afford w ∧ level i p < level i q := by
  have hden : 0 < |w i| + 1 := by have := abs_nonneg (w i); linarith
  obtain ⟨ε, hε, hεw⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * w i ≤ -∑ s, p s * w s := by
    refine ⟨-(∑ s, p s * w s) / (|w i| + 1), div_pos (by linarith) hden, ?_⟩
    have h1 : -(∑ s, p s * w s) / (|w i| + 1) * w i
        ≤ -(∑ s, p s * w s) / (|w i| + 1) * (|w i| + 1) :=
      mul_le_mul_of_nonneg_left (by have := le_abs_self (w i); linarith)
        (div_pos (by linarith) hden).le
    rw [div_mul_cancel₀ _ hden.ne'] at h1
    exact h1
  have hqi : p i + (if i = i then ε else 0) = p i + ε := by simp
  have hdot : ∑ s, (p s + (if s = i then ε else 0)) * w s = ∑ s, p s * w s + ε * w i := by
    have h1 : ∀ s, (p s + (if s = i then ε else 0)) * w s
        = p s * w s + (if s = i then ε * w s else 0) := by
      intro s
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  have hN : nsq (fun s => p s + (if s = i then ε else 0))
      = nsq p + (2 * ε * p i + ε ^ 2) := by
    have h1 : ∀ s, (p s + (if s = i then ε else 0)) ^ 2
        = p s ^ 2 + (if s = i then 2 * ε * p s + ε ^ 2 else 0) := by
      intro s
      split_ifs <;> ring
    show ∑ s, (p s + (if s = i then ε else 0)) ^ 2 = ∑ s, p s ^ 2 + (2 * ε * p i + ε ^ 2)
    rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  have hqpos : ∀ s, 0 < p s + (if s = i then ε else 0) := by
    intro s
    have := hp s
    split_ifs <;> linarith
  refine ⟨fun s => p s + (if s = i then ε else 0), ⟨hqpos, ?_⟩, ?_⟩
  · rw [hdot]
    linarith
  · have hNp := nsq_pos p i hp
    have hNq := nsq_pos _ i hqpos
    have hsplit : p i ^ 2 + ∑ s ∈ Finset.univ.erase i, p s ^ 2 = ∑ s, p s ^ 2 :=
      Finset.add_sum_erase Finset.univ (fun s => p s ^ 2) (Finset.mem_univ i)
    have hrest : 0 < ∑ s ∈ Finset.univ.erase i, p s ^ 2 :=
      Finset.sum_pos' (fun s _ => sq_nonneg (p s))
        ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩, pow_pos (hp j) 2⟩
    have hgap : 0 < nsq p - p i ^ 2 := by
      show 0 < ∑ s, p s ^ 2 - p i ^ 2
      linarith
    have hA : 0 < 2 * ε * p i + ε ^ 2 := by
      have := mul_pos hε (hp i)
      have := pow_pos hε 2
      linarith
    have hprod := mul_pos hA hgap
    have hid : (p i + ε) ^ 2 * nsq p - p i ^ 2 * (nsq p + (2 * ε * p i + ε ^ 2))
        = (2 * ε * p i + ε ^ 2) * (nsq p - p i ^ 2) := by ring
    show p i ^ 2 / nsq p
      < (p i + (if i = i then ε else 0)) ^ 2 / nsq (fun s => p s + (if s = i then ε else 0))
    rw [div_lt_div_iff₀ hNp hNq, hqi, hN]
    linarith

/-- The agent's own net trade has utility minus the level of the price. -/
theorem util_demand (p : S → ℝ) (hp : ∀ s, 0 < p s) (i : S) (β : ℝ) (hβ : 0 < β) :
    util i (fun s => β * proj p i s) = - level i p := by
  have hmem : p ∈ afford (fun s => β * proj p i s) :=
    ⟨hp, (scaled_walras p hp i β).le⟩
  show - sSup (level i '' afford (fun s => β * proj p i s)) = - level i p
  rw [neg_inj]
  apply le_antisymm
  · refine csSup_le ⟨level i p, p, hmem, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    exact rp_level p q hp hq.1 i β hβ hq.2
  · exact le_csSup (bdd i _) ⟨p, hmem, rfl⟩

theorem util_le (p w : S → ℝ) (hp : ∀ s, 0 < p s) (i : S) (hw : ∑ s, p s * w s ≤ 0) :
    util i w ≤ - level i p :=
  neg_le_neg (le_csSup (bdd i w) ⟨p, ⟨hp, hw⟩, rfl⟩)

theorem util_lt (p w : S → ℝ) (hp : ∀ s, 0 < p s) (i j : S) (hj : j ≠ i)
    (hw : ∑ s, p s * w s < 0) : util i w < - level i p := by
  obtain ⟨q, hq, hlt⟩ := exists_higher p w hp i j hj hw
  have h : util i w ≤ - level i q := neg_le_neg (le_csSup (bdd i w) ⟨q, hq, rfl⟩)
  linarith

/-- Pointwise form. -/
theorem decompose_rational [Nontrivial S] (z : S → ℝ) (p : S → ℝ) (hp : ∀ s, 0 < p s)
    (hwal : ∑ s, p s * z s = 0) :
    ∃ g : S → S → ℝ, (∀ t, ∑ i, g i t = z t) ∧
      ∀ i, (∑ s, p s * g i s = 0) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) ≤ 0 → util i w ≤ util i (g i)) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) < 0 → util i w < util i (g i)) := by
  obtain ⟨β, hβ, hsum, hwi⟩ := positive_decomposition p z hp hwal
  refine ⟨fun i s => β i * proj p i s, hsum, fun i => ⟨hwi i, fun w hw => ?_, fun w hw => ?_⟩⟩
  · rw [util_demand p hp i (β i) (hβ i)]
    exact util_le p w hp i hw
  · obtain ⟨j, hj⟩ := exists_ne i
    rw [util_demand p hp i (β i) (hβ i)]
    exact util_lt p w hp i j hj hw

/-- **Sonnenschein–Mantel–Debreu, revealed-preference form.** Any function obeying Walras'
law on strictly positive prices is the sum of the net trades of one utility-maximising,
non-satiated agent per good, the utilities being fixed in advance. -/
theorem mantel_rationalizable [Nontrivial S] (z : (S → ℝ) → (S → ℝ))
    (hwal : ∀ p : S → ℝ, (∀ s, 0 < p s) → ∑ s, p s * z p s = 0) :
    ∃ f : S → (S → ℝ) → (S → ℝ), ∀ p : S → ℝ, (∀ s, 0 < p s) →
      (∀ t, ∑ i, f i p t = z p t) ∧
      ∀ i, (∑ s, p s * f i p s = 0) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) ≤ 0 → util i w ≤ util i (f i p)) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) < 0 → util i w < util i (f i p)) := by
  have h : ∀ p : S → ℝ, ∃ g : S → S → ℝ, (∀ s, 0 < p s) →
      ((∀ t, ∑ i, g i t = z p t) ∧
      ∀ i, (∑ s, p s * g i s = 0) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) ≤ 0 → util i w ≤ util i (g i)) ∧
        (∀ w : S → ℝ, (∑ s, p s * w s) < 0 → util i w < util i (g i))) := by
    intro p
    by_cases hp : ∀ s, 0 < p s
    · obtain ⟨g, hg⟩ := decompose_rational (z p) p hp (hwal p hp)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hp⟩
  choose F hF using h
  exact ⟨fun i p => F p i, fun p hp => hF p hp⟩

/-! ### Stage 287: classical properties of the Mantel utilities -/

theorem level_nonneg (i : S) (q : S → ℝ) : 0 ≤ level i q := by
  unfold level
  exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun s _ => sq_nonneg (q s)))

theorem sSup_level_nonneg (i : S) (A : Set (S → ℝ)) : 0 ≤ sSup (level i '' A) :=
  Real.sSup_nonneg (by rintro _ ⟨q, _, rfl⟩; exact level_nonneg i q)

/-- A larger net trade is affordable at fewer prices. -/
theorem afford_anti (w w' : S → ℝ) (h : ∀ s, w s ≤ w' s) : afford w' ⊆ afford w := by
  rintro q ⟨hq, hqw⟩
  exact ⟨hq, le_trans
    (Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (hq s).le)) hqw⟩

/-- **Monotone.** More of every good is never worse. -/
theorem util_monotone (i : S) (w w' : S → ℝ) (h : ∀ s, w s ≤ w' s) :
    util i w ≤ util i w' := by
  show - sSup (level i '' afford w) ≤ - sSup (level i '' afford w')
  apply neg_le_neg
  rcases (level i '' afford w').eq_empty_or_nonempty with he | hne
  · rw [he, Real.sSup_empty]
    exact sSup_level_nonneg i _
  · exact csSup_le_csSup (bdd i w) hne (Set.image_mono (afford_anti w w' h))

/-- A mixture is affordable only where one of its two parts is. -/
theorem afford_mix (w w' v : S → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv : ∀ s, v s = t * w s + (1 - t) * w' s) : afford v ⊆ afford w ∪ afford w' := by
  rintro q ⟨hq, hqm⟩
  have e : ∑ s, q s * v s = t * ∑ s, q s * w s + (1 - t) * ∑ s, q s * w' s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by rw [hv s]; ring)
  rw [e] at hqm
  by_contra hcon
  have h1 : 0 < ∑ s, q s * w s := by
    by_contra h
    exact hcon (Or.inl ⟨hq, not_lt.1 h⟩)
  have h2 : 0 < ∑ s, q s * w' s := by
    by_contra h
    exact hcon (Or.inr ⟨hq, not_lt.1 h⟩)
  have ha := mul_nonneg ht0 h1.le
  have hb := mul_nonneg (sub_nonneg.2 ht1) h2.le
  have ha0 : t * ∑ s, q s * w s = 0 := by linarith
  have hb0 : (1 - t) * ∑ s, q s * w' s = 0 := by linarith
  rcases mul_eq_zero.1 ha0 with h | h
  · rw [h, sub_zero, one_mul] at hb0
    linarith
  · linarith

/-- **Quasi-concave.** A mixture is at least as good as the worse of its two parts. -/
theorem util_quasiconcave (i : S) (w w' v : S → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv : ∀ s, v s = t * w s + (1 - t) * w' s) :
    min (util i w) (util i w') ≤ util i v := by
  have hsub := afford_mix w w' v t ht0 ht1 hv
  have hle : sSup (level i '' afford v)
      ≤ max (sSup (level i '' afford w)) (sSup (level i '' afford w')) := by
    rcases (level i '' afford v).eq_empty_or_nonempty with he | hne
    · rw [he, Real.sSup_empty]
      exact le_max_of_le_left (sSup_level_nonneg i _)
    · refine csSup_le hne ?_
      rintro _ ⟨q, hq, rfl⟩
      rcases hsub hq with h | h
      · exact le_max_of_le_left (le_csSup (bdd i w) ⟨q, h, rfl⟩)
      · exact le_max_of_le_right (le_csSup (bdd i w') ⟨q, h, rfl⟩)
  show min (- sSup (level i '' afford w)) (- sSup (level i '' afford w'))
    ≤ - sSup (level i '' afford v)
  rcases le_total (sSup (level i '' afford w)) (sSup (level i '' afford w')) with h | h
  · rw [max_eq_right h] at hle
    exact le_trans (min_le_right _ _) (neg_le_neg hle)
  · rw [max_eq_left h] at hle
    exact le_trans (min_le_left _ _) (neg_le_neg hle)

/-- Utility is bounded: it lies between minus one and zero on trades affordable somewhere. -/
theorem util_nonpos (i : S) (w : S → ℝ) : util i w ≤ 0 :=
  neg_nonpos.2 (sSup_level_nonneg i _)

/-- Utility over consumption bundles, given an endowment `ω`. -/
def cutil (i : S) (ω x : S → ℝ) : ℝ := util i (fun s => x s - ω s)

/-- **Monotone on the consumption set.** -/
theorem cutil_monotone (i : S) (ω x x' : S → ℝ) (h : ∀ s, x s ≤ x' s) :
    cutil i ω x ≤ cutil i ω x' :=
  util_monotone i _ _ (fun s => by linarith [h s])

/-- **Quasi-concave on the consumption set** (a mixture of non-negative bundles is
non-negative, so the consumption set `x ≥ 0` is convex). -/
theorem cutil_quasiconcave (i : S) (ω x x' : S → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min (cutil i ω x) (cutil i ω x') ≤ cutil i ω (fun s => t * x s + (1 - t) * x' s) :=
  util_quasiconcave i _ _ _ t ht0 ht1 (fun s => by ring)

/-- The consumption set is convex. -/
theorem consumption_convex (x x' : S → ℝ) (hx : ∀ s, 0 ≤ x s) (hx' : ∀ s, 0 ≤ x' s)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : S) : 0 ≤ t * x s + (1 - t) * x' s := by
  have := mul_nonneg ht0 (hx s)
  have := mul_nonneg (sub_nonneg.2 ht1) (hx' s)
  linarith

/-! ### Stage 292: the Mantel utilities are not continuous -/

/-- A net trade that is non-negative and positive somewhere is affordable at no strictly
positive price, so its utility is `0`, the top value. -/
theorem util_unaffordable (i j : S) (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hj : 0 < w j) :
    util i w = 0 := by
  unfold util
  have he : afford w = ∅ := by
    ext q
    constructor
    · rintro ⟨hq, hsum⟩
      have h1 : q j * w j ≤ ∑ s, q s * w s :=
        Finset.single_le_sum (f := fun s => q s * w s)
          (fun s _ => mul_nonneg (hq s).le (hw s)) (mem_univ j)
      have h2 := mul_pos (hq j) hj
      exfalso
      linarith
    · intro h
      simp at h
  rw [he, Set.image_empty, Real.sSup_empty, neg_zero]

/-- The zero trade has strictly negative utility. -/
theorem util_zero_neg (i : S) : util i 0 < 0 := by
  have hq : (fun _ => (1 : ℝ)) ∈ afford (0 : S → ℝ) := ⟨fun _ => one_pos, by simp⟩
  have h1 := le_csSup (bdd i 0) (Set.mem_image_of_mem (level i) hq)
  have h2 : 0 < level i (fun _ => (1 : ℝ)) := by
    unfold level
    exact div_pos (by norm_num) (nsq_pos _ i (fun _ => one_pos))
  unfold util
  linarith

open Filter Topology in
/-- **The Mantel utilities are discontinuous at the zero trade.**  Arbitrarily small
positive trades `ε eᵢ` have utility `0`, while the zero trade has negative utility. -/
theorem util_not_continuous (i : S) : ¬ ContinuousAt (util i) 0 := by
  intro hc
  have hseq : Tendsto (fun n : ℕ => fun s : S => 1 / ((n : ℝ) + 1) * (if s = i then 1 else 0))
      atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro s
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (if s = i then (1 : ℝ) else 0)
    rw [zero_mul] at this
    exact this
  have h2 := hc.tendsto.comp hseq
  have h3 : (util i ∘ fun n : ℕ => fun s : S => 1 / ((n : ℝ) + 1) * (if s = i then 1 else 0))
      = fun _ => 0 := by
    funext n
    apply util_unaffordable i i
    · intro s
      show 0 ≤ 1 / ((n : ℝ) + 1) * (if s = i then 1 else 0)
      split_ifs <;> positivity
    · show 0 < 1 / ((n : ℝ) + 1) * (if i = i then 1 else 0)
      simp only [↓reduceIte, mul_one]
      positivity
  rw [h3] at h2
  have h4 := tendsto_nhds_unique tendsto_const_nhds h2
  linarith [util_zero_neg i]

end Mantel

end

#print axioms Mantel.util_unaffordable
#print axioms Mantel.util_zero_neg
#print axioms Mantel.util_not_continuous
