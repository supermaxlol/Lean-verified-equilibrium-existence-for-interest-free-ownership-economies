import Mathlib

/-!
Stage 257: the maximum theorem for correspondences.

For a continuous objective `f` and a constraint correspondence `B` with closed graph that
is lower hemicontinuous, the correspondence of maximisers

  `argmax f B p = {x ∈ B p | ∀ y ∈ B p, f (p, y) ≤ f (p, x)}`

has closed graph, is nonempty when `B p` is compact and nonempty, and is convex when `f`
is quasi-concave in the choice.  Two instances are derived:

* `supply` — profit maximisation over a fixed compact convex production set (no strict
  convexity);
* `demand` — utility maximisation over the budget set in a box, for continuous
  quasi-concave utility and strictly positive endowment (no strict concavity).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators Filter Topology

namespace MaximumTheorem

/-- The correspondence of maximisers of `f (p, ·)` over `B p`. -/
def argmax {P X : Type*} (f : P × X → ℝ) (B : P → Set X) (p : P) : Set X :=
  {x | x ∈ B p ∧ ∀ y ∈ B p, f (p, y) ≤ f (p, x)}

/-- **Maximum theorem: closed graph.** -/
theorem argmax_closedGraph {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [FirstCountableTopology P] [FirstCountableTopology X]
    (f : P × X → ℝ) (hf : Continuous f) (B : P → Set X)
    (hBcl : IsClosed {pr : P × X | pr.2 ∈ B pr.1})
    (hlhc : ∀ (p : P) (y : X), y ∈ B p → ∀ q : ℕ → P, Tendsto q atTop (𝓝 p) →
      ∃ w : ℕ → X, (∀ n, w n ∈ B (q n)) ∧ Tendsto w atTop (𝓝 y)) :
    IsClosed {pr : P × X | pr.2 ∈ argmax f B pr.1} := by
  apply IsSeqClosed.isClosed
  intro u l hu hl
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 l.1) := (continuous_fst.tendsto l).comp hl
  have hlB : l.2 ∈ B l.1 := by
    have hmem : l ∈ {pr : P × X | pr.2 ∈ B pr.1} :=
      hBcl.mem_of_tendsto hl (Filter.Eventually.of_forall (fun n => (hu n).1))
    exact hmem
  show l.2 ∈ B l.1 ∧ ∀ y ∈ B l.1, f (l.1, y) ≤ f (l.1, l.2)
  refine ⟨hlB, fun y hy => ?_⟩
  obtain ⟨w, hw, hwy⟩ := hlhc l.1 y hy (fun n => (u n).1) h1
  have ha : Tendsto (fun n => f ((u n).1, w n)) atTop (𝓝 (f (l.1, y))) :=
    (hf.tendsto (l.1, y)).comp (h1.prodMk_nhds hwy)
  have hb : Tendsto (fun n => f ((u n).1, (u n).2)) atTop (𝓝 (f (l.1, l.2))) :=
    (hf.tendsto l).comp hl
  exact le_of_tendsto_of_tendsto' ha hb (fun n => (hu n).2 (w n) (hw n))

/-- **Maximum theorem: nonempty values.** -/
theorem argmax_nonempty {P X : Type*} [TopologicalSpace X]
    (f : P × X → ℝ) (B : P → Set X) (p : P) (hc : IsCompact (B p))
    (hne : (B p).Nonempty) (hf : Continuous (fun x => f (p, x))) :
    (argmax f B p).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, fun y hy => hmax hy⟩

/-- **Maximum theorem: convex values** under quasi-concavity. -/
theorem argmax_convex {P X : Type*} [AddCommMonoid X] [Module ℝ X]
    (f : P × X → ℝ) (B : P → Set X) (p : P)
    (hq : QuasiconcaveOn ℝ (B p) (fun x => f (p, x))) :
    Convex ℝ (argmax f B p) := by
  by_cases hne : (argmax f B p).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have he : argmax f B p = {x | x ∈ B p ∧ f (p, x0) ≤ f (p, x)} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, hx.2 x0 hx0.1⟩
      · intro hx
        exact ⟨hx.1, fun y hy => (hx0.2 y hy).trans hx.2⟩
    rw [he]
    exact hq (f (p, x0))
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact convex_empty

/-! ### Values of bundles -/

variable {S : Type*} [Fintype S]

/-- Value of the bundle `v` at prices `a`. -/
def val (a v : S → ℝ) : ℝ := ∑ s, a s * v s

theorem val_continuous (v : S → ℝ) : Continuous (fun a : S → ℝ => val a v) := by
  unfold val
  exact continuous_finsetSum _ (fun s _ => (continuous_apply s).mul continuous_const)

theorem val_continuous_right (a : S → ℝ) : Continuous (fun v : S → ℝ => val a v) := by
  unfold val
  exact continuous_finsetSum _ (fun s _ => continuous_const.mul (continuous_apply s))

theorem val_continuous_pair :
    Continuous (fun pr : (S → ℝ) × (S → ℝ) => val pr.1 pr.2) := by
  unfold val
  exact continuous_finsetSum _ (fun s _ =>
    ((continuous_apply s).comp continuous_fst).mul ((continuous_apply s).comp continuous_snd))

theorem val_lin (p a b : S → ℝ) (α β : ℝ) :
    val p (α • a + β • b) = α * val p a + β * val p b := by
  simp only [val, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Firm supply over a fixed production set -/

/-- Profit-maximising net outputs in the production set `Y` at prices `p`. -/
def supply (Y : Set (S → ℝ)) (p : S → ℝ) : Set (S → ℝ) :=
  argmax (fun pr : (S → ℝ) × (S → ℝ) => val pr.1 pr.2) (fun _ => Y) p

theorem supply_subset (Y : Set (S → ℝ)) (p : S → ℝ) : supply Y p ⊆ Y :=
  fun _ hx => hx.1

theorem supply_closedGraph (Y : Set (S → ℝ)) (hY : IsClosed Y) :
    IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ supply Y pr.1} :=
  argmax_closedGraph _ val_continuous_pair _ (hY.preimage continuous_snd)
    (fun _ y hy _ _ => ⟨fun _ => y, fun _ => hy, tendsto_const_nhds⟩)

theorem supply_nonempty (Y : Set (S → ℝ)) (hY : IsCompact Y) (hne : Y.Nonempty)
    (p : S → ℝ) : (supply Y p).Nonempty :=
  argmax_nonempty _ _ p hY hne (val_continuous_right p)

theorem supply_convex (Y : Set (S → ℝ)) (hY : Convex ℝ Y) (p : S → ℝ) :
    Convex ℝ (supply Y p) := by
  apply argmax_convex
  intro r a ha b hb α β hα hβ hαβ
  have ha2 : r ≤ val p a := ha.2
  have hb2 : r ≤ val p b := hb.2
  refine ⟨hY ha.1 hb.1 hα hβ hαβ, ?_⟩
  show r ≤ val p (α • a + β • b)
  rw [val_lin]
  have h1 := mul_le_mul_of_nonneg_left ha2 hα
  have h2 := mul_le_mul_of_nonneg_left hb2 hβ
  have h3 : α * r + β * r = r := by rw [← add_mul, hαβ, one_mul]
  linarith

/-! ### Household demand over the budget set -/

/-- The price simplex. -/
def simplex (S : Type*) [Fintype S] : Set (S → ℝ) :=
  {q | (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1}

/-- Budget set inside the box `[0, M]^S` at prices `p` and endowment `ω`. -/
def budget (M : ℝ) (ω p : S → ℝ) : Set (S → ℝ) :=
  {x | (∀ s, 0 ≤ x s ∧ x s ≤ M) ∧ val p x ≤ val p ω}

theorem val_pos (a : S → ℝ) (ha : a ∈ simplex S) (ω : S → ℝ) (hω : ∀ s, 0 < ω s) :
    0 < val a ω := by
  have hex : ∃ s, 0 < a s := by
    by_contra h
    have h' : ∀ s, a s ≤ 0 := fun s => not_lt.1 (fun hs => h ⟨s, hs⟩)
    have h0 : ∑ s, a s ≤ 0 := Finset.sum_nonpos (fun s _ => h' s)
    rw [ha.2] at h0
    linarith
  obtain ⟨s0, hs0⟩ := hex
  unfold val
  exact Finset.sum_pos' (fun s _ => mul_nonneg (ha.1 s) (hω s).le)
    ⟨s0, Finset.mem_univ s0, mul_pos hs0 (hω s0)⟩

theorem budget_convex (M : ℝ) (ω p : S → ℝ) : Convex ℝ (budget M ω p) := by
  intro a ha b hb α β hα hβ hαβ
  have h3 : α * M + β * M = M := by rw [← add_mul, hαβ, one_mul]
  refine ⟨fun s => ⟨?_, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα (ha.1 s).1) (mul_nonneg hβ (hb.1 s).1)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (ha.1 s).2 hα
    have h2 := mul_le_mul_of_nonneg_left (hb.1 s).2 hβ
    linarith
  · rw [val_lin]
    have h1 := mul_le_mul_of_nonneg_left ha.2 hα
    have h2 := mul_le_mul_of_nonneg_left hb.2 hβ
    have h4 : α * val p ω + β * val p ω = val p ω := by rw [← add_mul, hαβ, one_mul]
    linarith

theorem budget_compact (M : ℝ) (ω p : S → ℝ) : IsCompact (budget M ω p) := by
  have hbox : IsClosed {x : S → ℝ | ∀ s, 0 ≤ x s ∧ x s ≤ M} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter (fun s =>
      (isClosed_le continuous_const (continuous_apply s)).inter
        (isClosed_le (continuous_apply s) continuous_const))
  have hcl : IsClosed (budget M ω p) :=
    hbox.inter (isClosed_le (val_continuous_right p) continuous_const)
  have hsub : budget M ω p ⊆ Set.pi Set.univ (fun _ : S => Set.Icc (0:ℝ) M) :=
    fun x hx s _ => hx.1 s
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hcl hsub

theorem budget_nonempty (M : ℝ) (hM : 0 ≤ M) (ω p : S → ℝ) (hp : p ∈ simplex S)
    (hω : ∀ s, 0 ≤ ω s) : (budget M ω p).Nonempty := by
  refine ⟨fun _ => 0, fun _ => ⟨le_rfl, hM⟩, ?_⟩
  have h0 : val p (fun _ => (0:ℝ)) = 0 := by simp [val]
  rw [h0]
  unfold val
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp.1 s) (hω s))

theorem budget_closedGraph (M : ℝ) (ω : S → ℝ) :
    IsClosed {pr : ↥(simplex S) × (S → ℝ) | pr.2 ∈ budget M ω pr.1.1} := by
  have hc2 : ∀ s, Continuous (fun pr : ↥(simplex S) × (S → ℝ) => pr.2 s) :=
    fun s => (continuous_apply s).comp continuous_snd
  have hbox : IsClosed {pr : ↥(simplex S) × (S → ℝ) | ∀ s, 0 ≤ pr.2 s ∧ pr.2 s ≤ M} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter (fun s =>
      (isClosed_le continuous_const (hc2 s)).inter (isClosed_le (hc2 s) continuous_const))
  have hv1 : Continuous (fun pr : ↥(simplex S) × (S → ℝ) => val pr.1.1 pr.2) :=
    val_continuous_pair.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hv2 : Continuous (fun pr : ↥(simplex S) × (S → ℝ) => val pr.1.1 ω) :=
    (val_continuous ω).comp (continuous_subtype_val.comp continuous_fst)
  exact hbox.inter (isClosed_le hv1 hv2)

/-- **The budget correspondence is lower hemicontinuous** on the simplex when the
endowment is strictly positive. -/
theorem budget_lhc (M : ℝ) (ω : S → ℝ) (hω : ∀ s, 0 < ω s) (p : ↥(simplex S))
    (y : S → ℝ) (hy : y ∈ budget M ω p.1) (q : ℕ → ↥(simplex S))
    (hq : Tendsto q atTop (𝓝 p)) :
    ∃ w : ℕ → (S → ℝ), (∀ n, w n ∈ budget M ω (q n).1) ∧ Tendsto w atTop (𝓝 y) := by
  have hpos : ∀ a : ↥(simplex S), 0 < val a.1 ω := fun a => val_pos a.1 a.2 ω hω
  have hmaxpos : ∀ n, 0 < max (val (q n).1 y) (val (q n).1 ω) :=
    fun n => lt_max_of_lt_right (hpos (q n))
  have ht0 : ∀ n, 0 ≤ val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) :=
    fun n => div_nonneg (hpos (q n)).le (hmaxpos n).le
  have ht1 : ∀ n, val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) ≤ 1 :=
    fun n => (div_le_one (hmaxpos n)).2 (le_max_right _ _)
  refine ⟨fun n s => val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) * y s,
    fun n => ⟨fun s => ⟨mul_nonneg (ht0 n) (hy.1 s).1, ?_⟩, ?_⟩, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (ht1 n) (hy.1 s).1
    have h' := (hy.1 s).2
    linarith
  · have hv : val (q n).1
          (fun s => val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) * y s)
        = val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) * val (q n).1 y := by
      simp only [val, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [hv]
    have h1 : val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω) * val (q n).1 y
        ≤ val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω)
          * max (val (q n).1 y) (val (q n).1 ω) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (ht0 n)
    have h2 : val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω)
        * max (val (q n).1 y) (val (q n).1 ω) = val (q n).1 ω :=
      div_mul_cancel₀ _ (hmaxpos n).ne'
    linarith
  · have hqv : Tendsto (fun n => (q n).1) atTop (𝓝 p.1) :=
      (continuous_subtype_val.tendsto p).comp hq
    have hω' : Tendsto (fun n => val (q n).1 ω) atTop (𝓝 (val p.1 ω)) :=
      ((val_continuous ω).tendsto p.1).comp hqv
    have hy' : Tendsto (fun n => val (q n).1 y) atTop (𝓝 (val p.1 y)) :=
      ((val_continuous y).tendsto p.1).comp hqv
    have hmax : max (val p.1 y) (val p.1 ω) = val p.1 ω := max_eq_right hy.2
    have htt : Tendsto (fun n => val (q n).1 ω / max (val (q n).1 y) (val (q n).1 ω))
        atTop (𝓝 1) := by
      have h := hω'.div (hy'.max hω') (by rw [hmax]; exact (hpos p).ne')
      rw [hmax, div_self (hpos p).ne'] at h
      exact h
    rw [tendsto_pi_nhds]
    intro s
    have h := htt.mul_const (y s)
    rw [one_mul] at h
    exact h

/-- Utility-maximising bundles in the budget set. -/
def demand (U : (S → ℝ) → ℝ) (M : ℝ) (ω : S → ℝ) (p : ↥(simplex S)) : Set (S → ℝ) :=
  argmax (fun pr : ↥(simplex S) × (S → ℝ) => U pr.2) (fun a => budget M ω a.1) p

theorem demand_subset (U : (S → ℝ) → ℝ) (M : ℝ) (ω : S → ℝ) (p : ↥(simplex S)) :
    demand U M ω p ⊆ budget M ω p.1 :=
  fun _ hx => hx.1

theorem demand_closedGraph (U : (S → ℝ) → ℝ) (hU : Continuous U) (M : ℝ) (ω : S → ℝ)
    (hω : ∀ s, 0 < ω s) :
    IsClosed {pr : ↥(simplex S) × (S → ℝ) | pr.2 ∈ demand U M ω pr.1} :=
  argmax_closedGraph _ (hU.comp continuous_snd) _ (budget_closedGraph M ω)
    (budget_lhc M ω hω)

theorem demand_nonempty (U : (S → ℝ) → ℝ) (hU : Continuous U) (M : ℝ) (hM : 0 ≤ M)
    (ω : S → ℝ) (hω : ∀ s, 0 ≤ ω s) (p : ↥(simplex S)) : (demand U M ω p).Nonempty :=
  argmax_nonempty _ _ p (budget_compact M ω p.1) (budget_nonempty M hM ω p.1 p.2 hω) hU

theorem demand_convex (U : (S → ℝ) → ℝ) (hUq : QuasiconcaveOn ℝ Set.univ U) (M : ℝ)
    (ω : S → ℝ) (p : ↥(simplex S)) : Convex ℝ (demand U M ω p) := by
  apply argmax_convex
  intro r a ha b hb α β hα hβ hαβ
  have ha2 : r ≤ U a := ha.2
  have hb2 : r ≤ U b := hb.2
  refine ⟨budget_convex M ω p.1 ha.1 hb.1 hα hβ hαβ, ?_⟩
  exact (hUq r ⟨Set.mem_univ a, ha2⟩ ⟨Set.mem_univ b, hb2⟩ hα hβ hαβ).2

end MaximumTheorem

end

#print axioms MaximumTheorem.argmax_closedGraph
#print axioms MaximumTheorem.argmax_nonempty
#print axioms MaximumTheorem.argmax_convex
#print axioms MaximumTheorem.supply_closedGraph
#print axioms MaximumTheorem.supply_nonempty
#print axioms MaximumTheorem.supply_convex
#print axioms MaximumTheorem.budget_lhc
#print axioms MaximumTheorem.budget_closedGraph
#print axioms MaximumTheorem.budget_compact
#print axioms MaximumTheorem.demand_closedGraph
#print axioms MaximumTheorem.demand_nonempty
#print axioms MaximumTheorem.demand_convex
