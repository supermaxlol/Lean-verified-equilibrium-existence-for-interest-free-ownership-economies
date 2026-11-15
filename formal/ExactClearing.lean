import GEOverlap

set_option linter.unusedSectionVars false

/-!
Stage 242 (draft): Gale–Nikaido–Debreu for excess-demand CORRESPONDENCES (convex-valued
demand) — upstream target ①.

Generalizes `gale_nikaido_debreu` from a continuous excess-demand FUNCTION to a convex-valued,
closed-graph excess-demand CORRESPONDENCE `Z`. This removes the strict-concavity crutch: a
quasi-concave household has a convex (not necessarily singleton) demand set, and the
aggregate excess demand is then a correspondence, not a function.

Method: Kakutani on the product `priceSimplex ×ˢ K`, with the correspondence
`(p,x) ↦ priceAdjust x ×ˢ Z p` (auctioneer raises the price of goods in excess demand `x`,
households re-choose demand at `p`). A fixed point `(p,x)` has `p ∈ priceAdjust x` and
`x ∈ Z p`; Walras `p·x ≤ 0` then forces `x ≤ 0`.
-/

noncomputable section
open scoped BigOperators
open GEOverlap

namespace SetValuedGND

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Price-adjustment correspondence toward a fixed excess-demand vector `x`: the simplex
prices maximizing the value `∑ q·x`. -/
def priceAdjust (x : S → ℝ) : Set (S → ℝ) :=
  {q | q ∈ priceSimplex S ∧ ∀ q' ∈ priceSimplex S, (∑ s, q' s * x s) ≤ (∑ s, q s * x s)}

theorem priceAdjust_nonempty (x : S → ℝ) : (priceAdjust x).Nonempty := by
  have hcont : ContinuousOn (fun q => ∑ s, q s * x s) (priceSimplex S) :=
    (continuous_finsetSum _ (fun s _ => (continuous_apply s).mul continuous_const)).continuousOn
  obtain ⟨q, hq, hmax⟩ := priceSimplex_compact.exists_isMaxOn priceSimplex_nonempty hcont
  exact ⟨q, hq, fun q' hq' => hmax hq'⟩

theorem priceAdjust_convex (x : S → ℝ) : Convex ℝ (priceAdjust x) := by
  intro a ha b hb α β hα hβ hαβ
  refine ⟨priceSimplex_convex ha.1 hb.1 hα hβ hαβ, fun q' hq' => ?_⟩
  have hlin : ∑ s, (α • a + β • b) s * x s
      = α * (∑ s, a s * x s) + β * (∑ s, b s * x s) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hlin]
  have h1 := ha.2 q' hq'
  have h2 := hb.2 q' hq'
  have key := add_le_add (mul_le_mul_of_nonneg_left h1 hα) (mul_le_mul_of_nonneg_left h2 hβ)
  have hsum : α * (∑ s, q' s * x s) + β * (∑ s, q' s * x s) = ∑ s, q' s * x s := by
    rw [← add_mul, hαβ, one_mul]
  linarith [key, hsum]

/-- **Set-valued Gale–Nikaido–Debreu.** A convex-valued, closed-graph excess-demand
correspondence `Z` with values in a compact convex set `K` and obeying Walras' law
(`p·x ≤ 0` for every selection `x ∈ Z p` at a simplex price) has a clearing price: some
`p ∈ simplex` and `x ∈ Z p` with `x ≤ 0` in every good. -/
theorem setValued_gnd
    (K : Set (S → ℝ)) (hKcvx : Convex ℝ K) (hKcmp : IsCompact K) (hKne : K.Nonempty)
    (Z : (S → ℝ) → Set (S → ℝ))
    (hZsub : ∀ p, Z p ⊆ K) (hZcvx : ∀ p, Convex ℝ (Z p)) (hZne : ∀ p, (Z p).Nonempty)
    (hZcg : IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ Z pr.1})
    (hwal : ∀ p ∈ priceSimplex S, ∀ x ∈ Z p, (∑ s, p s * x s) ≤ 0) :
    ∃ p ∈ priceSimplex S, ∃ x ∈ Z p, ∀ s, x s ≤ 0 := by
  classical
  set V := (S → ℝ) × (S → ℝ)
  set D : Set V := priceSimplex S ×ˢ K with hD
  have hDcvx : Convex ℝ D := by rw [hD]; exact priceSimplex_convex.prod hKcvx
  have hDcmp : IsCompact D := by rw [hD]; exact priceSimplex_compact.prod hKcmp
  have hDne : D.Nonempty := by rw [hD]; exact priceSimplex_nonempty.prod hKne
  set Φ : D → Set V := fun z => priceAdjust z.1.2 ×ˢ Z z.1.1 with hΦ
  -- values
  have hΦval : ∀ z : D, Φ z ⊆ D ∧ Convex ℝ (Φ z) ∧ (Φ z).Nonempty := by
    intro z
    refine ⟨?_, (priceAdjust_convex z.1.2).prod (hZcvx z.1.1),
      (priceAdjust_nonempty z.1.2).prod (hZne z.1.1)⟩
    rw [hD, hΦ]
    exact Set.prod_mono (fun q hq => hq.1) (hZsub z.1.1)
  -- closed graph
  have hq21 : Continuous (fun w : D × V => (w.2.1 : S → ℝ)) := continuous_fst.comp continuous_snd
  have hq22 : Continuous (fun w : D × V => (w.2.2 : S → ℝ)) := continuous_snd.comp continuous_snd
  have hp111 : Continuous (fun w : D × V => (w.1.1.1 : S → ℝ)) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hx112 : Continuous (fun w : D × V => (w.1.1.2 : S → ℝ)) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hΦcg : closedGraph Φ := by
    have hSet2 : IsClosed {w : D × V | w.2.2 ∈ Z w.1.1.1} :=
      hZcg.preimage (hp111.prodMk hq22)
    have hSet1a : IsClosed {w : D × V | (w.2.1 : S → ℝ) ∈ priceSimplex S} :=
      priceSimplex_compact.isClosed.preimage hq21
    have hSet1b : IsClosed {w : D × V | ∀ q' ∈ priceSimplex S,
        (∑ s, q' s * w.1.1.2 s) ≤ (∑ s, w.2.1 s * w.1.1.2 s)} := by
      have hrw : {w : D × V | ∀ q' ∈ priceSimplex S,
            (∑ s, q' s * w.1.1.2 s) ≤ (∑ s, w.2.1 s * w.1.1.2 s)}
          = ⋂ q', ⋂ (_ : q' ∈ priceSimplex S),
              {w : D × V | (∑ s, q' s * w.1.1.2 s) ≤ (∑ s, w.2.1 s * w.1.1.2 s)} := by
        ext w; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      rw [hrw]
      refine isClosed_iInter (fun q' => isClosed_iInter (fun _ => isClosed_le ?_ ?_))
      · exact continuous_finsetSum _ (fun s _ =>
          continuous_const.mul ((continuous_apply s).comp hx112))
      · exact continuous_finsetSum _ (fun s _ =>
          ((continuous_apply s).comp hq21).mul ((continuous_apply s).comp hx112))
    have heq : {w : D × V | w.2 ∈ Φ w.1}
        = ({w : D × V | (w.2.1 : S → ℝ) ∈ priceSimplex S}
            ∩ {w : D × V | ∀ q' ∈ priceSimplex S,
                (∑ s, q' s * w.1.1.2 s) ≤ (∑ s, w.2.1 s * w.1.1.2 s)})
          ∩ {w : D × V | w.2.2 ∈ Z w.1.1.1} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hΦ]
      rw [Set.mem_prod]
      simp only [priceAdjust, Set.mem_ofPred_eq]
    show IsClosed {w : D × V | w.2 ∈ Φ w.1}
    rw [heq]
    exact (hSet1a.inter hSet1b).inter hSet2
  -- Kakutani
  obtain ⟨z, hz⟩ := kakutani_fixed_point D hDcvx hDcmp hDne Φ hΦcg hΦval
  rw [hΦ] at hz
  rw [Set.mem_prod] at hz
  obtain ⟨hp_adj, hx_Z⟩ := hz
  -- hp_adj : z.1.1 ∈ priceAdjust z.1.2 ; hx_Z : z.1.2 ∈ Z z.1.1
  obtain ⟨hp_simplex, hp_max⟩ := hp_adj
  have hwx : (∑ s, z.1.1 s * z.1.2 s) ≤ 0 := hwal z.1.1 hp_simplex z.1.2 hx_Z
  refine ⟨z.1.1, hp_simplex, z.1.2, hx_Z, fun t => ?_⟩
  set et : S → ℝ := fun s => if s = t then 1 else 0 with het_def
  have het : et ∈ priceSimplex S := by
    refine ⟨fun s => ?_, ?_⟩
    · by_cases h : s = t <;> simp [het_def, h]
    · simp [het_def, Finset.sum_ite_eq']
  have hb := hp_max et het
  have hetval : (∑ s, et s * z.1.2 s) = z.1.2 t := by
    simp only [het_def, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']; simp
  rw [hetval] at hb
  linarith [hwx, hb]

end SetValuedGND


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


/-!
Stage 260: Arrow–Debreu existence with production, from primitives.

Primitives: finitely many households with continuous quasi-concave utility, strictly
positive endowments and non-negative profit shares summing to one; one compact convex
production set containing inaction; consumption sets `[0, M]^S`.

`Economy.equilibrium_exists` — there are a simplex price `p`, a production plan `y` that
maximises profit over the production set, and consumption bundles `x i` that maximise
utility over each household's budget set (endowment value plus profit share), with total
consumption no larger than total endowment plus net output in every good.

No strict concavity or strict convexity is assumed: demand and supply are correspondences,
built with the maximum theorem above and cleared with the set-valued
Gale–Nikaido–Debreu theorem.
-/

noncomputable section

open BigOperators Filter Topology MaximumTheorem

namespace ArrowDebreu

variable {I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

/-! ### A continuous retraction of price space onto the simplex -/

def posSum (p : S → ℝ) : ℝ := ∑ s, max (p s) 0

def gap (p : S → ℝ) : ℝ := |1 - posSum p|

def retr (p : S → ℝ) : S → ℝ :=
  fun s => (max (p s) 0 + gap p / (Fintype.card S : ℝ)) / (posSum p + gap p)

theorem den_pos (p : S → ℝ) : 0 < posSum p + gap p := by
  have h := le_abs_self (1 - posSum p)
  unfold gap
  linarith

theorem retr_mem (p : S → ℝ) : retr p ∈ priceSimplex S := by
  have hd := den_pos p
  have hn : (0:ℝ) < (Fintype.card S : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hg : 0 ≤ gap p := abs_nonneg _
  refine ⟨fun s => ?_, ?_⟩
  · show 0 ≤ (max (p s) 0 + gap p / (Fintype.card S : ℝ)) / (posSum p + gap p)
    exact div_nonneg (add_nonneg (le_max_right _ _) (div_nonneg hg hn.le)) hd.le
  · show ∑ s, (max (p s) 0 + gap p / (Fintype.card S : ℝ)) / (posSum p + gap p) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have h : (Fintype.card S : ℝ) * (gap p / (Fintype.card S : ℝ)) = gap p := by
      have := hn.ne'
      field_simp
    rw [h]
    exact div_self hd.ne'

theorem retr_fix (p : S → ℝ) (hp : p ∈ priceSimplex S) : retr p = p := by
  have hT : posSum p = 1 := by
    have h : posSum p = ∑ s, p s := Finset.sum_congr rfl (fun s _ => max_eq_left (hp.1 s))
    rw [h, hp.2]
  have hg : gap p = 0 := by
    unfold gap
    rw [hT]
    simp
  funext s
  show (max (p s) 0 + gap p / (Fintype.card S : ℝ)) / (posSum p + gap p) = p s
  rw [hT, hg, max_eq_left (hp.1 s)]
  simp

theorem retr_continuous : Continuous (retr : (S → ℝ) → S → ℝ) := by
  have hT : Continuous (posSum : (S → ℝ) → ℝ) :=
    continuous_finsetSum _ (fun s _ => (continuous_apply s).max continuous_const)
  have hg : Continuous (gap : (S → ℝ) → ℝ) :=
    continuous_abs.comp (continuous_const.sub hT)
  apply continuous_pi
  intro s
  exact (((continuous_apply s).max continuous_const).add (hg.div_const _)).div
    (hT.add hg) (fun p => (den_pos p).ne')

/-! ### Profit -/

/-- Maximal profit over the production set at prices `a`. -/
def profit (Y : Set (S → ℝ)) (a : S → ℝ) : ℝ := sSup ((fun y => val a y) '' Y)

theorem profit_continuous (Y : Set (S → ℝ)) (hY : IsCompact Y) : Continuous (profit Y) :=
  hY.continuous_sSup (f := fun (a : S → ℝ) (y : S → ℝ) => val a y) val_continuous_pair

theorem le_profit (Y : Set (S → ℝ)) (hY : IsCompact Y) (a y : S → ℝ) (hy : y ∈ Y) :
    val a y ≤ profit Y a :=
  le_csSup (hY.image (val_continuous_right a)).bddAbove (Set.mem_image_of_mem _ hy)

theorem profit_eq (Y : Set (S → ℝ)) (hY : IsCompact Y) (a y : S → ℝ) (hy : y ∈ supply Y a) :
    val a y = profit Y a :=
  le_antisymm (le_profit Y hY a y hy.1)
    (csSup_le ⟨_, Set.mem_image_of_mem _ hy.1⟩
      (by rintro _ ⟨y', hy', rfl⟩; exact hy.2 y' hy'))

theorem profit_nonneg (Y : Set (S → ℝ)) (hY : IsCompact Y) (h0 : (0 : S → ℝ) ∈ Y)
    (a : S → ℝ) : 0 ≤ profit Y a := by
  have h := le_profit Y hY a 0 h0
  have h' : val a (0 : S → ℝ) = 0 := by simp [val]
  linarith

/-! ### Budget sets with a wealth level -/

def budgetW (M : ℝ) (a : S → ℝ) (w : ℝ) : Set (S → ℝ) :=
  {x | (∀ s, 0 ≤ x s ∧ x s ≤ M) ∧ val a x ≤ w}

theorem box_closed {T : Type*} [TopologicalSpace T] (M : ℝ) (g : T → S → ℝ)
    (hg : Continuous g) : IsClosed {t : T | ∀ s, 0 ≤ g t s ∧ g t s ≤ M} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  exact isClosed_iInter (fun s =>
    (isClosed_le continuous_const ((continuous_apply s).comp hg)).inter
      (isClosed_le ((continuous_apply s).comp hg) continuous_const))

theorem budgetW_convex (M : ℝ) (a : S → ℝ) (w : ℝ) : Convex ℝ (budgetW M a w) := by
  intro x hx y hy α β hα hβ hαβ
  have h3 : α * M + β * M = M := by rw [← add_mul, hαβ, one_mul]
  refine ⟨fun s => ⟨?_, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα (hx.1 s).1) (mul_nonneg hβ (hy.1 s).1)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.1 s).2 hα
    have h2 := mul_le_mul_of_nonneg_left (hy.1 s).2 hβ
    linarith
  · rw [val_lin]
    have h1 := mul_le_mul_of_nonneg_left hx.2 hα
    have h2 := mul_le_mul_of_nonneg_left hy.2 hβ
    have h4 : α * w + β * w = w := by rw [← add_mul, hαβ, one_mul]
    linarith

theorem budgetW_compact (M : ℝ) (a : S → ℝ) (w : ℝ) : IsCompact (budgetW M a w) := by
  have hcl : IsClosed (budgetW M a w) :=
    (box_closed M (fun x : S → ℝ => x) continuous_id).inter
      (isClosed_le (val_continuous_right a) continuous_const)
  have hsub : budgetW M a w ⊆ Set.pi Set.univ (fun _ : S => Set.Icc (0:ℝ) M) :=
    fun x hx s _ => hx.1 s
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hcl hsub

theorem budgetW_closedGraph (M : ℝ) (a : (S → ℝ) → (S → ℝ)) (ha : Continuous a)
    (W : (S → ℝ) → ℝ) (hW : Continuous W) :
    IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ budgetW M (a pr.1) (W pr.1)} := by
  have hv : Continuous (fun pr : (S → ℝ) × (S → ℝ) => val (a pr.1) pr.2) :=
    val_continuous_pair.comp ((ha.comp continuous_fst).prodMk continuous_snd)
  exact (box_closed M (fun pr : (S → ℝ) × (S → ℝ) => pr.2) continuous_snd).inter
    (isClosed_le hv (hW.comp continuous_fst))

/-- Scaling factor that brings a bundle of value `v` inside wealth `w`. -/
def scale (w v : ℝ) : ℝ := w / max v w

theorem scale_nonneg (w v : ℝ) (hw : 0 < w) : 0 ≤ scale w v :=
  div_nonneg hw.le (lt_max_of_lt_right hw).le

theorem scale_le_one (w v : ℝ) (hw : 0 < w) : scale w v ≤ 1 :=
  (div_le_one (lt_max_of_lt_right hw)).2 (le_max_right _ _)

theorem scale_mul_le (w v : ℝ) (hw : 0 < w) : scale w v * v ≤ w := by
  have h1 : scale w v * v ≤ scale w v * max v w :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (scale_nonneg w v hw)
  have h2 : scale w v * max v w = w := div_mul_cancel₀ _ (lt_max_of_lt_right hw).ne'
  linarith

/-- The budget correspondence is lower hemicontinuous when wealth is continuous and
strictly positive. -/
theorem budgetW_lhc (M : ℝ) (a : (S → ℝ) → (S → ℝ)) (ha : Continuous a)
    (W : (S → ℝ) → ℝ) (hW : Continuous W) (hWpos : ∀ p, 0 < W p)
    (p y : S → ℝ) (hy : y ∈ budgetW M (a p) (W p)) (q : ℕ → S → ℝ)
    (hq : Tendsto q atTop (𝓝 p)) :
    ∃ w : ℕ → (S → ℝ), (∀ n, w n ∈ budgetW M (a (q n)) (W (q n))) ∧
      Tendsto w atTop (𝓝 y) := by
  refine ⟨fun n s => scale (W (q n)) (val (a (q n)) y) * y s,
    fun n => ⟨fun s => ⟨mul_nonneg (scale_nonneg _ _ (hWpos _)) (hy.1 s).1, ?_⟩, ?_⟩, ?_⟩
  · have h := mul_le_mul_of_nonneg_right
      (scale_le_one (W (q n)) (val (a (q n)) y) (hWpos _)) (hy.1 s).1
    have h' := (hy.1 s).2
    linarith
  · have hv : val (a (q n)) (fun s => scale (W (q n)) (val (a (q n)) y) * y s)
        = scale (W (q n)) (val (a (q n)) y) * val (a (q n)) y := by
      simp only [val, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    show val (a (q n)) (fun s => scale (W (q n)) (val (a (q n)) y) * y s) ≤ W (q n)
    rw [hv]
    exact scale_mul_le _ _ (hWpos _)
  · have hW' : Tendsto (fun n => W (q n)) atTop (𝓝 (W p)) := (hW.tendsto p).comp hq
    have hv' : Tendsto (fun n => val (a (q n)) y) atTop (𝓝 (val (a p) y)) :=
      ((val_continuous y).tendsto (a p)).comp ((ha.tendsto p).comp hq)
    have hmax : max (val (a p) y) (W p) = W p := max_eq_right hy.2
    have htt : Tendsto (fun n => scale (W (q n)) (val (a (q n)) y)) atTop (𝓝 1) := by
      have h := hW'.div (hv'.max hW') (by rw [hmax]; exact (hWpos p).ne')
      rw [hmax, div_self (hWpos p).ne'] at h
      exact h
    rw [tendsto_pi_nhds]
    intro s
    have h := htt.mul_const (y s)
    rw [one_mul] at h
    exact h

/-! ### Small-step lemmas -/

theorem small_step (M : ℝ) (x x' : S → ℝ) (hx : ∀ s, x s + 1 ≤ M) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ s, (1 - t) * x s + t * x' s ≤ M := by
  have hD0 : 0 ≤ ∑ s, |x' s - x s| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpos : 0 < ∑ s, |x' s - x s| + 2 := by linarith
  refine ⟨1 / (∑ s, |x' s - x s| + 2), div_pos one_pos hpos,
    by rw [div_lt_one hpos]; linarith, fun s => ?_⟩
  have h1 : |x' s - x s| ≤ ∑ s, |x' s - x s| :=
    Finset.single_le_sum (f := fun s => |x' s - x s|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)
  have h2 := le_abs_self (x' s - x s)
  have h3 : 1 / (∑ s, |x' s - x s| + 2) * (x' s - x s) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
    linarith
  have h4 := hx s
  have h5 : (1 - 1 / (∑ s, |x' s - x s| + 2)) * x s + 1 / (∑ s, |x' s - x s| + 2) * x' s
      = x s + 1 / (∑ s, |x' s - x s| + 2) * (x' s - x s) := by ring
  linarith

theorem small_scalar (g a : ℝ) (hg : 0 < g) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * a ≤ g := by
  have hA := abs_nonneg a
  have hden : 0 < |a| + g + 1 := by linarith
  refine ⟨g / (|a| + g + 1), div_pos hg hden, by rw [div_lt_one hden]; linarith, ?_⟩
  have h1 : g / (|a| + g + 1) * a ≤ g / (|a| + g + 1) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) (div_pos hg hden).le
  have h2 : g / (|a| + g + 1) * |a| ≤ g := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [mul_pos hg hg, mul_nonneg hg.le hA]
  linarith

/-- Budget set without an upper bound on consumption. -/
def budgetU (a : S → ℝ) (w : ℝ) : Set (S → ℝ) := {x | (∀ s, 0 ≤ x s) ∧ val a x ≤ w}

/-- A concave utility is semi-strictly quasi-concave. -/
theorem semistrict_of_concave (U : (S → ℝ) → ℝ) (hU : ConcaveOn ℝ Set.univ U)
    (x x' : S → ℝ) (h : U x < U x') (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    U x < U ((1 - t) • x + t • x') := by
  have h1 := hU.2 (Set.mem_univ x) (Set.mem_univ x') (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
    (by ring)
  simp only [smul_eq_mul] at h1
  nlinarith [mul_pos ht0 (sub_pos.2 h)]

/-- With semi-strict quasi-concavity and non-satiation, an optimal bundle exhausts the
budget. -/
theorem budget_binds (U : (S → ℝ) → ℝ)
    (hss : ∀ x x' : S → ℝ, U x < U x' → ∀ t : ℝ, 0 < t → t < 1 →
      U x < U ((1 - t) • x + t • x'))
    (hns : ∀ x : S → ℝ, (∀ s, 0 ≤ x s) → ∃ x' : S → ℝ, (∀ s, 0 ≤ x' s) ∧ U x < U x')
    (p : S → ℝ) (w : ℝ) (x : S → ℝ) (hx : x ∈ budgetU p w)
    (hopt : ∀ x' ∈ budgetU p w, U x' ≤ U x) : val p x = w := by
  by_contra hne
  have hlt : val p x < w := lt_of_le_of_ne hx.2 hne
  obtain ⟨x', hx'0, hU⟩ := hns x hx.1
  obtain ⟨t, ht0, ht1, ht⟩ := small_scalar (w - val p x) (val p x' - val p x) (by linarith)
  have hz : (1 - t) • x + t • x' ∈ budgetU p w := by
    refine ⟨fun s => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg (by linarith) (hx.1 s)) (mul_nonneg ht0.le (hx'0 s))
    · rw [val_lin]
      linarith
  exact absurd (hopt _ hz) (not_le.2 (hss x x' hU t ht0 ht1))

/-! ### The economy -/

/-- A private-ownership economy with several firms. -/
structure Economy (I J S : Type*) [Fintype I] [Fintype J] [Fintype S] where
  U : I → (S → ℝ) → ℝ
  U_cont : ∀ i, Continuous (U i)
  U_qc : ∀ i, QuasiconcaveOn ℝ Set.univ (U i)
  ω : I → S → ℝ
  ω_pos : ∀ i s, 0 < ω i s
  θ : I → J → ℝ
  θ_nonneg : ∀ i j, 0 ≤ θ i j
  θ_sum : ∀ j, ∑ i, θ i j = 1
  Y : J → Set (S → ℝ)
  Y_compact : ∀ j, IsCompact (Y j)
  Y_convex : ∀ j, Convex ℝ (Y j)
  Y_zero : ∀ j, (0 : S → ℝ) ∈ Y j
  M : ℝ
  M_nonneg : 0 ≤ M

namespace Economy

variable {J : Type*} [Fintype J] (E : Economy I J S)

def wealth (i : I) (p : S → ℝ) : ℝ :=
  val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p)

theorem wealth_continuous (i : I) : Continuous (E.wealth i) :=
  ((val_continuous (E.ω i)).comp retr_continuous).add
    (continuous_finsetSum _ (fun j _ => continuous_const.mul
      ((profit_continuous (E.Y j) (E.Y_compact j)).comp retr_continuous)))

theorem wealth_pos (i : I) (p : S → ℝ) : 0 < E.wealth i p := by
  have h1 := val_pos (retr p) (retr_mem p) (E.ω i) (E.ω_pos i)
  have h2 : 0 ≤ ∑ j, E.θ i j * profit (E.Y j) (retr p) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (E.θ_nonneg i j)
      (profit_nonneg (E.Y j) (E.Y_compact j) (E.Y_zero j) (retr p)))
  show 0 < val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p)
  linarith

def dem (i : I) (p : S → ℝ) : Set (S → ℝ) :=
  argmax (fun pr : (S → ℝ) × (S → ℝ) => E.U i pr.2)
    (fun q => budgetW E.M (retr q) (E.wealth i q)) p

theorem dem_closed (i : I) :
    IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.dem i pr.1} :=
  argmax_closedGraph _ ((E.U_cont i).comp continuous_snd) _
    (budgetW_closedGraph E.M retr retr_continuous _ (E.wealth_continuous i))
    (budgetW_lhc E.M retr retr_continuous _ (E.wealth_continuous i) (E.wealth_pos i))

theorem dem_nonempty (i : I) (p : S → ℝ) : (E.dem i p).Nonempty := by
  have hne : (budgetW E.M (retr p) (E.wealth i p)).Nonempty := by
    refine ⟨fun _ => 0, fun _ => ⟨le_rfl, E.M_nonneg⟩, ?_⟩
    have h0 : val (retr p) (fun _ => (0:ℝ)) = 0 := by simp [val]
    rw [h0]
    exact (E.wealth_pos i p).le
  exact argmax_nonempty _ _ p (budgetW_compact _ _ _) hne (E.U_cont i)

theorem dem_convex (i : I) (p : S → ℝ) : Convex ℝ (E.dem i p) := by
  apply argmax_convex
  intro r a ha b hb α β hα hβ hαβ
  have ha2 : r ≤ E.U i a := ha.2
  have hb2 : r ≤ E.U i b := hb.2
  refine ⟨budgetW_convex _ _ _ ha.1 hb.1 hα hβ hαβ, ?_⟩
  exact (E.U_qc i r ⟨Set.mem_univ a, ha2⟩ ⟨Set.mem_univ b, hb2⟩ hα hβ hαβ).2

def net (pr : (I → S → ℝ) × (J → S → ℝ)) : S → ℝ :=
  ∑ i, pr.1 i - ∑ i, E.ω i - ∑ j, pr.2 j

theorem net_apply (pr : (I → S → ℝ) × (J → S → ℝ)) (s : S) :
    E.net pr s = ∑ i, pr.1 i s - ∑ i, E.ω i s - ∑ j, pr.2 j s := by
  simp [net, Finset.sum_apply]

theorem net_continuous : Continuous E.net := by
  show Continuous (fun pr : (I → S → ℝ) × (J → S → ℝ) =>
    ∑ i, pr.1 i - ∑ i, E.ω i - ∑ j, pr.2 j)
  exact ((continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_fst)).sub
    continuous_const).sub
    (continuous_finsetSum _ (fun j _ => (continuous_apply j).comp continuous_snd))

theorem net_image_convex (A : Set ((I → S → ℝ) × (J → S → ℝ))) (hA : Convex ℝ A) :
    Convex ℝ (E.net '' A) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ a b ha hb hab
  refine ⟨a • u + b • v, hA hu hv ha hb hab, ?_⟩
  funext s
  simp only [E.net_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb' : b = 1 - a := by linarith
  subst hb'
  ring

theorem val_net (p : S → ℝ) (c : (I → S → ℝ) × (J → S → ℝ)) :
    val p (E.net c)
      = ∑ i, val p (c.1 i) - ∑ i, val p (E.ω i) - ∑ j, val p (c.2 j) := by
  have e1 : ∑ s, ∑ i, p s * c.1 i s = ∑ i, ∑ s, p s * c.1 i s := Finset.sum_comm
  have e2 : ∑ s, ∑ i, p s * E.ω i s = ∑ i, ∑ s, p s * E.ω i s := Finset.sum_comm
  have e3 : ∑ s, ∑ j, p s * c.2 j s = ∑ j, ∑ s, p s * c.2 j s := Finset.sum_comm
  unfold val
  simp only [E.net_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [e1, e2, e3]

def prof (p : S → ℝ) : Set ((I → S → ℝ) × (J → S → ℝ)) :=
  {x | ∀ i, x i ∈ E.dem i p} ×ˢ {y | ∀ j, y j ∈ supply (E.Y j) (retr p)}

def boxP : Set ((I → S → ℝ) × (J → S → ℝ)) :=
  (Set.pi Set.univ (fun _ : I => Set.pi Set.univ (fun _ : S => Set.Icc (0:ℝ) E.M))) ×ˢ
    (Set.pi Set.univ (fun j : J => E.Y j))

def N (p : S → ℝ) : Set (S → ℝ) := E.net '' E.prof p

theorem boxP_compact : IsCompact E.boxP :=
  (isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))).prod
    (isCompact_univ_pi (fun j => E.Y_compact j))

theorem boxP_convex : Convex ℝ E.boxP :=
  (convex_pi (fun _ _ => convex_pi (fun _ _ => convex_Icc 0 E.M))).prod
    (convex_pi (fun j _ => E.Y_convex j))

theorem prof_sub (p : S → ℝ) : E.prof p ⊆ E.boxP :=
  fun _ hu => ⟨fun i _ s _ => (hu.1 i).1.1 s, fun j _ => (hu.2 j).1⟩

theorem prof_convex (p : S → ℝ) : Convex ℝ (E.prof p) :=
  Convex.prod (fun _ hx _ hy _ _ ha hb hab i => E.dem_convex i p (hx i) (hy i) ha hb hab)
    (fun _ hx _ hy _ _ ha hb hab j =>
      supply_convex (E.Y j) (E.Y_convex j) (retr p) (hx j) (hy j) ha hb hab)

theorem prof_nonempty (p : S → ℝ) : (E.prof p).Nonempty :=
  Set.Nonempty.prod
    ⟨fun i => (E.dem_nonempty i p).some, fun i => (E.dem_nonempty i p).some_mem⟩
    ⟨fun j => (supply_nonempty (E.Y j) (E.Y_compact j) ⟨0, E.Y_zero j⟩ (retr p)).some,
      fun j => (supply_nonempty (E.Y j) (E.Y_compact j) ⟨0, E.Y_zero j⟩ (retr p)).some_mem⟩

theorem N_closed : IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.N pr.1} := by
  apply IsSeqClosed.isClosed
  intro u l hu hl
  have hu' : ∀ n, ∃ c, c ∈ E.prof (u n).1 ∧ E.net c = (u n).2 := fun n => hu n
  choose c hc hcn using hu'
  obtain ⟨cb, _, φ, hφ, hcb⟩ := E.boxP_compact.tendsto_subseq (fun n => E.prof_sub _ (hc n))
  have hcb' : Tendsto (fun n => c (φ n)) atTop (𝓝 cb) := hcb
  have hlφ : Tendsto (fun n => u (φ n)) atTop (𝓝 l) := hl.comp hφ.tendsto_atTop
  have h1 : Tendsto (fun n => (u (φ n)).1) atTop (𝓝 l.1) :=
    (continuous_fst.tendsto l).comp hlφ
  have h2 : Tendsto (fun n => (u (φ n)).2) atTop (𝓝 l.2) :=
    (continuous_snd.tendsto l).comp hlφ
  have hd : ∀ i, cb.1 i ∈ E.dem i l.1 := by
    intro i
    have hci : Tendsto (fun n => (c (φ n)).1 i) atTop (𝓝 (cb.1 i)) :=
      (((continuous_apply i).comp continuous_fst).tendsto cb).comp hcb'
    have hmem : (l.1, cb.1 i) ∈ {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.dem i pr.1} :=
      (E.dem_closed i).mem_of_tendsto (h1.prodMk_nhds hci)
        (Filter.Eventually.of_forall (fun n => (hc (φ n)).1 i))
    exact hmem
  have hs : ∀ j, cb.2 j ∈ supply (E.Y j) (retr l.1) := by
    intro j
    have hc2 : Tendsto (fun n => (c (φ n)).2 j) atTop (𝓝 (cb.2 j)) :=
      (((continuous_apply j).comp continuous_snd).tendsto cb).comp hcb'
    have hr : Tendsto (fun n => retr (u (φ n)).1) atTop (𝓝 (retr l.1)) :=
      (retr_continuous.tendsto l.1).comp h1
    have hmem : (retr l.1, cb.2 j) ∈
        {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ supply (E.Y j) pr.1} :=
      (supply_closedGraph (E.Y j) (E.Y_compact j).isClosed).mem_of_tendsto
        (hr.prodMk_nhds hc2) (Filter.Eventually.of_forall (fun n => (hc (φ n)).2 j))
    exact hmem
  have hn : E.net cb = l.2 := by
    have ha : Tendsto (fun n => E.net (c (φ n))) atTop (𝓝 (E.net cb)) :=
      (E.net_continuous.tendsto cb).comp hcb'
    have hb : (fun n => E.net (c (φ n))) = fun n => (u (φ n)).2 :=
      funext (fun n => hcn (φ n))
    rw [hb] at ha
    exact tendsto_nhds_unique ha h2
  exact ⟨cb, ⟨hd, hs⟩, hn⟩

theorem share_sum (π : J → ℝ) : ∑ i, ∑ j, E.θ i j * π j = ∑ j, π j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => by rw [← Finset.sum_mul, E.θ_sum j, one_mul])

theorem N_walras (p : S → ℝ) (hp : p ∈ priceSimplex S) (n : S → ℝ) (hn : n ∈ E.N p) :
    (∑ s, p s * n s) ≤ 0 := by
  obtain ⟨c, hc, rfl⟩ := hn
  have hr := retr_fix p hp
  show val p (E.net c) ≤ 0
  rw [E.val_net]
  have hy : ∀ j, val p (c.2 j) = profit (E.Y j) p := by
    intro j
    have h := profit_eq (E.Y j) (E.Y_compact j) (retr p) (c.2 j) (hc.2 j)
    rwa [hr] at h
  have hx : ∀ i, val p (c.1 i) ≤ val p (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) p := by
    intro i
    have h : val (retr p) (c.1 i)
        ≤ val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p) := (hc.1 i).1.2
    rwa [hr] at h
  have hsum : ∑ i, val p (c.1 i)
      ≤ ∑ i, (val p (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) p) :=
    Finset.sum_le_sum (fun i _ => hx i)
  rw [Finset.sum_add_distrib, E.share_sum (fun j => profit (E.Y j) p)] at hsum
  rw [Finset.sum_congr rfl (fun j _ => hy j)]
  linarith

/-- Equilibrium with consumption sets `[0, M]^S`. -/
theorem equilibrium_exists :
    ∃ p ∈ priceSimplex S, ∃ x : I → S → ℝ, ∃ y : J → S → ℝ,
      (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) ∧
      (∀ i, x i ∈ budgetW E.M p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetW E.M p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i)) ∧
      ∀ s, ∑ i, x i s ≤ ∑ i, E.ω i s + ∑ j, y j s := by
  obtain ⟨p, hp, n, hn, hle⟩ := SetValuedGND.setValued_gnd (E.net '' E.boxP)
    (E.net_image_convex _ E.boxP_convex) (E.boxP_compact.image E.net_continuous)
    (((E.prof_nonempty 0).mono (E.prof_sub 0)).image _)
    E.N (fun p => Set.image_mono (E.prof_sub p))
    (fun p => E.net_image_convex _ (E.prof_convex p))
    (fun p => (E.prof_nonempty p).image _)
    E.N_closed E.N_walras
  obtain ⟨c, hc, rfl⟩ := hn
  have hr := retr_fix p hp
  have hy : ∀ j, val p (c.2 j) = profit (E.Y j) p := by
    intro j
    have h := profit_eq (E.Y j) (E.Y_compact j) (retr p) (c.2 j) (hc.2 j)
    rwa [hr] at h
  refine ⟨p, hp, c.1, c.2, fun j => ⟨(hc.2 j).1, ?_⟩, ?_, ?_⟩
  · intro y' hy'
    have h : val (retr p) y' ≤ val (retr p) (c.2 j) := (hc.2 j).2 y' hy'
    rwa [hr] at h
  · intro i
    have hw : (val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p))
        = val p (E.ω i) + ∑ j, E.θ i j * val p (c.2 j) := by
      rw [hr]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [hy j])
    have h1 : c.1 i ∈ budgetW E.M (retr p)
        (val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p)) := (hc.1 i).1
    have h2 : ∀ x' ∈ budgetW E.M (retr p)
        (val (retr p) (E.ω i) + ∑ j, E.θ i j * profit (E.Y j) (retr p)),
        E.U i x' ≤ E.U i (c.1 i) := (hc.1 i).2
    rw [hw, hr] at h1 h2
    exact ⟨h1, h2⟩
  · intro s
    have h := hle s
    rw [E.net_apply] at h
    linarith

/-- If the consumption bound exceeds everything attainable, it does not bind: the bundles
are optimal in the unbounded budget sets. -/
theorem equilibrium_unbounded
    (hM : ∀ y : J → S → ℝ, (∀ j, y j ∈ E.Y j) →
      ∀ s, ∑ i, E.ω i s + ∑ j, y j s + 1 ≤ E.M)
    (hss : ∀ (i : I) (x x' : S → ℝ), E.U i x < E.U i x' → ∀ t : ℝ, 0 < t → t < 1 →
      E.U i x < E.U i ((1 - t) • x + t • x')) :
    ∃ p ∈ priceSimplex S, ∃ x : I → S → ℝ, ∃ y : J → S → ℝ,
      (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) ∧
      (∀ i, x i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i)) ∧
      ∀ s, ∑ i, x i s ≤ ∑ i, E.ω i s + ∑ j, y j s := by
  obtain ⟨p, hp, x, y, hy, hx, hf⟩ := E.equilibrium_exists
  refine ⟨p, hp, x, y, hy,
    fun i => ⟨⟨fun s => ((hx i).1.1 s).1, (hx i).1.2⟩, ?_⟩, hf⟩
  intro x' hx'
  by_contra hcon
  have hlt : E.U i (x i) < E.U i x' := lt_of_not_ge hcon
  have hxM : ∀ s, x i s + 1 ≤ E.M := by
    intro s
    have h1 : x i s ≤ ∑ k, x k s :=
      Finset.single_le_sum (f := fun k => x k s) (fun k _ => ((hx k).1.1 s).1)
        (Finset.mem_univ i)
    have h2 := hf s
    have h3 := hM y (fun j => (hy j).1) s
    linarith
  obtain ⟨t, ht0, ht1, htM⟩ := small_step E.M (x i) x' hxM
  have hz : (1 - t) • x i + t • x'
      ∈ budgetW E.M p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) := by
    refine ⟨fun s => ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg (by linarith) ((hx i).1.1 s).1)
        (mul_nonneg ht0.le (hx'.1 s))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact htM s
    · rw [val_lin]
      have h1 := mul_le_mul_of_nonneg_left (hx i).1.2 (by linarith : (0:ℝ) ≤ 1 - t)
      have h2 := mul_le_mul_of_nonneg_left hx'.2 ht0.le
      linarith
  exact absurd ((hx i).2 _ hz) (not_le.2 (hss i (x i) x' hlt t ht0 ht1))

/-- A consumption bound larger than everything attainable exists. -/
theorem exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : J → S → ℝ, (∀ j, y j ∈ E.Y j) →
    ∀ s, ∑ i, E.ω i s + ∑ j, y j s + 1 ≤ M := by
  have hB : ∀ j, ∃ R : ℝ, ∀ y ∈ E.Y j, ‖y‖ ≤ R :=
    fun j => (E.Y_compact j).isBounded.exists_norm_le
  choose R hR using hB
  have hR0 : ∀ j, 0 ≤ R j := fun j => by
    have h := hR j 0 (E.Y_zero j)
    rwa [norm_zero] at h
  refine ⟨∑ i, ∑ s, E.ω i s + ∑ j, R j + 1, ?_, fun y hy s => ?_⟩
  · have h1 : 0 ≤ ∑ i, ∑ s, E.ω i s :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun s _ => (E.ω_pos i s).le))
    have h2 : 0 ≤ ∑ j, R j := Finset.sum_nonneg (fun j _ => hR0 j)
    linarith
  · have h1 : ∑ i, E.ω i s ≤ ∑ i, ∑ s, E.ω i s :=
      Finset.sum_le_sum (fun i _ =>
        Finset.single_le_sum (f := fun s => E.ω i s) (fun s _ => (E.ω_pos i s).le)
          (Finset.mem_univ s))
    have h2 : ∑ j, y j s ≤ ∑ j, R j :=
      Finset.sum_le_sum (fun j _ => by
        have a := norm_le_pi_norm (y j) s
        have b := hR j (y j) (hy j)
        have c := le_abs_self (y j s)
        rw [Real.norm_eq_abs] at a
        linarith)
    linarith

/-- **Competitive equilibrium of a private-ownership economy.** Unbounded consumption sets,
several firms, and zero price for every good in excess supply. -/
theorem competitive_equilibrium
    (hss : ∀ (i : I) (x x' : S → ℝ), E.U i x < E.U i x' → ∀ t : ℝ, 0 < t → t < 1 →
      E.U i x < E.U i ((1 - t) • x + t • x'))
    (hns : ∀ (i : I) (x : S → ℝ), (∀ s, 0 ≤ x s) →
      ∃ x' : S → ℝ, (∀ s, 0 ≤ x' s) ∧ E.U i x < E.U i x') :
    ∃ p ∈ priceSimplex S, ∃ x : I → S → ℝ, ∃ y : J → S → ℝ,
      (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) ∧
      (∀ i, x i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i)) ∧
      (∀ s, ∑ i, x i s ≤ ∑ i, E.ω i s + ∑ j, y j s) ∧
      ∀ s, p s * (∑ i, E.ω i s + ∑ j, y j s - ∑ i, x i s) = 0 := by
  obtain ⟨M', hM'0, hM'⟩ := E.exists_bound
  obtain ⟨p, hp, x, y, hy, hx, hf⟩ :=
    Economy.equilibrium_unbounded { E with M := M', M_nonneg := hM'0 } hM' hss
  refine ⟨p, hp, x, y, hy, hx, hf, ?_⟩
  have hb : ∀ i, val p (x i) = val p (E.ω i) + ∑ j, E.θ i j * val p (y j) :=
    fun i => budget_binds (E.U i) (hss i) (hns i) p _ (x i) (hx i).1 (hx i).2
  have e1 : ∑ s, p s * ∑ i, E.ω i s = ∑ i, val p (E.ω i) := by
    simp only [val, Finset.mul_sum]
    exact Finset.sum_comm
  have e2 : ∑ s, p s * ∑ j, y j s = ∑ j, val p (y j) := by
    simp only [val, Finset.mul_sum]
    exact Finset.sum_comm
  have e3 : ∑ s, p s * ∑ i, x i s = ∑ i, val p (x i) := by
    simp only [val, Finset.mul_sum]
    exact Finset.sum_comm
  have hsum : ∑ i, val p (x i) = ∑ i, val p (E.ω i) + ∑ j, val p (y j) := by
    rw [Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_add_distrib,
      E.share_sum (fun j => val p (y j))]
  have hsplit : ∑ s, p s * (∑ i, E.ω i s + ∑ j, y j s - ∑ i, x i s)
      = ∑ s, p s * ∑ i, E.ω i s + ∑ s, p s * ∑ j, y j s - ∑ s, p s * ∑ i, x i s := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have htot : ∑ s, p s * (∑ i, E.ω i s + ∑ j, y j s - ∑ i, x i s) = 0 := by
    rw [hsplit, e1, e2, e3, hsum]
    ring
  have hnn : ∀ s ∈ Finset.univ, 0 ≤ p s * (∑ i, E.ω i s + ∑ j, y j s - ∑ i, x i s) :=
    fun s _ => mul_nonneg (hp.1 s) (by linarith [hf s])
  intro s
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 htot s (Finset.mem_univ s)

/-- Value of an aggregate equals the sum of values. -/
theorem val_sum {K : Type*} [Fintype K] (p : S → ℝ) (f : K → S → ℝ) :
    ∑ s, p s * ∑ k, f k s = ∑ k, val p (f k) := by
  simp only [val, Finset.mul_sum]
  exact Finset.sum_comm

/-- **First welfare theorem.** At a competitive equilibrium no feasible allocation makes
every household at least as well off and some household strictly better off. -/
theorem first_welfare
    (hss : ∀ (i : I) (x x' : S → ℝ), E.U i x < E.U i x' → ∀ t : ℝ, 0 < t → t < 1 →
      E.U i x < E.U i ((1 - t) • x + t • x'))
    (hns : ∀ (i : I) (x : S → ℝ), (∀ s, 0 ≤ x s) →
      ∃ x' : S → ℝ, (∀ s, 0 ≤ x' s) ∧ E.U i x < E.U i x')
    (p : S → ℝ) (hp : p ∈ priceSimplex S) (x : I → S → ℝ) (y : J → S → ℝ)
    (hy : ∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j))
    (hx : ∀ i, x i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i))
    (x' : I → S → ℝ) (y' : J → S → ℝ) (hy' : ∀ j, y' j ∈ E.Y j)
    (hx'0 : ∀ i s, 0 ≤ x' i s)
    (hfeas : ∀ s, ∑ i, x' i s ≤ ∑ i, E.ω i s + ∑ j, y' j s)
    (hweak : ∀ i, E.U i (x i) ≤ E.U i (x' i)) :
    ∀ i, ¬ E.U i (x i) < E.U i (x' i) := by
  intro k hk
  have hge : ∀ i, val p (E.ω i) + ∑ j, E.θ i j * val p (y j) ≤ val p (x' i) := by
    intro i
    by_contra h
    have hlt := lt_of_not_ge h
    have hmem : x' i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) :=
      ⟨hx'0 i, hlt.le⟩
    have heq : E.U i (x' i) = E.U i (x i) := le_antisymm ((hx i).2 _ hmem) (hweak i)
    have hb := budget_binds (E.U i) (hss i) (hns i) p _ (x' i) hmem
      (fun z hz => by rw [heq]; exact (hx i).2 z hz)
    linarith
  have hgt : val p (E.ω k) + ∑ j, E.θ k j * val p (y j) < val p (x' k) := by
    by_contra h
    have hmem : x' k ∈ budgetU p (val p (E.ω k) + ∑ j, E.θ k j * val p (y j)) :=
      ⟨hx'0 k, le_of_not_gt h⟩
    exact absurd ((hx k).2 _ hmem) (not_le.2 hk)
  have h1 : ∑ i, (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) < ∑ i, val p (x' i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  rw [Finset.sum_add_distrib, E.share_sum (fun j => val p (y j))] at h1
  have h2 : ∑ j, val p (y' j) ≤ ∑ j, val p (y j) :=
    Finset.sum_le_sum (fun j _ => (hy j).2 _ (hy' j))
  have h3 : ∑ s, p s * ∑ i, x' i s ≤ ∑ s, p s * (∑ i, E.ω i s + ∑ j, y' j s) :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfeas s) (hp.1 s))
  have hs : ∑ s, p s * (∑ i, E.ω i s + ∑ j, y' j s)
      = ∑ s, p s * ∑ i, E.ω i s + ∑ s, p s * ∑ j, y' j s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [hs, val_sum, val_sum, val_sum] at h3
  linarith

/-- **Existence of a Pareto-efficient competitive equilibrium.** -/
theorem efficient_equilibrium
    (hss : ∀ (i : I) (x x' : S → ℝ), E.U i x < E.U i x' → ∀ t : ℝ, 0 < t → t < 1 →
      E.U i x < E.U i ((1 - t) • x + t • x'))
    (hns : ∀ (i : I) (x : S → ℝ), (∀ s, 0 ≤ x s) →
      ∃ x' : S → ℝ, (∀ s, 0 ≤ x' s) ∧ E.U i x < E.U i x') :
    ∃ p ∈ priceSimplex S, ∃ x : I → S → ℝ, ∃ y : J → S → ℝ,
      (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) ∧
      (∀ i, x i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i)) ∧
      (∀ s, ∑ i, x i s ≤ ∑ i, E.ω i s + ∑ j, y j s) ∧
      ∀ (x' : I → S → ℝ) (y' : J → S → ℝ), (∀ j, y' j ∈ E.Y j) → (∀ i s, 0 ≤ x' i s) →
        (∀ s, ∑ i, x' i s ≤ ∑ i, E.ω i s + ∑ j, y' j s) →
        (∀ i, E.U i (x i) ≤ E.U i (x' i)) → ∀ i, ¬ E.U i (x i) < E.U i (x' i) := by
  obtain ⟨p, hp, x, y, hy, hx, hf, _⟩ := E.competitive_equilibrium hss hns
  exact ⟨p, hp, x, y, hy, hx, hf, fun x' y' hy' hx'0 hfeas hweak =>
    E.first_welfare hss hns p hp x y hy hx x' y' hy' hx'0 hfeas hweak⟩

/-- Dividends exhaust profit: all firm income is paid to owners, none to fixed claims. -/
theorem dividends_exhaust_profit (p : S → ℝ) (y : J → S → ℝ) :
    ∑ i, ∑ j, E.θ i j * val p (y j) = ∑ j, val p (y j) :=
  E.share_sum (fun j => val p (y j))

/-- At profit-maximising plans no owner receives a negative dividend from any firm. -/
theorem dividend_nonneg (p : S → ℝ) (y : J → S → ℝ)
    (hy : ∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) (i : I) (j : J) :
    0 ≤ E.θ i j * val p (y j) := by
  have h := (hy j).2 0 (E.Y_zero j)
  have h0 : val p (0 : S → ℝ) = 0 := by simp [val]
  rw [h0] at h
  exact mul_nonneg (E.θ_nonneg i j) h

/-- **Exact market clearing.** With strictly monotone utilities every price is strictly
positive and supply equals demand in every market. -/
theorem exact_equilibrium [Nonempty I]
    (hss : ∀ (i : I) (x x' : S → ℝ), E.U i x < E.U i x' → ∀ t : ℝ, 0 < t → t < 1 →
      E.U i x < E.U i ((1 - t) • x + t • x'))
    (hmono : ∀ (i : I) (x x' : S → ℝ), (∀ s, x s ≤ x' s) → x ≠ x' → E.U i x < E.U i x') :
    ∃ p ∈ priceSimplex S, (∀ s, 0 < p s) ∧ ∃ x : I → S → ℝ, ∃ y : J → S → ℝ,
      (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, val p y' ≤ val p (y j)) ∧
      (∀ i, x i ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) ∧
        ∀ x' ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)),
          E.U i x' ≤ E.U i (x i)) ∧
      ∀ s, ∑ i, x i s = ∑ i, E.ω i s + ∑ j, y j s := by
  classical
  have hns : ∀ (i : I) (x : S → ℝ), (∀ s, 0 ≤ x s) →
      ∃ x' : S → ℝ, (∀ s, 0 ≤ x' s) ∧ E.U i x < E.U i x' := by
    intro i x hx0
    refine ⟨fun s => x s + 1, fun s => by linarith [hx0 s], ?_⟩
    apply hmono i x _ (fun s => by linarith)
    intro hEq
    have := congrFun hEq (Classical.arbitrary S)
    simp at this
  obtain ⟨p, hp, x, y, hy, hx, hf, hz⟩ := E.competitive_equilibrium hss hns
  have hpos : ∀ s, 0 < p s := by
    intro s
    by_contra hc
    have hps : p s = 0 := le_antisymm (not_lt.1 hc) (hp.1 s)
    let i : I := Classical.arbitrary I
    have hv : val p (fun r => x i r + (if r = s then (1 : ℝ) else 0)) = val p (x i) := by
      simp only [val, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, hps, add_zero]
    have hmem : (fun r => x i r + (if r = s then (1 : ℝ) else 0))
        ∈ budgetU p (val p (E.ω i) + ∑ j, E.θ i j * val p (y j)) := by
      refine ⟨fun r => ?_, ?_⟩
      · have := (hx i).1.1 r
        beta_reduce
        split_ifs <;> linarith
      · rw [hv]; exact (hx i).1.2
    have hle := (hx i).2 _ hmem
    have hlt : E.U i (x i) < E.U i (fun r => x i r + (if r = s then (1 : ℝ) else 0)) := by
      apply hmono i (x i) _ (fun r => by split_ifs <;> linarith)
      intro hEq
      have := congrFun hEq s
      simp at this
    linarith
  refine ⟨p, hp, hpos, x, y, hy, hx, fun s => ?_⟩
  have h := hz s
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd h0 (hpos s).ne'
  · linarith

end Economy

end ArrowDebreu

end

#print axioms ArrowDebreu.Economy.exact_equilibrium
