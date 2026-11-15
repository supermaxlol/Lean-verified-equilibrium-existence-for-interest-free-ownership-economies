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
Stage 254: production equilibrium with convex-valued demand and supply.

Wires the set-valued Gale–Nikaido–Debreu engine above into a production economy whose
consumer excess demand `Z` and net supply `Y` are correspondences (convex-valued, closed
graph, values in compact convex sets) linked by the production Walras law.  No strict
concavity is needed on either side.
-/

open scoped Pointwise
open Filter Topology

/-- A production economy with set-valued consumer excess demand and net supply. -/
structure CorrProductionEconomy (S : Type*) [Fintype S] where
  Z : (S → ℝ) → Set (S → ℝ)
  Y : (S → ℝ) → Set (S → ℝ)
  KZ : Set (S → ℝ)
  KY : Set (S → ℝ)
  KZ_convex : Convex ℝ KZ
  KY_convex : Convex ℝ KY
  KZ_compact : IsCompact KZ
  KY_compact : IsCompact KY
  Z_sub : ∀ p, Z p ⊆ KZ
  Y_sub : ∀ p, Y p ⊆ KY
  Z_convex : ∀ p, Convex ℝ (Z p)
  Y_convex : ∀ p, Convex ℝ (Y p)
  Z_nonempty : ∀ p, (Z p).Nonempty
  Y_nonempty : ∀ p, (Y p).Nonempty
  Z_closed : IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ Z pr.1}
  Y_closed : IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ Y pr.1}
  walras : ∀ p ∈ priceSimplex S, ∀ x ∈ Z p, ∀ y ∈ Y p,
    (∑ s, p s * x s) ≤ (∑ s, p s * y s)

namespace CorrProductionEconomy

variable {S : Type*} [Fintype S]

/-- The net excess-demand correspondence `Z p - Y p` has closed graph. -/
theorem net_closed (E : CorrProductionEconomy S) :
    IsClosed {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.Z pr.1 - E.Y pr.1} := by
  apply IsSeqClosed.isClosed
  intro u l hu hl
  have hu' : ∀ n, ∃ x ∈ E.Z (u n).1, ∃ y ∈ E.Y (u n).1, x - y = (u n).2 :=
    fun n => Set.mem_sub.1 (hu n)
  choose x hx y hy hxy using hu'
  obtain ⟨a, _, φ, hφ, hxa⟩ := E.KZ_compact.tendsto_subseq (fun n => E.Z_sub _ (hx n))
  have hxa' : Tendsto (fun n => x (φ n)) atTop (𝓝 a) := hxa
  have hlφ : Tendsto (fun n => u (φ n)) atTop (𝓝 l) := hl.comp hφ.tendsto_atTop
  have h1 : Tendsto (fun n => (u (φ n)).1) atTop (𝓝 l.1) :=
    (continuous_fst.tendsto l).comp hlφ
  have h2 : Tendsto (fun n => (u (φ n)).2) atTop (𝓝 l.2) :=
    (continuous_snd.tendsto l).comp hlφ
  have hy' : Tendsto (fun n => y (φ n)) atTop (𝓝 (a - l.2)) := by
    have he : (fun n => y (φ n)) = fun n => x (φ n) - (u (φ n)).2 := by
      funext n
      rw [← hxy (φ n), sub_sub_cancel]
    rw [he]
    exact hxa'.sub h2
  have hZ : a ∈ E.Z l.1 := by
    have hmem : (l.1, a) ∈ {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.Z pr.1} :=
      E.Z_closed.mem_of_tendsto (h1.prodMk_nhds hxa')
        (Filter.Eventually.of_forall (fun n => hx (φ n)))
    exact hmem
  have hY : a - l.2 ∈ E.Y l.1 := by
    have hmem : (l.1, a - l.2) ∈ {pr : (S → ℝ) × (S → ℝ) | pr.2 ∈ E.Y pr.1} :=
      E.Y_closed.mem_of_tendsto (h1.prodMk_nhds hy')
        (Filter.Eventually.of_forall (fun n => hy (φ n)))
    exact hmem
  exact Set.mem_sub.2 ⟨a, hZ, a - l.2, hY, sub_sub_cancel a l.2⟩

/-- **Production equilibrium with convex-valued demand and supply.** Some simplex price
`p`, demand selection `x ∈ Z p` and supply selection `y ∈ Y p` satisfy `x ≤ y` in every
good. -/
theorem equilibrium_exists [Nonempty S] (E : CorrProductionEconomy S) :
    ∃ p ∈ priceSimplex S, ∃ x ∈ E.Z p, ∃ y ∈ E.Y p, ∀ s, x s ≤ y s := by
  obtain ⟨p, hp, n, hn, hle⟩ := SetValuedGND.setValued_gnd (E.KZ - E.KY)
    (E.KZ_convex.sub E.KY_convex) (by
      have h : E.KZ - E.KY = (fun pr : (S → ℝ) × (S → ℝ) => pr.1 - pr.2) '' (E.KZ ×ˢ E.KY) := by
        ext n
        constructor
        · intro hn
          obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.1 hn
          exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
          exact Set.mem_sub.2 ⟨a, ha, b, hb, rfl⟩
      rw [h]
      exact (E.KZ_compact.prod E.KY_compact).image continuous_sub)
    (((E.Z_nonempty 0).mono (E.Z_sub 0)).sub ((E.Y_nonempty 0).mono (E.Y_sub 0)))
    (fun p => E.Z p - E.Y p) (fun p => Set.sub_subset_sub (E.Z_sub p) (E.Y_sub p))
    (fun p => (E.Z_convex p).sub (E.Y_convex p))
    (fun p => (E.Z_nonempty p).sub (E.Y_nonempty p))
    E.net_closed
    (fun p hp n hn => by
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.1 hn
      have hw := E.walras p hp x hx y hy
      have h : ∑ s, p s * (x - y) s = (∑ s, p s * x s) - ∑ s, p s * y s := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by rw [Pi.sub_apply]; ring)
      rw [h]
      linarith)
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.1 hn
  refine ⟨p, hp, x, hx, y, hy, fun s => ?_⟩
  have := hle s
  rw [Pi.sub_apply] at this
  linarith

end CorrProductionEconomy

#print axioms SetValuedGND.setValued_gnd
#print axioms CorrProductionEconomy.net_closed
#print axioms CorrProductionEconomy.equilibrium_exists
