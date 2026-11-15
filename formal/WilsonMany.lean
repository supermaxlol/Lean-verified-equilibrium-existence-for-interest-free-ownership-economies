import Mathlib

/-!
Stage 294: Wilson for n households — linear sharing forces one common cautiousness for all, and aggregate tolerance is the sum.

Two households with marginal utilities `gi`, `gj` (derivatives `hi`, `hj`) share output `Y`
by affine rules `ci Y = bi * Y + ki`, `cj Y = bj * Y + kj` that satisfy the first-order
conditions of an efficient allocation, `λi * gi (ci Y) = μ Y = λj * gj (cj Y)`, for all `Y`
in an open set `U`.  Risk tolerance `T` is defined by `T x * g' x = - g x`.

* `foc_deriv` — differentiating the first-order condition;
* `tolerance_share` — `Ti (ci Y) * μ' Y = - bi * μ Y`: each household's risk tolerance at its
  consumption is its slope times the aggregate tolerance (Wilson's identity, affine case);
* `wilson_converse` — the derivatives of risk tolerance (cautiousness) agree along the rule:
  `Ti' (ci Y) = Tj' (cj Y)` for all `Y ∈ U`;
* `wilson_hara` — in particular, for HARA households (`T x = α + ρ x`) linear sharing is
  efficient only if `ρi = ρj`: a common slope.
-/

noncomputable section

open Filter Topology

namespace WilsonMany

/-- Differentiating the first-order condition along an affine rule. -/
theorem foc_deriv (g h μ μd : ℝ → ℝ) (lam b k : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hg : ∀ Y ∈ U, HasDerivAt g (h (b * Y + k)) (b * Y + k))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hfoc : ∀ Y ∈ U, lam * g (b * Y + k) = μ Y) :
    ∀ Y ∈ U, lam * (h (b * Y + k) * (b * 1)) = μd Y := by
  intro Y hY
  have h1 := ((hg Y hY).comp Y (((hasDerivAt_id' Y).const_mul b).add_const k)).const_mul lam
  have h2 : HasDerivAt μ (lam * (h (b * Y + k) * (b * 1))) Y :=
    h1.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hY)
      (fun y hy => (hfoc y hy).symm))
  exact ((hμ Y hY).unique h2).symm

/-- **Wilson's identity along an affine rule.** -/
theorem tolerance_share (g h T μ μd : ℝ → ℝ) (lam b k : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hg : ∀ Y ∈ U, HasDerivAt g (h (b * Y + k)) (b * Y + k))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hfoc : ∀ Y ∈ U, lam * g (b * Y + k) = μ Y)
    (hT : ∀ x, T x * h x = - g x) :
    ∀ Y ∈ U, T (b * Y + k) * μd Y = - b * μ Y := by
  intro Y hY
  rw [← foc_deriv g h μ μd lam b k U hU hg hμ hfoc Y hY, ← hfoc Y hY]
  have := hT (b * Y + k)
  linear_combination lam * b * this

/-- **Wilson's converse.**  If two households share by affine rules satisfying the
efficiency conditions, their cautiousness (derivative of risk tolerance) agrees along the
rules. -/
theorem wilson_converse (gi hi Ti Ti' gj hj Tj Tj' μ μd : ℝ → ℝ)
    (lami lamj bi ki bj kj : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hlami : lami ≠ 0) (hbi : bi ≠ 0) (hbj : bj ≠ 0) (hhi : ∀ x, hi x ≠ 0)
    (hgi : ∀ Y ∈ U, HasDerivAt gi (hi (bi * Y + ki)) (bi * Y + ki))
    (hgj : ∀ Y ∈ U, HasDerivAt gj (hj (bj * Y + kj)) (bj * Y + kj))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hfi : ∀ Y ∈ U, lami * gi (bi * Y + ki) = μ Y)
    (hfj : ∀ Y ∈ U, lamj * gj (bj * Y + kj) = μ Y)
    (hTi : ∀ x, Ti x * hi x = - gi x) (hTj : ∀ x, Tj x * hj x = - gj x)
    (hTi' : ∀ x, HasDerivAt Ti (Ti' x) x) (hTj' : ∀ x, HasDerivAt Tj (Tj' x) x) :
    ∀ Y ∈ U, Ti' (bi * Y + ki) = Tj' (bj * Y + kj) := by
  have hd := foc_deriv gi hi μ μd lami bi ki U hU hgi hμ hfi
  have hne : ∀ Y ∈ U, μd Y ≠ 0 := by
    intro Y hY
    rw [← hd Y hY, mul_one]
    exact mul_ne_zero hlami (mul_ne_zero (hhi _) hbi)
  have si := tolerance_share gi hi Ti μ μd lami bi ki U hU hgi hμ hfi hTi
  have sj := tolerance_share gj hj Tj μ μd lamj bj kj U hU hgj hμ hfj hTj
  have heq : ∀ y ∈ U, bj * Ti (bi * y + ki) = bi * Tj (bj * y + kj) := by
    intro y hy
    have h1 := si y hy
    have h2 := sj y hy
    have h3 : (bj * Ti (bi * y + ki) - bi * Tj (bj * y + kj)) * μd y = 0 := by
      linear_combination bj * h1 - bi * h2
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h (hne y hy)
  intro Y hY
  have d1 := ((hTi' (bi * Y + ki)).comp Y
    (((hasDerivAt_id' Y).const_mul bi).add_const ki)).const_mul bj
  have d2 := ((hTj' (bj * Y + kj)).comp Y
    (((hasDerivAt_id' Y).const_mul bj).add_const kj)).const_mul bi
  have d1' : HasDerivAt (fun y => bi * Tj (bj * y + kj))
      (bj * (Ti' (bi * Y + ki) * (bi * 1))) Y :=
    d1.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hY)
      (fun y hy => (heq y hy).symm))
  have h4 := d1'.unique d2
  have h5 : (bi * bj) * (Ti' (bi * Y + ki) - Tj' (bj * Y + kj)) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.1 h5 with h | h
  · exact absurd h (mul_ne_zero hbi hbj)
  · linarith

/-- **HARA case: linear sharing needs a common slope.** -/
theorem wilson_hara (gi hi Ti gj hj Tj μ μd : ℝ → ℝ)
    (lami lamj bi ki bj kj ρi ρj : ℝ) (U : Set ℝ) (hU : IsOpen U) (hUne : U.Nonempty)
    (hlami : lami ≠ 0) (hbi : bi ≠ 0) (hbj : bj ≠ 0) (hhi : ∀ x, hi x ≠ 0)
    (hgi : ∀ Y ∈ U, HasDerivAt gi (hi (bi * Y + ki)) (bi * Y + ki))
    (hgj : ∀ Y ∈ U, HasDerivAt gj (hj (bj * Y + kj)) (bj * Y + kj))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hfi : ∀ Y ∈ U, lami * gi (bi * Y + ki) = μ Y)
    (hfj : ∀ Y ∈ U, lamj * gj (bj * Y + kj) = μ Y)
    (hTi : ∀ x, Ti x * hi x = - gi x) (hTj : ∀ x, Tj x * hj x = - gj x)
    (hTi' : ∀ x, HasDerivAt Ti ρi x) (hTj' : ∀ x, HasDerivAt Tj ρj x) :
    ρi = ρj := by
  obtain ⟨Y, hY⟩ := hUne
  exact wilson_converse gi hi Ti (fun _ => ρi) gj hj Tj (fun _ => ρj) μ μd lami lamj bi ki bj kj
    U hU hlami hbi hbj hhi hgi hgj hμ hfi hfj hTi hTj hTi' hTj' Y hY

/-- **Wilson's converse for any number of households.** -/
theorem wilson_converse_all {I : Type*} (g h T T' : I → ℝ → ℝ) (μ μd : ℝ → ℝ)
    (lam b k : I → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hlam : ∀ i, lam i ≠ 0) (hb : ∀ i, b i ≠ 0) (hh : ∀ i x, h i x ≠ 0)
    (hg : ∀ i, ∀ Y ∈ U, HasDerivAt (g i) (h i (b i * Y + k i)) (b i * Y + k i))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hf : ∀ i, ∀ Y ∈ U, lam i * g i (b i * Y + k i) = μ Y)
    (hT : ∀ i x, T i x * h i x = - g i x) (hT' : ∀ i x, HasDerivAt (T i) (T' i x) x) :
    ∀ i j, ∀ Y ∈ U, T' i (b i * Y + k i) = T' j (b j * Y + k j) := fun i j =>
  wilson_converse (g i) (h i) (T i) (T' i) (g j) (h j) (T j) (T' j) μ μd (lam i) (lam j)
    (b i) (k i) (b j) (k j) U hU (hlam i) (hb i) (hb j) (hh i) (hg i) (hg j) hμ (hf i) (hf j)
    (hT i) (hT j) (hT' i) (hT' j)

/-- One common cautiousness function for all households. -/
theorem common_cautiousness {I : Type*} (i0 : I) (g h T T' : I → ℝ → ℝ) (μ μd : ℝ → ℝ)
    (lam b k : I → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hlam : ∀ i, lam i ≠ 0) (hb : ∀ i, b i ≠ 0) (hh : ∀ i x, h i x ≠ 0)
    (hg : ∀ i, ∀ Y ∈ U, HasDerivAt (g i) (h i (b i * Y + k i)) (b i * Y + k i))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hf : ∀ i, ∀ Y ∈ U, lam i * g i (b i * Y + k i) = μ Y)
    (hT : ∀ i x, T i x * h i x = - g i x) (hT' : ∀ i x, HasDerivAt (T i) (T' i x) x) :
    ∃ C : ℝ → ℝ, ∀ i, ∀ Y ∈ U, T' i (b i * Y + k i) = C Y :=
  ⟨fun Y => T' i0 (b i0 * Y + k i0), fun i Y hY =>
    wilson_converse_all g h T T' μ μd lam b k U hU hlam hb hh hg hμ hf hT hT' i i0 Y hY⟩

/-- **HARA households: all slopes equal.** -/
theorem wilson_hara_all {I : Type*} (g h T : I → ℝ → ℝ) (ρ : I → ℝ) (μ μd : ℝ → ℝ)
    (lam b k : I → ℝ) (U : Set ℝ) (hU : IsOpen U) (hUne : U.Nonempty)
    (hlam : ∀ i, lam i ≠ 0) (hb : ∀ i, b i ≠ 0) (hh : ∀ i x, h i x ≠ 0)
    (hg : ∀ i, ∀ Y ∈ U, HasDerivAt (g i) (h i (b i * Y + k i)) (b i * Y + k i))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hf : ∀ i, ∀ Y ∈ U, lam i * g i (b i * Y + k i) = μ Y)
    (hT : ∀ i x, T i x * h i x = - g i x) (hT' : ∀ i x, HasDerivAt (T i) (ρ i) x) :
    ∀ i j, ρ i = ρ j := by
  intro i j
  obtain ⟨Y, hY⟩ := hUne
  exact wilson_converse_all g h T (fun i _ => ρ i) μ μd lam b k U hU hlam hb hh hg hμ hf hT
    hT' i j Y hY

/-- **Risk tolerances add up.**  With slopes summing to one, the households' risk tolerances
sum to the aggregate risk tolerance `-μ/μ'`. -/
theorem tolerance_sum {I : Type*} [Fintype I] (g h T : I → ℝ → ℝ) (μ μd : ℝ → ℝ)
    (lam b k : I → ℝ) (U : Set ℝ) (hU : IsOpen U) (hsum : ∑ i, b i = 1)
    (hg : ∀ i, ∀ Y ∈ U, HasDerivAt (g i) (h i (b i * Y + k i)) (b i * Y + k i))
    (hμ : ∀ Y ∈ U, HasDerivAt μ (μd Y) Y)
    (hf : ∀ i, ∀ Y ∈ U, lam i * g i (b i * Y + k i) = μ Y)
    (hT : ∀ i x, T i x * h i x = - g i x) :
    ∀ Y ∈ U, (∑ i, T i (b i * Y + k i)) * μd Y = - μ Y := by
  intro Y hY
  rw [Finset.sum_mul, Finset.sum_congr rfl (fun i _ =>
    tolerance_share (g i) (h i) (T i) μ μd (lam i) (b i) (k i) U hU (hg i) hμ (hf i) (hT i) Y hY),
    ← Finset.sum_mul, Finset.sum_neg_distrib, hsum]
  ring

end WilsonMany

end

#print axioms WilsonMany.wilson_converse_all
#print axioms WilsonMany.common_cautiousness
#print axioms WilsonMany.wilson_hara_all
#print axioms WilsonMany.tolerance_sum
