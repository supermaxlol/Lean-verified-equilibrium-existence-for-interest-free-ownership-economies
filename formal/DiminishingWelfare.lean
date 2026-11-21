import Mathlib

/-!
# Stage 362: diminishing marginal utility — why the distribution of ownership matters

Stage 250 shows that consumption shares equal ownership (wealth) shares, so with total
consumption `C` household `h` consumes `x h * C`. Let every household have the same felicity
`u`, strictly concave on `[0, ∞)`: marginal utility diminishes. Utilitarian welfare is
`welfare u C x = ∑ h, u (x h * C)`.

* `pigou_dalton`: moving `t` from a richer household (`b`) to a poorer one (`a`) without
  reversing their order (`0 < t < b − a`) strictly raises `u a + u b`. Same output, more welfare.
* `equal_maximises`: for any shares summing to one, `welfare ≤ N u (C / N)`: equal ownership
  gives the most welfare from a given output (Jensen).
* `concentrated_worse`: with `N ≥ 2` and `C > 0`, the fully concentrated outcome
  `u C + (N − 1) u 0` is strictly below the equal outcome `N u (C / N)`.
* `concentration_limit`: if one household's share tends to one and every other share tends to
  zero (stage 356, pro rata issuance under different patience), welfare tends to
  `u C + (N − 1) u 0`, hence eventually stays strictly below equal welfare.
* `floor_welfare`: if `u` is monotone and every share is at least `f` (stage 356, equal
  issuance), welfare is at least `N u (f C)`.

Reading: with diminishing marginal utility the same economy yields more total satisfaction the
more evenly ownership is spread. Pro rata issuance drives welfare toward its concentrated value;
an equal-issuance floor keeps it above an explicit bound. Output is held fixed throughout, so
this is a statement about distribution, not about growth.
-/

noncomputable section

open Finset BigOperators Filter Topology Set

namespace DiminishingWelfare

variable {H : Type*} [Fintype H]

def welfare (u : ℝ → ℝ) (C : ℝ) (x : H → ℝ) : ℝ := ∑ h, u (x h * C)

/-- **Pigou–Dalton.** A transfer from richer to poorer that keeps the order strictly raises
the sum of utilities when marginal utility diminishes. -/
theorem pigou_dalton (u : ℝ → ℝ) (hu : StrictConcaveOn ℝ (Ici 0) u) (a b t : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (ht : 0 < t) (htb : t < b - a) :
    u a + u b < u (a + t) + u (b - t) := by
  have hd : 0 < b - a := by linarith
  set l := t / (b - a) with hl
  have hl0 : 0 < l := div_pos ht hd
  have hl1 : l < 1 := (div_lt_one hd).2 htb
  have hai : a ∈ Ici (0:ℝ) := ha
  have hbi : b ∈ Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
  have e1 : (1 - l) • a + l • b = a + t := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  have e2 : l • a + (1 - l) • b = b - t := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  have i1 := hu.2 hai hbi hab.ne (show (0:ℝ) < 1 - l by linarith) hl0 (by ring)
  have i2 := hu.2 hai hbi hab.ne hl0 (show (0:ℝ) < 1 - l by linarith) (by ring)
  rw [e1] at i1
  rw [e2] at i2
  simp only [smul_eq_mul] at i1 i2
  linarith

/-- **Equal ownership maximises welfare** for a given output (Jensen). -/
theorem equal_maximises [Nonempty H] (u : ℝ → ℝ) (hu : ConcaveOn ℝ (Ici 0) u) (C : ℝ)
    (hC : 0 ≤ C) (x : H → ℝ) (hx : ∀ h, 0 ≤ x h) (hs : ∑ h, x h = 1) :
    welfare u C x ≤ (Fintype.card H : ℝ) * u (C / Fintype.card H) := by
  have hN : (0:ℝ) < Fintype.card H := Nat.cast_pos.2 Fintype.card_pos
  have hj := hu.le_map_sum (t := Finset.univ) (w := fun _ => 1 / (Fintype.card H : ℝ))
    (p := fun h => x h * C) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun h _ => mul_nonneg (hx h) hC)
  simp only [smul_eq_mul] at hj
  have e : ∑ i, 1 / (Fintype.card H : ℝ) * (x i * C) = C / Fintype.card H := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, hs]; ring
  rw [e, ← Finset.mul_sum] at hj
  unfold welfare
  have := mul_le_mul_of_nonneg_left hj hN.le
  rwa [← mul_assoc, mul_one_div_cancel hN.ne', one_mul] at this

/-- **Concentration is strictly worse** than equality when marginal utility diminishes. -/
theorem concentrated_worse (u : ℝ → ℝ) (hu : StrictConcaveOn ℝ (Ici 0) u) (N : ℝ)
    (hN : 2 ≤ N) (C : ℝ) (hC : 0 < C) :
    u C + (N - 1) * u 0 < N * u (C / N) := by
  have hNp : 0 < N := by linarith
  have h1 : 0 < 1 / N := by positivity
  have h2 : 0 < 1 - 1 / N := by
    rw [sub_pos, div_lt_one hNp]; linarith
  have i := hu.2 (show C ∈ Ici (0:ℝ) from hC.le) (show (0:ℝ) ∈ Ici (0:ℝ) from Set.mem_Ici.2 le_rfl)
    hC.ne' h1 h2 (by ring : 1 / N + (1 - 1 / N) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero] at i
  have e : 1 / N * C = C / N := by ring
  rw [e] at i
  have := mul_lt_mul_of_pos_left i hNp
  have e2 : N * (1 / N * u C + (1 - 1 / N) * u 0) = u C + (N - 1) * u 0 := by
    field_simp
  linarith

/-- **Welfare along a concentrating path.** If household `top` takes everything in the limit,
welfare tends to its concentrated value. -/
theorem concentration_limit [DecidableEq H] (u : ℝ → ℝ) (hu : Continuous u) (C : ℝ)
    (x : ℕ → H → ℝ) (top : H) (htop : Tendsto (fun n => x n top) atTop (𝓝 1))
    (hrest : ∀ k, k ≠ top → Tendsto (fun n => x n k) atTop (𝓝 0)) :
    Tendsto (fun n => welfare u C (x n)) atTop
      (𝓝 (u C + ((Fintype.card H : ℝ) - 1) * u 0)) := by
  have hlim : ∀ k, Tendsto (fun n => u (x n k * C)) atTop
      (𝓝 (u ((if k = top then 1 else 0) * C))) := by
    intro k
    apply (hu.tendsto _).comp
    apply Tendsto.mul_const
    by_cases hk : k = top
    · subst hk; simpa using htop
    · simpa [hk] using hrest k hk
  have hsum := tendsto_finsetSum (s := Finset.univ) fun k _ => hlim k
  unfold welfare
  convert hsum using 2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)]
  rw [show ((if top = top then (1:ℝ) else 0) * C) = C by simp]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => u 0) (fun k hk => by
    simp [Finset.ne_of_mem_erase hk])]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨top⟩), Nat.cast_one]

/-- **Pro rata concentration eventually costs welfare.** -/
theorem concentration_eventually_worse [DecidableEq H] (u : ℝ → ℝ)
    (hu : StrictConcaveOn ℝ (Ici 0) u) (hc : Continuous u) (C : ℝ) (hC : 0 < C)
    (hN : 2 ≤ Fintype.card H) (x : ℕ → H → ℝ) (top : H)
    (htop : Tendsto (fun n => x n top) atTop (𝓝 1))
    (hrest : ∀ k, k ≠ top → Tendsto (fun n => x n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, welfare u C (x n) <
      (Fintype.card H : ℝ) * u (C / Fintype.card H) := by
  have hN' : (2:ℝ) ≤ Fintype.card H := by exact_mod_cast hN
  exact (concentration_limit u hc C x top htop hrest).eventually
    (gt_mem_nhds (concentrated_worse u hu _ hN' C hC))

/-- **An ownership floor gives a welfare floor.** -/
theorem floor_welfare (u : ℝ → ℝ) (hu : MonotoneOn u (Ici 0)) (C f : ℝ) (hC : 0 ≤ C)
    (hf : 0 ≤ f) (x : H → ℝ) (hx : ∀ h, f ≤ x h) :
    (Fintype.card H : ℝ) * u (f * C) ≤ welfare u C x := by
  unfold welfare
  have : ∑ _h : H, u (f * C) ≤ ∑ h, u (x h * C) :=
    Finset.sum_le_sum fun h _ =>
      hu (show f * C ∈ Ici (0:ℝ) from mul_nonneg hf hC)
        (show x h * C ∈ Ici (0:ℝ) from mul_nonneg (hf.trans (hx h)) hC)
        (mul_le_mul_of_nonneg_right (hx h) hC)
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this

end DiminishingWelfare

end

#print axioms DiminishingWelfare.pigou_dalton
#print axioms DiminishingWelfare.equal_maximises
#print axioms DiminishingWelfare.concentrated_worse
#print axioms DiminishingWelfare.concentration_limit
#print axioms DiminishingWelfare.concentration_eventually_worse
#print axioms DiminishingWelfare.floor_welfare
