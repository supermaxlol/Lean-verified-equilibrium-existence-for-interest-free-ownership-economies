import Mathlib

/-!
# Stage 361: a loss under ownership versus debt, with the same resources

An enterprise has assets `V = E + F`: the entrepreneur puts in `E > 0` and an outside party
`F > 0`. A loss `L` with `0 ≤ L ≤ V` occurs.

* Ownership: the outsider holds the share `s = F / (E + F)` and bears `s L`; the entrepreneur
  bears `(1 − s) L`.
* Debt at par `F`: the entrepreneur bears `min L E` first; the creditor bears `max (L − E) 0`.

Results:
* `equity_conserves`, `debt_conserves`: both arrangements allocate exactly the whole loss.
* `equity_proportional`: under ownership each party's share of the loss equals its share of
  the resources it put in.
* `debt_shifts_to_entrepreneur`: the entrepreneur's loss under debt is at least its loss under
  ownership, and the creditor's is at most the owner's.
* `small_loss_all_on_entrepreneur`: if `L ≤ E`, the creditor loses nothing and the
  entrepreneur bears the entire loss.
* `debt_wipeout`: under debt, a loss `L ≥ E` leaves the entrepreneur with nothing.
* `equity_survives`: under ownership the entrepreneur keeps `(1 − s)(V − L) > 0` whenever
  `L < V`.

Reading: with identical resources and an identical loss, ownership spreads the loss in
proportion to what each put in; debt concentrates it on the entrepreneur and protects the
creditor until the entrepreneur is wiped out.
-/

noncomputable section

namespace ShockSharing

def share (E F : ℝ) : ℝ := F / (E + F)

def eqOutsider (E F L : ℝ) : ℝ := share E F * L
def eqEntrepreneur (E F L : ℝ) : ℝ := (1 - share E F) * L
def debtEntrepreneur (E L : ℝ) : ℝ := min L E
def debtCreditor (E L : ℝ) : ℝ := max (L - E) 0

theorem equity_conserves (E F L : ℝ) : eqOutsider E F L + eqEntrepreneur E F L = L := by
  unfold eqOutsider eqEntrepreneur; ring

theorem debt_conserves (E L : ℝ) : debtEntrepreneur E L + debtCreditor E L = L := by
  unfold debtEntrepreneur debtCreditor
  rcases le_total L E with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

theorem equity_proportional (E F L : ℝ) (hE : 0 < E) (hF : 0 < F) :
    eqOutsider E F L = F / (E + F) * L ∧ eqEntrepreneur E F L = E / (E + F) * L := by
  refine ⟨rfl, ?_⟩
  unfold eqEntrepreneur share
  have : E + F ≠ 0 := by linarith
  field_simp
  ring

theorem share_mem (E F : ℝ) (hE : 0 < E) (hF : 0 < F) : 0 < share E F ∧ share E F < 1 := by
  unfold share
  exact ⟨div_pos hF (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- **Debt shifts the loss onto the entrepreneur.** -/
theorem debt_shifts_to_entrepreneur (E F L : ℝ) (hE : 0 < E) (hF : 0 < F) (hL : 0 ≤ L)
    (hLV : L ≤ E + F) :
    eqEntrepreneur E F L ≤ debtEntrepreneur E L ∧ debtCreditor E L ≤ eqOutsider E F L := by
  have key : eqEntrepreneur E F L ≤ debtEntrepreneur E L := by
    unfold eqEntrepreneur debtEntrepreneur share
    have hEF : 0 < E + F := by linarith
    have e : (1 - F / (E + F)) * L = E * L / (E + F) := by field_simp; ring
    rw [e, div_le_iff₀ hEF]
    rcases le_total L E with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  refine ⟨key, ?_⟩
  have h1 := equity_conserves E F L
  have h2 := debt_conserves E L
  linarith

theorem small_loss_all_on_entrepreneur (E L : ℝ) (hLE : L ≤ E) :
    debtCreditor E L = 0 ∧ debtEntrepreneur E L = L := by
  unfold debtCreditor debtEntrepreneur
  exact ⟨max_eq_right (by linarith), min_eq_left hLE⟩

/-- **Debt wipes out the entrepreneur** once the loss reaches its stake. -/
theorem debt_wipeout (E L : ℝ) (hLE : E ≤ L) : E - debtEntrepreneur E L = 0 := by
  unfold debtEntrepreneur
  rw [min_eq_right hLE]; ring

/-- **Ownership keeps the entrepreneur in business** while any value remains. -/
theorem equity_survives (E F L : ℝ) (hE : 0 < E) (hF : 0 < F) (hLV : L < E + F) :
    0 < (1 - share E F) * (E + F - L) := by
  have := (share_mem E F hE hF).2
  exact mul_pos (by linarith) (by linarith)

end ShockSharing

end

#print axioms ShockSharing.equity_conserves
#print axioms ShockSharing.debt_conserves
#print axioms ShockSharing.equity_proportional
#print axioms ShockSharing.debt_shifts_to_entrepreneur
#print axioms ShockSharing.small_loss_all_on_entrepreneur
#print axioms ShockSharing.debt_wipeout
#print axioms ShockSharing.equity_survives
