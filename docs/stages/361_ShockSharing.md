# Stage 361: a loss under ownership versus debt, with the same resources

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. Source: [`formal/ShockSharing.lean`](../../formal/ShockSharing.lean).

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
