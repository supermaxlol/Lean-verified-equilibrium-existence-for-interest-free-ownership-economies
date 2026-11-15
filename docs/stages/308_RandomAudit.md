# Stage 308: Random audits (Mookherjee–Png) and interest-free contracts

Lean 4.35 + Mathlib. 10 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting

There are finitely many states `s` with output `y s ≥ 0`. The borrower:
- reports a state `m`;
- repays `R m`, never more than output (`R ≤ y`);
- is audited with probability `a m`.

A caught lie costs the borrower everything (maximal penalty). Truth-telling therefore means
`(1 − a m)(y s − R m) ≤ y s − R s` whenever report `m` is affordable in state `s`. This is equivalent to
`R s − R m ≤ a m (y s − R m)` (`ic_pair_iff`).

## Results

| Theorem | Content |
|---|---|
| `det_full` | With deterministic audits (`a ∈ {0,1}`), any report a higher-paying state can afford to imitate must be audited for sure (Townsend, stage 301). |
| `full_surrender_audit` | If the borrower hands over all output in state `s` (as debt does in default), any lower report must be audited with probability 1, **even with random audits**. |
| `astar_ic` | The minimal random audit `a*(m) = max_s (R s − R m)/(y s − R m)`, taken over affordable lies, is incentive compatible. |
| `astar_lt_one` | If the borrower keeps a strictly positive residual in every state, `a*(m) < 1` for every report. |
| `astar_le_det` | `a*` never exceeds any deterministic incentive-compatible audit rule. |
| `cost_saving` | So randomization strictly lowers expected verification cost whenever some report with positive probability was audited for sure. |
| `ps_astar_le` | Profit sharing with share `θ` (`R = θy`) needs audit probability at most `θ` at every report. |
| `ps_break_even` | An interest-free profit-sharing contract recovers principal `I` whenever `I ≤ θ(E[y] − c)`. |
| `ps_beats_debt` | Random-audit profit sharing has strictly lower verification cost than deterministic debt once `θ < P(y < D)`. |

## Reading for the thesis

Stages 301 and 303 found that, with deterministic audits, debt is the cheapest contract to verify and
profit sharing costs `c · P(no default)` more. That ranking depends on audits being deterministic.

With random audits and a maximal penalty, two things change:
- What drives the audit burden is the residual the borrower keeps. Debt's full surrender in default is
  exactly what forces certain audits.
- Profit sharing leaves a residual `(1 − θ) y` in every state. Its audit probability is capped at `θ`,
  so its expected audit cost is at most `cθ`.

With a small enough share, the interest-free equity contract audits more cheaply than debt.

## Limits

* This is **not** the full Mookherjee–Png / Border–Sobel optimal-contract characterisation. It does not
  prove which contract is optimal. It proves:
  - randomization strictly helps whenever the borrower keeps a residual;
  - it cannot help between full-surrender states;
  - profit sharing's audit cost is at most `cθ`.
* The maximal penalty (losing everything when caught) is assumed. With bounded penalties the required
  audit probabilities rise.
* The comparison in `ps_beats_debt` is against **deterministic** debt. Random-audit debt with a
  default residual is not separately optimised here.
* Commitment to the audit probabilities is assumed.
