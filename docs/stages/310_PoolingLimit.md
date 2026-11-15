# Stage 310: The pooling limit

Lean 4.35 + Mathlib. 7 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Stage 304 proved that the per-member pooled-loss variance is `ρv + (1−ρ)v/N`.

- `pv_tendsto`: it tends to exactly `ρv` as `N → ∞`.
- `pv_antitone`, `pv_floor`: it decreases in `N` and never falls below `ρv`.
- `pv_eventually_lt`: any target above `ρv` is eventually met.
- `pv_indep`, `pv_indep_tendsto`: with independent losses it is `v/N → 0`.
- `reserve_floor`: a per-member Chebyshev reserve `k` with failure probability ≤ α must satisfy `k² ≥ ρv/α` at every pool size.

Reading: takaful pooling removes idiosyncratic risk, but correlated risk must be held as capital (or covered by the LOLR, stage 305).

Honest limits: equicorrelated losses; Chebyshev only.
