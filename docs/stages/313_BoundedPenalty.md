# Stage 313: Random audits with a bounded penalty

Lean 4.35 + Mathlib. 12 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

A detected misreport pays the true repayment plus a fine `F`; a lie saves gap `D` unless audited (probability `a`).
- `ic_iff`: truth-telling ⟺ `(1−a)D ≤ aF`.
- `ic_of_need`, `need_le_of_ic`: the least audit probability is exactly `D/(D+F)`.
- `need_lt_one`: any positive fine makes certain audits unnecessary.
- `need_zero_fine`: with no fine, audits must be certain.
- `need_anti`, `need_tendsto`: the requirement falls in F and tends to 0 (Becker).
- `need_mono`: the requirement rises with the gap.
- `ps_uniform_ic`: under profit sharing (gap ≤ θΔ) a uniform audit probability `θΔ/(θΔ+F)` is incentive compatible.
- `ps_cost_le_debt`: its cost is below debt's `cG/(G+F)` whenever θΔ ≤ G.
- `ps_need_tendsto`: as θ → 0 the audit requirement → 0.

Reading: this extends 308 from maximal to bounded penalties. Profit sharing's verification burden scales with θ.

Honest limits:
- The fine is assumed collectable.
- Commitment to audit is assumed.
- Uniform rules, not the optimal report-dependent rule.
