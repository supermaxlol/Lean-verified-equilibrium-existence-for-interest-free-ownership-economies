# Stage 251 — Automation, ownership and issuance (Study C)

Lean 4.35 / Mathlib, 11 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: revenue `R` split into labour share `lam` and capital share `1 - lam`.

- `income_total` — total household income is `R` at every labour share.
- `income_tendsto` — as `lam → 0`, income tends to `θ h * R`.
- `assetless_tendsto_zero` — an assetless household's income tends to zero.
- `income_floor` — ownership floor `m` gives income floor `(1 - lam) * m * R`.
- `pro_rata_preserves` — pro-rata issuance of new units keeps every share fixed forever.
- `universal_issuance_converges` — if a fraction `σ > 0` of new units is issued equally and
  capital grows at `g > 0`, every share converges to the equal share, geometrically at
  rate `(1 + g(1 - σ)) / (1 + g)`.

Limits: accounting model with exogenous `R`, `g`, `σ`; no saving choice, no trading of
units, no prices. The issuance result is a property of the rule, not an equilibrium outcome.
