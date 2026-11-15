# Stage 250 — Initial ownership and distribution (Study A)

Lean 4.35 / Mathlib, 10 declarations, all `[propext, Classical.choice, Quot.sound]`. Mathlib-only.

Setting: households with labour income `L h` and ownership share `θ h` of profit `π`;
demand taken in identical Cobb–Douglas form (assumed demand rule, not derived here).

- `capital_income_share` — capital income shares equal ownership shares.
- `assetless_bound` — an assetless household spends at most its labour income.
- `aggregate_demand_ownership_neutral`, `clearing_ownership_neutral` — aggregate demand and
  market-clearing prices do not depend on the ownership distribution.
- `consumption_share`, `pure_capital_consumption` — consumption is the wealth (ownership) share
  of aggregate consumption.
- `assetless_no_labour_zero` — no labour income and no ownership gives zero consumption.

Reading: the market mechanism passes the initial ownership distribution through unchanged.
Limits: static, one firm, identical homothetic demand. Neutrality of prices fails for
non-homothetic or heterogeneous preferences.
