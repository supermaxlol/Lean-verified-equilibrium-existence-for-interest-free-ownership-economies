# Release notes — 19 November 2026 (v2.3)

Extends v2.2 (195 modules, 2,113 audited declarations) with Stage 356.

- Modules: 196 (was 195). Audited declarations: 2,138 (was 2,113).
- Stage 356 (`formal/HeterogeneousIssuance.lean`) rebuilds the stage-263 issuance equilibrium without
  its three uniformity assumptions: households differ in patience (saving rate) and in access to new
  units, and the issuance rule mixes an equal part with a pro rata part.
  - The market clears at `Q = B D/(1 − B)` with return `1/B`, where `B` is the wealth-weighted saving rate.
  - Under pro rata issuance the most patient household's share tends to one (log utility, and CRRA with a common `γ`).
  - A household without access is diluted towards zero unless part of issuance is equal; then it keeps
    a floor, `σ/N` under common patience.
  - With common patience and full access the model reduces exactly to stage 263.
- The new module compiles on its own with `lake env lean` against the pinned Mathlib (v4.35.0).
  Its retained log shows 0 errors, 0 warnings, and only `[propext, Classical.choice, Quot.sound]`.
- `scripts/verify_release.py` passes for all 196 modules.

## What is not claimed

- Saving rates are given paths (optimal for log utility; stationary for CRRA). Patience and access are exogenous.
- Continuous Sonnenschein–Mantel–Debreu surjectivity with Debreu's own weights remains open
  (see `docs/CONTINUOUS_MANTEL_OBSTRUCTION.md`).
- This is not a fresh cold `lake build` of the whole library. Stages up to 249 are the accepted
  sealed sources; stages from 250 on were each compiled standalone.
