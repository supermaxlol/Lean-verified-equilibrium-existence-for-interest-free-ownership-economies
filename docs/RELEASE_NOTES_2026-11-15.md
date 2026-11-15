# Release notes — 15 November 2026 (v2.2)

Extends the sealed v2.1 release (90 modules, 918 audited declarations) with Stages 250–355.

- Modules: 195 (was 90). Audited declarations: 2,113 (was 918).
- Every new module compiles on its own with `lake env lean` against the pinned Mathlib (v4.35.0).
  Its retained log shows 0 errors, 0 warnings, and only `[propext, Classical.choice, Quot.sound]`.
- `scripts/verify_release.py` checks the hashes, the absence of `sorry`/`admit`/`axiom`/`native_decide`,
  the logs, the audit order and the imports for all 195 modules.
- Per-stage statements and limits: `docs/stages/`.

## What is not claimed

- Continuous Sonnenschein–Mantel–Debreu surjectivity with Debreu's own weights on the whole of `S_ε`
  is **not** proved. See `docs/CONTINUOUS_MANTEL_OBSTRUCTION.md`.
- Stage 349 assumes a uniform Lipschitz bound for the grid utilities. Its limit utility is a cluster
  point, and uniqueness of demand is not carried to the limit.
- Sequential incomplete-market (GEI) equilibrium remains open in general.
- This is not a fresh cold `lake build` of the whole library. Stages up to 249 are the accepted
  sealed sources; stages from 250 on were each compiled standalone.
