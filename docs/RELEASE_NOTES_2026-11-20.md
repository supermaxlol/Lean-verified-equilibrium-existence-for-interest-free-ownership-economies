# Release notes — 20 November 2026 (v2.4)

Extends v2.3 (196 modules, 2,138 audited declarations) with Stages 357–387.

- Modules: 227 (was 196). Audited declarations: 2,484 (was 2,138).
- Each new module compiles on its own with `lake env lean` against the pinned Mathlib (v4.35.0).
  Its retained log shows 0 errors, 0 warnings, and only `[propext, Classical.choice, Quot.sound]`.
  Each new module imports only Mathlib and, where it uses Brouwer's theorem,
  `FixedPointTheorems.brouwer`; definitions from earlier stages are restated in each file.
- `scripts/verify_release.py` passes for all 227 modules.
- Per-stage statements and limits: `docs/stages/357_*.md` to `docs/stages/387_*.md`.

## What is new

**Ownership dynamics (Stages 357, 359, 360, 362, 363, 365, 367, 368, 376).**
- The long-run distribution under mixed issuance exists, is unique, and has a closed form; every share
  has a floor (357). With constant saving rates every positive starting distribution converges to it
  geometrically (363); with common patience the limit is equal ownership (367).
- With patience or access that depends on wealth, a long-run distribution still exists for every
  continuous rule (365, Brouwer) and for monotone threshold rules (368, Knaster–Tarski). It need not be
  unique: explicit examples have two or three rest points, including a poverty trap (365, 368). An
  explicit Lipschitz condition restores uniqueness and global convergence (376).
- Control: under pro rata issuance a majority is permanent; any positive equal part dissolves every
  minority majority in finite time (359).
- Growth and welfare: with common patience the issuance rule costs no growth; otherwise the cost is
  bounded by the spread of patience times the share moved (360). With diminishing marginal utility, equal
  ownership maximises welfare from a given output, and concentration lowers it strictly (362).

**Perfect-foresight equilibrium paths (Stages 364, 370, 373, 378, 383, 387).**
- A finite-horizon equilibrium path with forward-looking CRRA saving exists for every `γ > 0` (364,
  Brouwer); the infinite-horizon path exists for `γ ≥ 1`, and for `γ < 1` under an explicit condition.
- Uniqueness: log utility, common patience, horizon one (370); horizon two for `1/2 < γ² < 2` (373);
  every finite horizon under a band that narrows with the horizon (378); every finite horizon for
  `0 < γ ≤ 1` between ordered paths (383); horizon two for every `γ > 0`, with no ordering and no band (387).

**Interest, money and loss sharing (Stages 358, 361, 369, 377, 381, 384, 385).**
- The Ramsey (Euler) return is paid in full by ownership of output, and is kept under inflation, where a
  nominal claim loses it (358).
- With the same resources and the same loss, ownership shares the loss pro rata; debt puts it on the
  entrepreneur first (361).
- Interest-free fiat money has value in an overlapping-generations economy exactly under the Samuelson
  condition, and improves on autarky (369). With a growing money stock the inflation tax lowers real
  balances, and a constant stock is the best steady state (377).
- Transition paths: for `γ ≤ 1` every path either stays at the monetary steady state or collapses to zero,
  with rising inflation (381, 384). For `γ > 2` two-cycles exist under an explicit slope condition (385).

**Incomplete markets and many assets (Stages 366, 371, 375, 380, 382, 386).**
- Equity-and-bond equilibrium with heterogeneous CRRA exists (366). Many assets with common CRRA (371),
  and many assets with heterogeneous CRRA under complete markets (375).
- Incomplete markets: the household optimum exists and is unique at every arbitrage-free price (380);
  demand is continuous and equilibrium reduces to clearing of payoffs (382); equilibrium exists with any
  number of assets, incomplete markets and heterogeneous CRRA, in the one-period, one-good economy (386).

**Sonnenschein–Mantel–Debreu for continuous excess demand (Stages 372, 374, 379).**
- A continuous (not only Lipschitz) Walras excess demand is a sum of `n` trades that satisfy the weak and
  strong axioms (372), rationalised by monotone quasi-concave utilities (374), and then by **continuous**,
  monotone, quasi-concave utilities, with endowments and non-negative consumption (379).

## What is not claimed

- Several of these are classical theorems given a machine-checked proof in the stated setting, not new
  theorems: for example one-period incomplete-markets existence with one good (386), the Samuelson
  condition (369), and Negishi existence under complete markets (375).
- SMD (379): preferences are weakly monotone and convex, not strictly; the full theorem with strictly
  monotone, strictly convex preferences for continuous non-Lipschitz excess demand remains open.
- Multi-period (sequential) incomplete-markets existence is not proved; 386 is one period, one good.
- Path uniqueness for horizon three or more with `γ > 1` and unordered paths is not proved. Existence of the
  infinite-horizon path for `γ < 1` needs a stated condition.
- Patience, access and saving rules are exogenous where stated; optimality of the forward-looking saving
  rule (sufficiency including transversality) is not formalized (364).
- Money results are for a one-good overlapping-generations economy with lump-sum injections; there is no
  bank money or credit.
- This is not a fresh cold `lake build` of the whole library. Stages up to 249 are the accepted sealed
  sources; stages from 250 on were each compiled standalone.
