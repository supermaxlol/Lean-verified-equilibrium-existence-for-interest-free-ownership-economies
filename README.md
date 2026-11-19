# Verified Foundations for Interest-Free Finance

**Can an economy run on ownership instead of interest?
We proved that it can, and a computer checked every step.**

## What was achieved

- **Markets clear without interest.** People hold shares in what is produced, not loans.
  Prices are positive, every budget balances, and every market clears.
  No interest rate is used anywhere.
- **Time still has value.** It comes from people's own patience, not from a lending rate.
- **A guaranteed premium adds nothing.** Paying a fixed return on top of a share creates
  no extra value and no better incentive (Stage 350).
- **We show when debt appears, and why.** When people differ in how much risk they can bear,
  someone issues a fixed claim and someone else buys it (Stage 354).
- **The equilibrium is stable.** In the Cobb–Douglas case it is unique, and prices that start
  away from it move back to it (Stage 351).
- **Where concentration comes from.** When households differ in patience, issuing new shares in
  proportion to what people already own concentrates ownership on the most patient. A household
  shut out of new issues is diluted towards zero. Issuing part of new shares equally to everyone
  gives every household a floor (Stage 356).
- **Payouts are exact.** Profit shares and fees are paid in a fixed order, to the last cent.
  No money is lost or created.
- **Every step is machine-checked.** 196 Lean modules and 2,138 audited results. Each one uses
  only the three standard axioms of mathematics (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

- **For Islamic finance.** For fifty years the industry has priced against LIBOR and SOFR.
  Here is a price-setting rule that borrows from neither. Scholars get an exact object to
  rule on. Product designers get a foundation to build on.
- **For an automated economy.** If machines earn more of the income, people live from what
  they own. This proves an economy of owners can clear.
- **For economics.** The classical existence theorems never removed the loan contract.
  This work removes it and still finds equilibrium.
- **For builders.** The settlement rules come with proofs. A platform can implement them
  and know the arithmetic is right.
- **For formal methods.** To our knowledge, one of the largest machine-checked bodies of
  economic theory, released in full with its audit logs.

Anyone can rebuild every module from source with `lake build`
(see [Verify it yourself](#verify-it-yourself)). Proof sources keep their accepted bytes;
cleaned receipts and portable wrappers are listed separately in the docs.

Start with [the detailed status table](docs/PROGRAMME_STATUS.md),
[remaining gaps and claim upgrades](docs/ROADMAP.md), and
[the primary funding constitution](docs/PRIMARY_FUNDING.md).

**Where the mechanism fits in the real world — [technical-fit memos](docs/TECHNICAL_FIT_2026-11-06.md)** (69 memos, §Z failure matrix) and its companion synthesis, **[bigger picture](docs/BIGGER_PICTURE_2026-11-06.md)** (one maths for the last 50 and the next 50).

Reading it in two layers: this page + §Z is the aha (deployable in 2 minutes: two questions, two answers, five rows of what doesn't follow); the 69 memos below it are the evidence layer — load on demand, not "Appendix" burial — read them to see the failure modes, not the success stories.

# One maths for the last 50 and the next 50.

## Solved the 50-year-old Islamic finance maths problem — and the maths problem we will face in the next 50 years

As automation lets capital produce more of the output and labor less of it, the economic question shifts from "what is my wage?" to "what do I own?" Economists have seen this coming — the problem is often posed as whoever owns the machines ends up owning the output — but the ownership answer has always carried an unproven hole: no one had shown that an economy in which people are sustained by ownership of production instead of wages can actually clear — positive prices, budgets that balance, markets that settle — and do so with no interest-rate benchmark anchoring it.

That coherence result is the piece that was missing, and it is what this work supplies, machine-checked: for a defined economy built on state-contingent ownership claims, a competitive equilibrium exists, with binding budgets, exact clearing, and no risk-free lending rate. It does not forecast automation or claim any policy is just or achievable — it proves that the economy such a world would require is mathematically coherent rather than wishful. Interest-free finance is one instance; the result is secular and general.

**What the results reveal, in plain language: [What the maths shows](docs/WHAT_THE_MATHS_SHOWS.md).**

**What is new, and what lies outside mathematics: see [What this contribution is](#what-this-contribution-is), [Relationship to earlier economics](#relationship-to-earlier-economics) and [Scope and research frontier](#scope-and-research-frontier).**

## Why this matters — the missing piece

As automation does this: capital produces more of the output. Labor produces less.

The question changes.
Not "what is my wage?"
"What do I own?"

Economists have seen this coming.
The problem is often posed as *whoever owns the machines ends up owning the output*.

But one hole stayed open.
No one had shown that an economy sustained by **ownership of production instead of wages** can actually clear.

Positive prices. Budgets that balance. Markets that settle.
And do it with **no interest-rate benchmark** anchoring it.

That coherence result is the piece that was missing.
And it is what this work supplies, **machine-checked**.

Take a defined economy built on state-contingent ownership claims.
A competitive equilibrium exists.
Budgets bind. Clearing is exact. No risk-free lending rate is used.

It does not forecast automation.
It does not claim any policy is just or achievable.

It proves that the economy a wage-free world would require is mathematically coherent, rather than wishful.

Interest-free finance is one instance. The result is secular and general.

## Latest connected results

- **Actual heterogeneous overlapping-payoff markets:** existence with global household optimization.
  Positive prices. Binding budgets. Exact clearing.
  Initially assetless households are included in the stated finite CRRA class.
- **Multiplicity and conditional uniqueness:** an actual economy supports two distinct equilibria.
  Around a supported no-net-trade reference, a separate theorem establishes unique actual equilibria.
  One-sided boundary responses hold for sufficiently small admissible joint primitive changes.
- **Ownership certificates and funded protection:** specified denomination. Backing. Exhaustion. Cash-allocation identities.
  Those identities are connected to valuation.
- **Compute and due-date cash:** supplied bottleneck production and funded operating plans produce payoff data.
  The exact cash buffer characterizes payment affordability across supplied state paths.
- **Primary escrow (Stage 209):** 32 audited endpoints.
  Consented settled subscription posting. Budgeted close. Attested release. Ownership activation.
  Cancellation. Affordable non-repeatable refunds. Named dispute scopes.
  Released cash meets the imported operating-buffer condition.
- **Actual voluntary formation (Stages 211–214):** one defined single-new-issue class.
  Funded formation exists iff actual household demand at the construction floor covers supply.
  Floor = construction + buffer + outside option.
  Independent positive future incomes are admitted.
  Arbitrary positive CRRA curvatures are admitted.
  Actual natural-lot choices connect to the reached escrow release.
- **Exact executable funding (Stages 215–218):** integer money refines the real-valued rules.
  The proved dispatcher handles refusals. The versioned protocol handles retries, conflicts and stale versions.
- **Persistence (Stage 219):** complete journal and result encoding are proved. Same-core correspondence holds. Conditional replay recovery holds.
  The local SQLite adapter passes 150 exact comparisons, eight competing-writer schedules, six process-exit cases, 13 corruption rejections.
  SQLite itself is not proved.
- **Connected demonstration (Stage 220):** two households. Unique actual choices.
  Cost-covering formation. Five executable funding requests. Complete recovered state.
  The same final record is obtained in SQLite — including reopening and cached retries.
  This is a risky two-state synthetic enterprise. Not observed fundraising. Not a guaranteed-return investment.
- **Financeability frontier (Stage 222):** hold primitives, payoffs and issue size fixed.
  A formed price gives an exact ceiling on construction, reserve and supplier outside option.
  Formation and dated affordability hold together exactly when the required buffer fits below that ceiling.
  See the [safe reserve window](docs/FINANCEABILITY_FRONTIER.md).
- **Strict participation, stress and exact reserves (Stage 224):**
  Strict issuer participation holds iff actual demand at the funding floor strictly exceeds supply.
  Positive subscribers gain strictly over zero investment.
  Cashflow-loss bounds give funded reserve-stress certificates.
  The integer calculator returns the minimum reserve. It also returns the earliest negative cash prefix.
  Transport passes 566 exact comparisons. Seven malformed inputs are rejected.
  See [the connected guarantees and limits](docs/STRICT_PARTICIPATION_AND_RESERVES.md).
- **Integer payouts, fees and certified price bounds (Stage 226):**
  A declared ordered cumulative-quota rule distributes integer cash after a basis-point fee.
  Fee plus owners is conserved exactly.
  Zero ownership pays zero. Error is below one minor unit per payment.
  This is the declared rule — not the older largest-remainder allocator.
  Household-score certificates enclose the actual formed price.
  Log-utility example: interval `[1.99, 2.01]`. Midpoint error at most `1/100`.
  Strictly inactive households are certified too — without inserting the known price.
  This is a conditional certificate. Not a general numerical solver.
  Transport passes 508 exact comparisons. Eleven malformed inputs rejected. No new database run.
  See [payouts and price certificates](docs/PAYOUTS_AND_PRICE_CERTIFICATES.md).
- **Production, welfare and general-equilibrium frontier (Stages 228–249):**
  Four groups, each closed separately.
  **Production.** Endogenous profit-maximizing production.
  Profit income sits inside household budgets.
  Multi-issue interacting formation.
  Decreasing returns and a money object.
  **Welfare.** First and second welfare theorems.
  A separating-hyperplane score and its wrapper from preferences.
  Core, uniqueness, money premium.
  **Demand.** Both SMD directions. Micro-founded multi-household equilibrium.
  Nash bargaining. Expenditure minimization.
  **Engines.** Set-valued Gale–Nikaido–Debreu. General Berge maximum theorem.
  Price extraction / separating price. Production-economy structure.
  Continuous firm supply over a production set.
  Continuous Mantel surjectivity with Debreu's own weights and genuinely sequential incomplete-market
  equilibrium remain open; see [the frontier note](docs/GE_FRONTIER_2026-11-06.md) and Stages 250–356 below.

The economic and pure executable core is **proved**; the database adapter is
**tested under explicit storage/runtime assumptions**. Truthful physical evidence,
authentication, real custody, legal title and demonstrated social outcomes are
not supplied by these results. See the [connected example](docs/CONNECTED_DEMO.md),
[implementation contract](runtime/README.md) and [roadmap](docs/ROADMAP.md).

## New in this release: Stages 250–356

106 further modules, 1220 further audited declarations. Each module was
compiled on its own against the pinned Mathlib, and its clean axiom log is retained. Per-stage
statements and limits are in [`docs/stages/`](docs/stages/).

- **Classical machinery, from primitives (Stages 252–261, 278).**
  Cobb–Douglas demand derived from utility maximisation.
  Convex-valued production equilibrium. Debreu's decomposition of excess demand.
  The maximum theorem for supply and demand correspondences.
  Blackwell contraction and the Bellman equation.
  Stability and convergence of price adjustment under the weak axiom.
  Arrow–Debreu existence with production and several firms, with exact clearing.
- **Ownership is the equilibrium (Stages 250–252, 265–285, 288, 291, 295, 351–352, 354).**
  With log, homothetic or any CRRA utility, every interior equilibrium is a division of ownership.
  The ownership state prices are the only supporting prices.
  Every efficient interior allocation is a division of ownership.
  A fixed claim layered on ownership is strictly costly.
  Share claims are solvent in every state; fixed claims are not.
  The shadow riskless return is below the expected return on ownership.
  Heterogeneous risk attitudes, CARA risk tolerance and heterogeneous beliefs are covered.
  Wilson's converse: linear sharing forces common cautiousness (also for `n` households, Stage 294).
  Incomplete markets with only equity and debt (Stage 285). With different CRRA coefficients the fixed
  claim is traded in every interior equilibrium: someone issues it and someone holds it (Stage 354).
  Boundary allocations: non-negative optima are interior, for log and every power utility (288, 291, 295).
  Stage 250's ownership-neutral prices now follow from utility maximisation (Stage 352).
  With common Cobb–Douglas preferences the equilibrium is unique and globally stable under price
  adjustment, whatever the ownership distribution (Stage 351).
- **Dynamics (Stages 253, 263–264, 277, 286, 289, 293, 297–299).**
  Lucas-tree ownership equilibria with log and general CRRA utility, many assets, short sales and debt.
  Issuance dynamics as a trading equilibrium, including infinite-horizon savers.
  Saving rules are optimal against whole plans. Transversality is derived from position limits.
  The CRRA optimum in closed form.
- **Interest-free contracting (Stages 301–322, 327, 350).**
  Costly state verification. Random audits (Mookherjee–Png), with a bounded penalty.
  The Border–Sobel audit schedule. Moral hazard, including limited liability.
  Stiglitz–Weiss screening without interest. Selection on the mean under profit sharing.
  Pooling (takaful), its limit, and correlated risks. Exponential tail bounds for the buffer.
  A lender of last resort with a haircut in place of a penalty rate.
  Every Arrow–Debreu equilibrium can be traded with interest-free contracts (Stage 320).
  Innes's theorem: debt is optimal under MLRP (Stage 327). It marks where debt wins, and is reported, not hidden.
  Shape and interest are separable: holding the debt shape fixed, a premium above the zero-return face
  buys no surplus and no effort incentive; it is a transfer less verification cost (Stage 350).
- **Different patience and unequal access (Stage 356, new in v2.3).**
  The stage-263 issuance equilibrium without its uniformity assumptions: each household has its own
  saving rate, and only some have access to the pro rata part of new issues. The market clears at
  `Q = B D/(1 − B)` with return `1/B`, where `B` is the wealth-weighted saving rate. Under pro rata
  issuance the most patient household's share tends to one (log utility, and CRRA with a common `γ`).
  An excluded household is diluted towards zero unless part of issuance is equal; then every household
  keeps a floor, `σ/N` under common patience. With common patience and full access it is exactly stage 263.
- **Sonnenschein–Mantel–Debreu (Stages 262, 287, 292, 296, 300, 302, 306–307, 312, 316, 323–326, 328–349, 353, 355).**
  - Finite price sets: **proved**. Continuous, strictly concave utilities with unique demand, with endowments
    (Stages 296, 300, 326, 329).
  - The revealed-preference Mantel utility is upper semicontinuous but not lower semicontinuous, on any
    compact price set (Stages 316, 324, 328). The endowment rescaling of Stage 323 is necessary (Stage 325).
  - Continuum of prices: Afriat's construction (Stage 330). Unique demand for Debreu's constant-weight
    consumer (331) and for slowly varying weights (335).
  - Debreu's weight `p_k`: reduced to a one-variable inequality (336), proved with an explicit constant (339),
    rationalised with explicit Afriat numbers (344), with unique demand on rich price sets (347) and up to the
    boundary of a closed cap (348). Boundary prices for slowly varying weights are resolved (341, 345).
  - Debreu's weight `A p_k + Z_k`: the Afriat inequalities hold with a quantitative margin (346).
    Assembled (353): a Walras excess demand that is bounded and **Lipschitz** on the cap is, at every
    price of the cap, the sum of `n` optimal trades of continuous, concave, strictly monotone utilities.
    Uniqueness of demand for this weight is not proved.
  - Exact single-price decomposition with the necessary endowment floor (338). Debreu's own decomposition
    overshoots that floor (340).
  - Grid route: optimal trades are stable under locally uniform limits (343). Arzelà–Ascoli compactness
    supplies a limit utility that rationalises the trades at every price, **assuming** a uniform Lipschitz
    bound for the grid utilities (349).
  - That uniform bound exists only when the excess demand is already Lipschitz: a pointwise limit of
    `L`-Lipschitz maps is `L`-Lipschitz, and along any approximation of a non-Lipschitz demand the
    stage-353 Afriat scale degenerates (355). This closes that route; it does not show Mantel fails.

**Research frontier.** Continuous Mantel/Debreu for excess demands that are continuous but
not Lipschitz, with Debreu's own weights. The Lipschitz case is done on the cap (353), and the uniform-
Lipschitz route to the rest is closed (355); a different construction is needed. It is not a failure of
revealed preference. See
[`docs/CONTINUOUS_MANTEL_OBSTRUCTION.md`](docs/CONTINUOUS_MANTEL_OBSTRUCTION.md).

## What this contribution is

This repository is a **sealed 196-module Lean formalization**, SHA-audited and kept to
standard foundations. It answers, with machine-checked proof, two questions the
literature has left open or blurred together:

- **(a) Existence.** An economy of owners, with no lending rate, still clears.
- **(b) Settlement.** Profit shares and fees are paid out exactly, in a fixed order,
  to the last cent, with nothing lost.

Both are proved. Together they are the mechanism the interest-free
programme was missing.

### The "50-year problem" in Islamic finance — what it is

The phrase originates with the critique coined by **M. Ayub (2007)**.
Reinforced by **M. Umer Chapra**. Echoed by **Monzer Kahf**.

Despite five decades of instrument engineering, Islamic finance has not built a genuinely riba-free benchmark.

Practice prices against LIBOR. SOFR. SONIA. MYOR-i.
It preserves a carry on those liquidity assumptions.

Murabaha and tawarruq reproduce the cash-flow shape of conventional credit.
Genuine profit-and-loss sharing (musharakah / mudarabah) remains a small slice of assets.

IIBR and MYOR-i are transaction-referenced Islamic references.
They inherit conventional overnight structure.

None of these is a formal claim made by this repo.
They are the market facts the repo is positioned against.

### What this repository closes, and who settles the rest

| Missing from the 50-year problem | Status |
|---|---|
| A price-formation rule independent of risk-free rates | **Solved, machine-checked** — prices come from what is produced and who owns it; no outside rate is imported |
| Executable, conservation-preserving settlement for equity/profit-share | **Solved, machine-checked** — every payout step is checked, to the last cent, in a fixed order |
| A widely accepted benchmark rate for the industry | **Outside mathematics** — a coordination step for markets and regulators, who can now build on a proved price-formation rule |
| Jurisprudential acceptance by sharia councils | **Outside mathematics** — a ruling for scholars; the proof gives them an exact object to rule on |
| Banks actually stopping LIBOR/SOFR proxies | **Outside mathematics** — an institutional transition, no longer blocked by a missing theory |

**Claim.** *The mathematical core of the 50-year problem is solved: a
machine-checked proof that an ownership economy can price, clear, conserve and
distribute without any interest-rate benchmark.*

Adoption, fiqh rulings and regulation are not mathematical questions, and no proof
can settle them. What changes is where they now stand: on a proved foundation
instead of an open theoretical objection.

## Relationship to earlier economics

[Arrow and Debreu (1954)](https://doi.org/10.2307/1907353) and
[McKenzie (1954)](https://doi.org/10.2307/1907539) proved that equilibrium exists
when households own firms. In their framework interest rates are implied by
intertemporal prices, and the framework never asks the question interest-free
finance asks: if the lending contract is removed and households hold only
ownership claims, does the economy still clear, and where does the time value of
money come from?

This repository answers that question and builds well beyond the classical
existence theorem:

- **Existence without debt.** Equilibrium exists with ownership claims only and no
  benchmark rate; the time value of money is *derived* from household impatience,
  not imposed.
- **Shape versus interest (Stage 350).** A fixed-return premium is separable from
  the shape of a claim and buys no surplus or incentive.
- **Why debt arises at all (Stage 354).** With heterogeneous risk aversion a
  fixed claim is traded in equilibrium, with an identified issuer and holder.
- **Stability and derived demand (Stages 351–352).** The ownership equilibrium is
  unique and globally stable in the Cobb–Douglas class, and its demand is derived
  from preferences, not assumed.
- **Sonnenschein–Mantel–Debreu for ownership economies.** Finite price sets
  (Stages 296–329), the continuous Lipschitz case with explicit concave utilities
  (Stage 353), and a theorem closing the uniform-Lipschitz route (Stage 355).
- **Exact settlement.** Integer payout and fee rules, verified to conserve every
  minor unit.

To our knowledge this is the first machine-checked proof of equilibrium existence
for an interest-free ownership economy, and the first to connect it, in one
verified chain, to executable settlement rules.

## Original foundations module: what is proven

The original `GEOverlap.lean` retains its 25 headline theorem audits. The other
194 modules in `formal/` extend it; the original source and historical seal are
preserved unchanged.

**The machinery**
- **Kakutani** fixed-point theorem for correspondences; **Brouwer** fixed-point theorem.
- **Gale–Nikaido–Debreu existence**: a continuous excess-demand map obeying
  Walras' law on the price simplex has a market-clearing price (strong and weak forms).
- **Berge's maximum theorem** (fixed-, varying-, and compact-subset domain forms):
  demand varies continuously with prices.
- **Budget lower-hemicontinuity**; **unique maximizer from strict concavity**.

**The equilibria** (each built end-to-end on the machinery above)
- **Utility-maximizing households** (`optimizing_economy_equilibrium`): a strictly
  concave utility induces unique, continuous, budget-feasible demand, and a clearing
  price exists at which the optimal allocation satisfies every market.
- **General preferences** (`general_preferences_equilibrium`): the same, for **any**
  continuous strictly-concave utility — not just the quadratic case.
- **Interest-free asset market** (`interest_free_asset_market_equilibrium`): a
  competitive equilibrium for an overlapping-payoff asset market with **no risk-free
  asset** — state-contingent (equity/partnership-like) claims, not fixed-interest debt.
- **Incomplete markets / Radner** (`incomplete_markets_equilibrium_exists`): existence
  witnessed with strictly incomplete asset span (one asset, two states) — the payoff
  needs full *column* rank, never spanning.
- **Multi-period / intertemporal** (`intertemporal_equilibrium_exists`): an
  Arrow–Debreu date-event equilibrium exists over a finite horizon. The equilibrium
  **date-event prices are the discount factors** — time value of money arises as an
  *endogenous shadow price*, with no interest rate, bond, or risk-free asset in the
  primitives.
- **Positive time value from impatience** (`positive_time_value_from_impatience`):
  a one-agent, two-date log-utility economy whose unique competitive equilibrium has
  **discount factor exactly `β ∈ (0,1)`** — future consumption strictly discounted,
  the discount factor being the equilibrium price ratio `p₁/p₀ = β`, with no interest rate.
- **Non-uniqueness** (`equilibrium_not_unique`): an explicit continuous excess demand
  satisfying Walras' law exactly that clears at **two distinct prices** — the
  economically-relevant content of Sonnenschein–Mantel–Debreu, witnessed with a
  non-degenerate (non-autarky) excess demand.
- **Sequential (Radner) trading** (`radner_implements_arrow_debreu`): with Arrow
  securities, the sequential asset-trading budget set *equals* the Arrow–Debreu
  date-event budget set — so the intertemporal equilibrium is implementable by
  one-period asset trading, with no complete date-0 contingent market.
- **Production** (`production_equilibrium_exists`): adding constant-returns
  (zero-profit) firms, a clearing price still exists — consumer excess demand is met
  by production in every market.

The construction uses **no numeraire interest rate**. The classical objection
that valuation, discounting, and equilibrium require an interest-rate benchmark
does not hold for this class.

## Scope and research frontier

Stated precisely, so every result can be checked and built on:

- **Setting.** The standard setting of general-equilibrium theory: finite goods and
  states, concave preferences, explicit structure.
- **Domain.** Mathematics and executable rules. Empirical performance, legal
  enforceability and Shariah rulings are decided by markets, courts and scholars;
  they are outside what any proof settles.
- It establishes **existence and coherence**, with conditional uniqueness and
  sensitivity in additional specified classes. The bounded funding/protection/
  ledger applications now address selected accounting and control rules, not
  the complete safe-claim, liquidity, screening, monitoring or distress functions
  of debt. Modelling those functions in the same verified chain is a natural next step.
- Full payoff rank is not the same as ruling out a certain portfolio. The broad
  class needs no supplied lending benchmark; narrower risky controls and trading
  restrictions retain their own assumptions. Time value is not abolished; it is
  derived, from household impatience rather than an imposed lending rate.
- **Research frontier:** continuous Sonnenschein–Mantel–Debreu *surjectivity* with Debreu's
  own weights on the whole price cap `S_ε`. Finite price sets are proved (Stages
  296–329). The continuum is proved for constant and slowly varying weights (Stages
  330–335) and in part for the weight `p_k` (Stages 336–349). The remaining input is a
  uniform bound on Afriat numbers or on grid utilities, not a failure of revealed
  preference. *Incomplete-market* (GEI) sequential
  equilibrium also remains open in general; Stage 285 covers only equity and debt. Decreasing-returns production with profit-share
  distribution and a money object are now closed in Stages 232/236/238/248;
  *monetary* time value beyond the money-object premium needs further modeling.

## Verify it yourself

Requires Lean 4 (`v4.35.0`). Exact dependency revisions are pinned in
`lake-manifest.json`; see `NOTICE.md` for attribution. The source/log audit uses
only Python 3.11 or newer and does not install tools or rebuild accepted proofs:

```sh
python3 scripts/verify_release.py
```

This checks source/log hashes, import closure, declaration/axiom correspondence,
package pins and the independent exact escrow controls. A fresh kernel build,
when you choose to run one with sufficient disk/memory, is separate:

```sh
lake exe cache get              # fetch the Mathlib build cache
lake build                      # build foundation and extension libraries
```

- `GEOverlap.lean` — the full development.
- `AXIOM_AUDIT.txt` — the axiom audit (every theorem: `[propext, Classical.choice, Quot.sound]`).
- `SEAL_GND.json` — historical foundations snapshot, not the latest gap ledger.
- `formal/` — accepted productive-ownership extension sources (Stages 183–249 and 250–356).
- `docs/stages/` — statement and limits of each stage from 250 on.
- `evidence/verification-manifest.json` — portable module/stage/hash inventory.
- `evidence/axioms/` — clean retained extension compiler/axiom logs.
- `tests/primary_escrow_controls.py` — independent exact specification controls,
  not a proof of implementation refinement or observed economic performance.
- `runtime/` — original-byte SQLite adapter, Lean transport and backend controls;
  portable launch helpers are separate from the kernel-checked proof core.
- `evidence/controls/connected_witness.json` — exact complete economic-example
  initial/final records and requests, with retained execution receipts.

## Author

Shehzad Ahmed — ORCID [0009-0007-3538-6811](https://orcid.org/0009-0007-3538-6811).
