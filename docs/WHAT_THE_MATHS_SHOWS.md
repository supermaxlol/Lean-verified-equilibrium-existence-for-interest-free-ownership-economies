# What the maths shows

A plain-language reading of the machine-checked results, organised in layers, from the
foundations to what the models say *against* the interest-free case. Stage numbers point
to `docs/stages/` (Stages 250 on) and to `docs/PROGRAMME_STATUS.md` (earlier stages).
Each stage states its own setting and limits; read them before quoting a result.

## 1. The economy is coherent without interest

- **Equilibrium exists without a risk-free asset.** Brouwer and Kakutani give
  Gale–Nikaido–Debreu, which gives a competitive equilibrium. This holds with
  utility-maximising households, any continuous strictly concave utility, incomplete
  (Radner) markets, many dates, and production.
- **Time value comes from impatience, not interest.** Discounting appears as date-event
  prices with discount factor β. The equilibrium return on ownership is exactly `1/β`
  (Stage 263). The "rate" is simply how impatient people are.
- **Both welfare theorems hold, and equilibrium lies in the core** (Stages 235, 237, 265).
  Interest-free markets are Pareto-efficient, and no coalition can block the outcome.
- **Interest-free contracts are enough.** Every Arrow–Debreu equilibrium can be traded with
  interest-free contracts alone (Stage 320).

## 2. Automation: income moves from wages to ownership (Stages 250–253)

- As the labour share falls to 0, each household's income tends to its ownership share
  times revenue, and an assetless household's income tends to zero (Stage 251).
- An ownership floor guarantees an income floor (Stage 251).
- **Issuance decides the distribution.** Pro-rata issuance of new units freezes every share
  forever. Issuing even a fraction `σ > 0` of new units equally makes shares converge
  (Stage 251).
- **Prices do not depend on who owns what.** With Cobb–Douglas preferences, aggregate
  demand and clearing prices are independent of the ownership distribution (Stage 250; the
  demand is derived from utility maximisation in Stage 352). The equilibrium is unique and
  globally stable under price adjustment, whatever the ownership distribution (Stage 351).
- The issuance-market unit price is `β d / (1 + g)`, set by dividends, growth and
  impatience only (Stage 253).

## 3. Ownership is the efficient allocation (Stages 266–285)

- With common log, homothetic or CRRA utility, every interior equilibrium and every
  efficient interior allocation is a division of ownership, and only the ownership state
  prices support it (Stages 268, 275, 276, 280, 281).
- A fixed claim layered on ownership is strictly costly (Stages 267, 270).
- **Debt is redundant even when available** (Stage 285). Offer households both a bond and a
  share: no one issues or holds the bond, and the bond market is zero in equilibrium.
  (Common preferences and beliefs; prices taken from the ownership equilibrium.)
- **Share claims are solvent in every state.** A fixed-claim issuer defaults exactly when
  `Y s < b / a`, and fixed claims exceeding output leave someone unpaid (Stage 272).
- The riskless return exists only as a shadow price, strictly below the expected return on
  ownership whenever output varies (Stage 271; log utility, one date).

## 4. Dynamics (Lucas trees, Stages 263–264, 277, 286–299)

- Asset prices come from dividends and consumption, with many assets, short sales, debt in
  zero net supply, and heterogeneous households.
- **Position limits replace the transversality condition** (Stage 297). Bounded positions
  rule out bubbles, with no interest-rate condition.
- Saving rules are optimal against whole plans, not only one-step deviations.

## 5. Where pure ownership is not enough (Stages 282–284, 290, 294)

- When risk attitudes differ, optimal sharing is shifted-linear: it has a fixed component.
- Wilson's converse: pure proportional sharing requires everyone to have the same
  cautiousness (Stage 290; `n` households, Stage 294).
- So a fixed component is justified by heterogeneity, not by interest, and it can be
  interest-free.

## 6. Information problems: the real case for debt

These results do not all favour profit sharing. They are reported, not hidden.

- **Verification (Stage 303).** A contract only divides surplus; verification cost is the
  only thing that destroys it. Debt verifies only on default. A truthful profit share must
  verify every state except the top output. Debt saves exactly `c · P(y ≥ D)`.
- **Flat repayment needs no audits** (Stage 319). An audit-free scheme exists if and only if
  every state's output covers the principal.
- **Moral hazard (Stages 309, 321).** Profit sharing dulls effort (gain `(1 − θ) ΔY`).
  Financing is capped below first-best, and limited liability leaves the borrower a rent of
  at least `κ`.
- **Innes (Stage 327).** Under MLRP, debt `min(y, D)` gives the strongest effort incentive
  among monotone limited-liability contracts.
- **Reading.** Every one of these favours the debt *shape* (a fixed repayment). None needs
  *interest*: in Stage 301 the lender's outside option is cash at zero return. Stage 350
  proves the separation: holding the debt shape fixed, any premium above the zero-return
  face lowers (weakly) total surplus, the borrower's residual and the effort incentive, and
  the lender gains at most what the borrower loses. The economics justify the shape, not
  the interest.
- **Different risk attitudes (Stage 354).** With different CRRA coefficients, the fixed
  claim is traded in every interior equilibrium of an equity-and-debt market: someone
  issues it and someone holds it. It is priced at par; no premium is involved.

## 7. Where interest itself fails

- **Credit rationing (Stage 314, Stiglitz–Weiss).** Raising the rate drives out safe
  borrowers first. In the worked example, raising the rate from 0.9 to 1.0 drops the
  lender's return from 0.675 to 0.5. The rate cannot clear the credit market.
- **Profit sharing removes risk selection but leaves selection on the mean** (Stage 318).
  Above-average types overpay by `(I − k)|μ − μ̄| / μ̄`, which falls to zero as the
  borrower's own contribution rises.

## 8. Interest-free institutional replacements

- **Audits instead of rates (Stages 308, 313, 315, 319).** The least audit probability is
  exactly `D / (D + F)`; any positive fine makes certain audits unnecessary. The
  Border–Sobel audit schedule is solved, with closed forms for two states.
- **Takaful pooling (Stages 304, 310, 322).** Pooling removes idiosyncratic risk (variance
  `v / N` when independent). It never removes the mean or correlated risk, which has a
  floor `ρ v` at any pool size. Correlated risk must be held as capital.
- **Buffer sizing (Stage 317).** Chernoff bounds give an explicit reserve that fails with
  probability at most `ε`, with no variance needed.
- **Lender of last resort without a penalty rate (Stage 305).** A haircut covering the
  worst collateral drop gives the central bank zero expected loss; a larger haircut never
  raises it.

## 9. Funding mechanism and money (Stages up to 249)

- Verified voluntary formation (an issue forms if and only if its funding floor is met),
  primary escrow, integer-money execution, persistence, reserve and stress certificates,
  integer payouts and certified price bounds. This is the deployable layer.
- Decreasing returns give strictly positive rent (Stage 232).
- A money object can be worth more than its cash flows by a convenience premium, even with
  zero cash flow (Stage 232).

## 10. Aggregate behaviour is unconstrained (Sonnenschein–Mantel–Debreu)

- On finite price sets, any excess demand consistent with Walras' law comes from rational
  households with continuous, strictly concave utility and unique demand (Stages 296, 300,
  326, 329). On the continuum, every bounded **Lipschitz** Walras excess demand on the
  price cap is a sum of rational consumers' trades (Stage 353). The merely continuous case
  is open, and the uniform-Lipschitz route to it is provably closed (Stage 355).
- So an interest-free economy can have multiple equilibria and unstable price adjustment,
  like any other. Stability must be designed through solvency, position limits and
  buffers. Removing interest does not buy it.
- Price adjustment is stable under the weak axiom (Stages 255, 259), so there are known
  sufficient conditions.

## 11. Where concentration comes from (Stage 356)

The issuance equilibrium of Stage 263 assumed that everyone has the same patience, the same
saving rate and the same access to new units. Stage 356 drops all three.

- The units market still clears exactly, at a return of `1/B`, where `B` is the wealth-weighted
  saving rate. Each household's post-trade share follows from clearing.
- Under pro rata issuance, the most patient household's share tends to one and every other share
  to zero. This holds for log utility and for CRRA with a common curvature, along any return path.
- A household shut out of new issues is diluted towards zero.
- Issuing part of new units equally to every household gives each one a floor in every period;
  an excluded household keeps a long-run share near `σ/N`.

So the issuance rule decides whether ownership concentrates, and differences in patience and
access are what drive the concentration.

## 12. Where ownership settles in the long run (Stages 357, 359, 363, 365, 367, 368, 376)

- With any positive equal part of issuance there is exactly one long-run distribution, in closed
  form, and every household holds at least a fixed floor in it (357). From every starting point the
  economy converges to it geometrically (363); with common patience the limit is equal ownership (367).
- When patience or access depends on wealth, a long-run distribution still exists for every
  continuous rule (365) and for threshold rules (368). But it need not be unique: explicit economies
  have two or three rest points, one of them a **poverty trap** in which a household stays below the
  access threshold for ever, although equal shares are also a rest point (368).
- An explicit condition rules this out: if saving rates vary little with wealth relative to the
  lowest saving rate, and enough of issuance is equal, the rest point is unique and reached from
  everywhere (376).
- **Control.** Voting weight follows ownership. Under pro rata issuance a majority, once held, is
  held for ever; any positive equal part dissolves every minority majority in finite time (359).

## 13. Growth and welfare (Stages 360, 362)

- With common patience the issuance rule costs no growth at all. With different patience, spreading
  ownership costs at most half the spread of patience times the share moved (360).
- With diminishing marginal utility, equal ownership gives the most welfare from a given output, and
  full concentration is strictly worse (362). Output is held fixed, so this is about distribution, not growth.

## 14. Equilibrium paths through time (Stages 364, 370, 373, 378, 383, 387)

- With forward-looking CRRA saving, an equilibrium path exists at every finite horizon for every
  curvature `γ > 0`, and at the infinite horizon for `γ ≥ 1` (for `γ < 1` under an explicit condition) (364).
- The path is unique for log utility, for common patience, at horizon one (370); at horizon two for every
  `γ > 0` (387); at every finite horizon under a band on `γ` (378); and at every finite horizon for
  `γ ≤ 1` between ordered paths (383).

## 15. Interest, money and loss (Stages 358, 361, 369, 377, 381, 384, 385)

- **The Ramsey return is paid by ownership.** The Euler condition says waiting must earn
  `(1 + g)/β` (log utility). Ownership of output pays exactly that, with no loan; a common change in
  prices leaves it unchanged, while a nominal claim loses it to inflation (358).
- **Losses.** With the same resources and the same loss, ownership splits the loss in proportion to what
  each party put in; debt puts it on the entrepreneur first and protects the creditor until the
  entrepreneur is wiped out (361).
- **Money that pays no interest can have value.** In an overlapping-generations economy, fiat money is
  valued exactly when the young would like to save at the growth rate (the Samuelson condition), and it
  makes every generation better off than autarky (369). Its return is the growth rate, not interest.
- Growing the money stock taxes money holders; a constant stock is the best steady state (377). For
  `γ ≤ 1` every non-stationary path collapses to zero with rising inflation (381, 384); for `γ > 2`
  two-period cycles exist under an explicit slope condition (385).

## 16. Many assets and incomplete markets (Stages 366, 371, 375, 380, 382, 386)

- An equity-and-bond economy with different risk attitudes has an equilibrium, and the bond is traded in
  it (366, with 354). With many assets, equilibrium exists for a common CRRA coefficient (371) and for
  different coefficients when markets are complete (375).
- With incomplete markets each household's optimum exists and is unique at every arbitrage-free price
  (380), demand is continuous (382), and equilibrium exists with any number of assets and different
  risk attitudes, for one period and one good (386). This last result is classical; it is now machine-checked.

## 17. Continuous excess demand (Stages 372, 374, 379)

- A continuous Walras excess demand, with no Lipschitz bound, splits into `n` consumers whose trades
  satisfy the weak and strong axioms (372), and each is the unique best choice of a **continuous**,
  monotone, quasi-concave utility, with endowments and non-negative consumption (379).
- What is still missing relative to the textbook theorem is strictness: preferences here are weakly
  monotone and convex, not strictly.

## Synthesis

1. Interest is not needed for markets to work: equilibrium, time value, efficiency and
   asset pricing all exist without it.
2. Ownership is the natural allocation, and fixed claims are redundant or costly in the
   benchmark.
3. Where fixed claims help (differing risk attitudes, verification, effort), what helps is
   the shape of the contract, not interest.
4. Interest has its own failure mode: credit rationing.
5. The real costs of going interest-free are concrete: audit costs, agency rents, mean
   selection, and correlated risk that must be held as capital. Each has an instrument and
   a formula.
6. Under automation, the decisive variable is how new ownership is issued: with different
   patience or access, pro rata issuance concentrates ownership, and an equal part keeps a floor
   under every household (Stage 356). Any positive equal part gives a unique long-run
   distribution with a floor; wealth-dependent access can create a poverty trap (357, 368).
7. Time value is a return on ownership: the Ramsey return is paid by owning output, and
   interest-free money can be valued (358, 369).
8. With the same resources, ownership shares a loss; debt concentrates it (361).
9. With diminishing marginal utility, spreading ownership raises welfare from the same output,
   and with common patience it costs no growth (360, 362).

## Where mathematics stops, and what comes next

Empirical magnitudes, institutional adoption and Shariah rulings are questions for markets,
regulators and scholars; no proof settles them, and these results give each of them a proved
foundation to work from. Inside mathematics, the open problems are:

- **Multi-period (sequential) incomplete markets.** Stage 386 is one period and one good; existence
  with dates, which is the setting of real ownership economies, is the most important next step.
- **Strictness in continuous Mantel.** Stage 379 gives continuous, monotone, quasi-concave utilities
  for continuous excess demand; strictly monotone, strictly convex preferences remain open.
- **Path uniqueness for `γ > 1`** at horizon three or more, without ordering (387 settles horizon two).

Some stages work in the classic textbook settings
(Cobb–Douglas preferences in Stages 250–252 and 351, one date in Stages 271 and 354), and each
stage's exact hypotheses are stated in its own file.
