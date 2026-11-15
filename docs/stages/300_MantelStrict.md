# Stage 300: Mantel on finite price sets with strictly concave utilities and unique demand

Lean 4.35 + Mathlib. 8 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

## Setting
Same as stage 296: finitely many strictly positive, distinct, normalised price vectors `p k`, and
an arbitrary target excess demand `Z k` satisfying Walras `p k · Z k = 0`. Net-trade budget `p · y ≤ 0`.

## Results
- `psi_strict`, `brk_lt`: the correction `ψ y = ∑ s, -exp (-y s)` is strictly concave, and its tangent gap is strictly negative away from the tangent point.
- `su_continuous`, `su_strictConcave`, `su_strictMono`: the corrected Afriat utility is continuous, strictly concave and strictly increasing.
- `su_unique_opt`: each data point is the *unique* optimum on its budget set.
- `afriat_strict`: from a strict potential, build such a utility rationalising the data (a strict Afriat margin from a larger exponent, then a small `δ` chosen by a filter argument).
- `mantel_strict`: there are `|S|` households with continuous, strictly concave, strictly increasing utilities whose *unique* demands at each `p k` sum to `Z k`.

## Reading
Stage 296 had concave piecewise-linear utilities, so demand could be a set. Here demand is a
function: at every observed price each household has exactly one optimum. So "anything goes"
for aggregate excess demand (Sonnenschein–Mantel–Debreu) holds on finite price sets even with
textbook-quality preferences.

## Limits
- Finite price sets only. The full Debreu 1974 statement (every continuous Walras function on an open price set) is not proved.
- Utilities are strictly concave but not smooth (minimum of smooth pieces).
- Net-trade formulation, `p · y ≤ 0`.
