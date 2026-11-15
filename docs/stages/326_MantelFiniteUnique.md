# Stage 326: Mantel on finite price sets with unique demand

Lean 4.35 + Mathlib. 24 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings. (The file reproduces stage 296 in full and adds the declarations below.)

## Results
- `bg` and its lemmas (`bg_self`, `bg_nonpos`, `bg_neg`, `bg_concave`): the Bregman-type penalty `bg t a = e^{-a} - e^{-t} - e^{-a}(t - a)` is zero at `t = a`, strictly negative elsewhere, and concave in `t`.
- `step_le`, `step_lt`, `pc_*`: the perturbed Afriat piece `-T_k + L T_k p_k·y + ε ∑ₛ bg(yₛ, x_{k,s})` is continuous and concave. It is strictly increasing in every coordinate once `ε e^{-x_{k,s}} < L T_k p_{k,s}`.
- `au_continuous`, `au_concave`, `au_strictMono`: the minimum of these pieces is a continuous, concave, strictly monotone utility.
- `strict_afriat`: a strict potential on the data gives Afriat numbers `L > 0`, `T > 0` with strict inequalities `-T_l < -T_k + L T_k p_k·x_l` for `k ≠ l`.
- `afriat_unique`: for `ε > 0` small enough, the perturbed utility rationalizes the data, and each observed bundle is the unique optimum on its budget set.
- `mantel_finite_unique`: on any finite set of distinct, strictly positive, normalized prices, any Walras-law excess demands are the sum of optimal net trades of as many consumers as goods. Each consumer has a continuous, concave, strictly monotone utility and a unique optimum at each price.

## Reading
Stage 296 produced continuous Afriat utilities, but their indifference sets have flat pieces, so demand at a price could be a set. Here the strict Afriat inequalities leave slack, and a small strictly concave penalty uses it up. The penalty vanishes exactly at the observed bundle, so demand becomes single-valued at every observed price without moving the observed choices. This is the finite-data form of "any Walras-law excess demand comes from well-behaved consumers with demand *functions*".

## Limits
- Only finitely many prices. Uniqueness holds on the budget sets of the observed prices; demand at other prices is not described.
- Utilities are concave, not strictly concave. Uniqueness comes from the penalty at the observed bundles, not from strict concavity everywhere.
- The continuum version (Mantel 1974, Debreu 1974) is not formalized.
