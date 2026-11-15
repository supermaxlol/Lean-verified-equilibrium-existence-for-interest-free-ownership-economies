# Stage 272 — Share claims are solvent in every state; fixed claims are not

Lean 4.35 / Mathlib, 6 audited declarations, all `[propext, Classical.choice, Quot.sound]`, no errors, no warnings.

Setting: output `Y s > 0`. A share claim pays `w * Y s`; a fixed claim pays `b` in every
state and leaves its issuer `a * Y s - b`.

- `share_solvent` — a positive share pays a positive amount in every state.
- `shares_exhaust` — share claims summing to one pay out exactly output.
- `default_iff` — the issuer is short exactly in the states with `Y s < b / a`.
- `fixed_claims_exceed` — if fixed claims total more than output in a state, some claim
  is not paid in full there.
- `leverage_amplifies` — for `y > y' > b > 0`, `y / y' < (y - b) / (y' - b)`.
- `share_ratio` — a share claim has the same ratio across states as output.

Limits: these are accounting identities and inequalities. They carry no behavioural or
welfare content on their own.
