# Open items — jacobian-alggeo-challenge

> **Before any new Lean work: read `CHIP_GATES.md` (repo root)** — vacuity
> lint gate (mechanical, baseline-ratcheted) + the anti-paraphrase gates —
> and `DEVELOPMENT.md` (panic-safe build rules, eval submission mechanics).

## Authoritative current state (2026-06-13: scaffold, all 9 holes OPEN)

Target: the official lean-eval problem
[`jacobian_challenge_alggeo`](https://lean-lang.org/eval/problems/jacobian_challenge_alggeo/)
(Christian Merten's algebraic-geometry analogue of the Buzzard Jacobian
challenge; the diffgeo variant was solved by rkirov/jacobian-claude
2026-06-11). DONE WHEN (arc): a submission accepted by the lean-eval
comparator and audited by the maintainer. Status board: Kim Morrison's
[Manifold market](https://manifold.markets/kimem/when-will-the-jacobian-challenge-be).

| # | Hole | Kind | Status |
|---|------|------|--------|
| 1 | `genus` | def | OPEN |
| 2 | `Jacobian` | def | OPEN |
| 3 | `Jacobian.instGrpObj` | def | OPEN |
| 4 | `Jacobian.smoothOfRelativeDimension_genus` | theorem | OPEN |
| 5 | `Jacobian.instIsProper` | theorem | OPEN |
| 6 | `Jacobian.instGeometricallyIrreducible` | theorem | OPEN |
| 7 | `Jacobian.ofCurve` | def | OPEN |
| 8 | `Jacobian.comp_ofCurve` | theorem | OPEN |
| 9 | `Jacobian.exists_unique_ofCurve_comp` | theorem | OPEN |

Current phase: **route research** — see
`docs/ROUTE_RESEARCH_2026_06_13.md` (mathlib-support inventory at the pin +
candidate construction routes + phase-1 DONE WHEN). No construction work
starts before that doc's go/no-go check is met.

## Rules inherited from the diffgeo challenge post-mortems

- A "named hypothesis" introduced without a same-session discharge on
  arbitrary data is a renamed sorry (paraphrase gate, `CHIP_GATES.md`).
- Single bar: a hole counts CLOSED only when the declaration compiles
  sorry-free/axiom-free against the pinned mathlib AND its statement is
  byte-compatible with `Challenge.lean` (the comparator is the judge —
  do not invent softer tiers).
- Per-item status lives HERE, refreshed every session; prose docs and
  docstrings are not trustworthy for open/closed status.
