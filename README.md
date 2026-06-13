# jacobian-alggeo-challenge

Private working repo for the **algebraic-geometry Jacobian challenge**
([lean-eval `jacobian_challenge_alggeo`](https://lean-lang.org/eval/problems/jacobian_challenge_alggeo/),
by Christian Merten): construct the Jacobian of a smooth proper curve over a
field as a group scheme — smooth of relative dimension g, proper,
geometrically irreducible — with the Abel–Jacobi map and the Albanese
universal property. 9 holes; statements fixed by `Challenge.lean`
(verbatim from the benchmark; Apache-2.0, © Christian Merten).

Pin: Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc` (matches the eval workspace).

- `OPEN.md` — authoritative per-hole status
- `CHIP_GATES.md` — anti-paraphrase gates + vacuity-lint merge gate
- `DEVELOPMENT.md` — panic-safe build rules + eval submission mechanics
- `docs/ROUTE_RESEARCH_2026_06_13.md` — routes, mathlib inventory, milestones
- `NEXT_SESSION.md` — entry protocol + DONE WHEN

Setup carried over from the solved diffgeo variant
([jacobian-lean-challenge](https://github.com/Brsanch/jacobian-lean-challenge),
frozen v1.0.0; external completion by
[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)).
