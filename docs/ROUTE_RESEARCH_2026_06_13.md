# Route research — alggeo Jacobian challenge (2026-06-13)

Per the route-research-before-arc rule: candidate textbook routes BEFORE any
construction work, with the mathlib-support inventory they sit on. Citations
are section-level; **exact theorem/page numbers are TO-VERIFY on first read
of each source — never cite them from memory in a proof comment.**

## What the 9 holes actually force

- `genus` is not free-floating: hole 4 (`SmoothOfRelativeDimension (genus C)
  (Jacobian C).hom`) forces the honest `g`. The identity component of the
  Picard scheme has tangent space `T₀ J ≅ H¹(C, 𝒪_C)` (deformation theory),
  so any workable `genus` definition must be provably equal to
  `dim_k H¹(C, 𝒪_C)` — there is no cohomology-free dodge.
- Hole 9 (Albanese universal property) is, per the problem's own metadata,
  "the no-cheating clamp": it quantifies over ALL abelian varieties `A`
  (smooth + proper + `GrpObj` + geometrically irreducible), so `Jacobian`
  cannot be a degenerate placeholder.
- The comparator pins every statement; helpers must be inlined in the
  submission workspace (no external deps beyond the pinned mathlib).

## Mathlib support at the pin (`5450b53e5ddc`, inventoried 2026-06-13, 9065 modules)

**Present** (vocabulary layer — much of it Merten's):
`Over`-category + `GrpObj` group objects incl.
`AlgebraicGeometry/Group/{Smooth,Abelian}`; morphism properties `IsProper`,
`SmoothOfRelativeDimension`, `GeometricallyIrreducible` (+ the
`Geometrically/` family); `ProjectiveSpectrum` (incl. `Proper.lean`);
`AlgebraicGeometry/FunctionField.lean`; `Cover/*`, `Gluing*`,
`Morphisms/Descent`; abstract sites-level sheaf cohomology
(`CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}`).
140 paths under `AlgebraicGeometry/`.

**Absent** (construction layer — ALL of it is on us):
Picard functor/scheme; divisors on schemes/curves; Riemann–Roch; coherent
cohomology of schemes (finiteness, base change); Hilbert/Quot schemes;
symmetric powers of schemes; quotients by finite group actions; abelian-
variety theory (rigidity etc.); Albanese.

## Candidate routes

### Route A — Weil's construction via symmetric powers (classical)

Sources: Milne, *Jacobian Varieties* (in Cornell–Silverman eds., *Arithmetic
Geometry*, Springer 1986; free at jmilne.org/math/articles) — construction
§§2–7: symmetric powers `C^(d)` are smooth projective; for `d = g` the
Abel–Jacobi map `C^(g) → Pic^g` is birational; birational group law via
Riemann–Roch; extend to a group variety by the theorem on birational group
laws (also BLR, *Néron Models*, ch. 5). Serre, *Groupes algébriques et
corps de classes*, ch. V for the divisor/AJ formalism.

Needs: finite-group quotients of quasi-projective schemes (for `Sym^d C`),
curve Riemann–Roch, function-field/birational machinery, the group-law
extension theorem. Everything is 1-variable classical; no Hilbert schemes.

### Route B — FGA representability of Pic⁰ (the "real thing")

Sources: Kleiman, *The Picard Scheme* (FGA Explained, AMS Surveys 123,
2005, ch. 9) — representability for projective geometrically integral
schemes over a field; smoothness + dimension of `Pic⁰` for curves via
deformation theory. Prerequisites: Hilbert/Quot (FGA Explained ch. 5–7),
flattening stratification, cohomology-and-base-change (Mumford, *Abelian
Varieties* §5; Hartshorne III.12).

Needs: the deepest infrastructure stack, but the trunk is maximally
mathlib-PR-able and reusable. Strictly larger than Route A for this
challenge alone.

### Route C — hybrid (A's construction, functorial packaging)

Build via symmetric powers (A) but state `Pic⁰` functorially so hole 9
(Albanese) follows from functoriality + rigidity of abelian varieties
(Mumford AV §4: pointed maps of abelian varieties are homomorphisms;
factorization through AJ: Milne JV §6) instead of ad-hoc birational
arguments. Likely the target shape regardless of A-vs-B.

## Shared prerequisite = the calibration canary

**M1: coherent cohomology for curves.** `H⁰/H¹` of coherent sheaves on a
proper curve, finite-dimensional over `k`, computable by Čech on a
two-affine cover (a smooth projective curve minus a closed point is affine —
classical; verify the geometrically-irreducible-over-arbitrary-`k` form).
Every route consumes M1 (genus, RR, tangent space, smoothness-of-dim-g),
and it is the single best-calibrated probe of cost-per-classical-theorem in
mathlib's current AG idiom.

## Milestones (each gets a DONE WHEN before work starts)

| ID | Content | DONE WHEN |
|----|---------|-----------|
| M0 | Scaffold + CI + manifest | CI green on scaffold; `lake-manifest.json` committed |
| M1 | Čech coherent cohomology on curves + finiteness | `FiniteDimensional k (H¹ C 𝒪_C)` compiles sorry-free at the pin |
| M2 | Divisors + Riemann–Roch on curves | curve RR theorem sorry-free, genus = h¹(𝒪) |
| M3 | `Sym^d C` as a scheme, smooth | `SmoothOfRelativeDimension d` instance for `Sym^d C` |
| M4 | Construction decision A vs B (priced by M1–M3 actuals) + `Jacobian` def | hole 2 filled |
| M5 | Group law, proper, geom. irred., dim = g | holes 3–6 filled |
| M6 | AJ map + Albanese | holes 1, 7–9 filled; comparator pass |

## Go/no-go (decisive-regime check)

- **Decisive observable:** M1's actual cost (LOC + wall-clock + elaboration
  pain) at the pinned mathlib.
- **Regime where it discriminates:** if M1 lands ≤ ~5k LOC with sane
  elaboration, the arc is viable at subscription budget; if it blows far
  past that, STOP — the obstruction statement goes to the leap queue and
  M1 itself becomes a standalone mathlib-PR contribution instead.
- **Cost of the probe:** M1 itself (bounded; first chip ≈ Čech complex of a
  two-set affine cover).

## Risks / notes

- Kim Morrison (Zulip, 2026-06-09): "multiple groups are working on the
  Jacobian challenge privately." Market: 25% by July, 62% by September.
  Scooping is acceptable (results > recognition); the infrastructure is
  mathlib-PR material either way. Log, don't chase.
- char-p caveats: `h⁰(Ω¹) = h¹(𝒪) = g` holds for smooth proper curves in
  all characteristics (Serre duality), but route choices that flirt with
  `H¹` vs `Ω¹` definitions must check duality availability — mathlib has
  NO Serre duality; prefer `h¹(𝒪_C)` as the primitive.
- The challenge quantifies `C` over `Over (Spec (.of k))` with instance
  hypotheses — no rational point is assumed for the CONSTRUCTION (only
  `ofCurve` takes `P`). Route A's birational arguments classically use a
  rational point / work over `k̄` + descent; this is a real gap to price
  during M4 (Kleiman ch. 9 handles general `k` natively — a point for B).
