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

## M1 API actuals + encoding decision (recorded 2026-06-13, loop run #1)

Pre-M1 grep prerequisite done via GitHub at the pin `5450b53e5ddc` (local
mathlib not yet checked out — bootstrap build still running). Path-level
inventory above is now refined to declaration-level for the M1-relevant
modules:

**`CategoryTheory/Sites/SheafCohomology/Basic.lean`** — abstract sheaf
cohomology `Sheaf.H F n : Type` defined as `Ext`-groups from the constant
abelian sheaf `ℤ`. Coefficients live in **`AddCommGrpCat` (abelian groups)**,
NOT in `ModuleCat k`. Also: `cohomologyFunctor`, `cohomologyPresheaf`,
`H' F n X`, `subsingleton_H_of_isZero`. ⇒ `Sheaf.H` alone gives `H¹ C 𝒪_C`
only as an abelian group, with **no k-module structure** — so it cannot
directly satisfy the M1 DONE WHEN `FiniteDimensional k (H¹ C 𝒪_C)`.

**`CategoryTheory/Sites/SheafCohomology/Cech.lean`** — `cechComplexFunctor :
(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` for a family `U : ι → C` (C has finite
products), valid for **any preadditive `A`**. ⇒ instantiating `A := ModuleCat
k` makes the Čech cochain complex — and hence its homology `H¹` — a **k-module
by construction**. No `Sheaf.H`↔Čech comparison and no `H⁰ ≅ Γ` lemma exist
in the file; both are on us (needed only for genus/RR *correctness*, a later
milestone, not for the M1 DONE WHEN as literally typed).

**`AlgebraicGeometry/Sites/SmallAffineZariski.lean`** — `Scheme.AffineZariskiSite
X := {U : X.Opens // IsAffineOpen U}`; `grothendieckTopology`; `sheafEquiv :
Sheaf (gT X) A ≌ TopCat.Sheaf A X`. ⇒ the scheme↔site bridge for getting
`𝒪_C` (and coherent sheaves) in as Čech input is present.

**`AlgebraicGeometry/Modules/{Presheaf,Sheaf,Tilde}.lean`** — sheaves of
modules on schemes + the `M~` (Tilde) construction on affine schemes; present
but not wired into the cohomology file.

**Absent (unchanged):** coherent finiteness / Serre finiteness, curve RR,
Picard. The deep core of M1 (`FiniteDimensional`) is Serre finiteness — no
short glue.

### Encoding DECISION (resolves the k-module fork)

Define `H¹ C 𝒪_C` as the **degree-1 homology of the two-affine-cover Čech
complex taken in `ModuleCat k`** (`cechComplexFunctor` with `A := ModuleCat
k`), NOT via the abelian-group `Sheaf.H`. This is exactly the route doc's
"computable by Čech on a two-affine cover," and it makes `FiniteDimensional k
(H¹ C 𝒪_C)` type-correct by construction. The Čech↔derived comparison is
deferred to its own milestone (only genus/RR need it).

### M1 decomposition (each its own gated chip)

- **M1a** — Define the two-object Čech complex of `𝒪_C` in `ModuleCat k` via
  `cechComplexFunctor` on a `Fin 2`-indexed affine cover, and define
  `H1 C 𝒪_C := (that complex).homology 1`. Substantive lemma (gate 5):
  identify Čech `H⁰` with the equalizer of the two restriction maps (= global
  sections of the cover), sorry-free. *First, gate-6 check: confirm mathlib
  has no ready `H⁰ ≅ Γ` / equalizer lemma for `cechComplexFunctor` — grep the
  warm local tree.* DONE WHEN: `H1 C 𝒪_C : ModuleCat k` + the H⁰/equalizer
  lemma compile sorry-free at the pin.
- **M1b** — The geometric input: the two-affine cover exists for a smooth
  proper curve (curve minus a closed point is affine; verify the
  geometrically-irreducible-over-arbitrary-`k` form), with its restriction
  and intersection-section maps. DONE WHEN: the cover + maps feeding M1a are
  constructed from the curve's instances, sorry-free.
- **M1c** — Finiteness (the deep core = Serre finiteness for the proper
  curve): `FiniteDimensional k (H1 C 𝒪_C)`. This is the M1 DONE WHEN and the
  go/no-go datum.

### Environment flags (loop run #1, 2026-06-13)

- Local mathlib package dir holds only `.git` — source not yet checked out;
  the bootstrap `lake build` (pid 59568) was still running at ~1h55m. So the
  warm-cache local grep / `lake env lean` iteration is NOT yet available; CI
  on a branch is the working gate (M0 CI runs were green in 3–4 min, so the
  CI-side mathlib cache is warm and fast).
- ⚠️ **Toolchain mismatch:** the running bootstrap (pid 59568) and its child
  `lean` (88311) are `leanprover--lean4---v4.29.0`, but `lean-toolchain`
  pins `v4.30.0-rc2`. Next run: verify the bootstrap is actually building the
  pinned toolchain (`elan show` in-repo, check `.lake` olean target) before
  trusting any local build; if it built 4.29.0 oleans, they are unusable and
  the bootstrap must be re-launched under 4.30.0-rc2.
