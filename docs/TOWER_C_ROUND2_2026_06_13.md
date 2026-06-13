# Tower C — round 2: hole-4 smoothness half + hole-9 uniqueness half (2026-06-13)

Branch `tower/abelian-variety-r2` off integrated `main` (`b6b2062`).  All Lean
below is sorry-free, axiom-clean (`#print axioms` = `{propext, Classical.choice,
Quot.sound}`), vacuity-lint 0, CI-green.  Files under `Submission/AbelianVariety/`.

## Delivered (two ready-to-wire bricks)

### `SmoothGroupScheme.lean` — `smooth_of_grpObj` (hole 4's **smoothness half**, CLOSED as a theorem)
- **`AlgebraicGeometry.smooth_of_grpObj`**: *a geometrically reduced, locally-of-finite-
  presentation group scheme over **any** field `k` is smooth.*
- Combines mathlib's `smooth_of_grpObj_of_isAlgClosed` (over `k̄`) with **round 1's
  faithfully-flat descent of smoothness** (`SmoothFaithfullyFlatDescent.lean`), applied
  to `Spec k̄ → Spec k` (`= Surjective ⊓ Flat ⊓ QuasiCompact`, the descent class).  This
  is the "one-line application" round 1 flagged as the remaining step — now a standalone
  theorem.
- **Wiring for hole 4**: the Jacobian is a proper, geometrically integral (⟹ geometrically
  reduced, ⟹ lfp via proper) group scheme, so `smooth_of_grpObj` gives `Smooth (Jacobian
  C).hom` once Tower B supplies `Jacobian C` with its `GrpObj`.  CI run `27476048455` ✓.

### `AlbaneseUniqueness.lean` — hole 9's **uniqueness half** (the `∃!`'s `!`)
Three genuine, general pieces, each discharged on arbitrary data:
- **`hom_ext_of_isDominant`**: *a morphism of `k`-schemes is determined by its restriction
  to a (topologically) dominant subscheme* (source reduced, target separated/proper).  The
  uniqueness engine, via mathlib's `ext_of_isDominant_of_isSeparated`.
- **`postcompHom`**: *postcomposition by a homomorphism of group objects is a monoid
  homomorphism `Hom(W, J) →* Hom(W, A)`* (`MonObj.one_comp` / `MonObj.mul_comp`); it sends
  a finite sum `∏ᵢ aᵢ` to `∏ᵢ (aᵢ ≫ g)`.
- **`albanese_uniqueness`**: assembles them — if the iterated sums of the Abel–Jacobi map
  `φ` generate `J` (a dominant sum-morphism `∏ᵢ (cᵢ ≫ φ)`, the geometric **generation**
  input), then two *homomorphisms* `g₁ g₂ : J ⟶ A` agreeing after `φ` coincide.
- **`albanese_uniqueness_of_pointed_factorization`** — *the full hole-9 `∃!` uniqueness, for
  arbitrary morphisms.*  The hole's `∃! g, f = ofCurve P ≫ g` ranges over **all** morphisms
  `g`, not only homomorphisms.  But every `g` satisfying the factorization is automatically
  *pointed* (`η[J] ≫ g = P ≫ f = η[A]`, from `comp_ofCurve` (hole 8) + `hf`), hence a
  homomorphism by **round-1 Mumford rigidity** (`isMonHom_of_pointed_of_geometricallyIntegral`);
  `albanese_uniqueness` then closes it.  So this single theorem is the entire uniqueness side
  of hole 9.
- **Wiring for hole 9**: the integrator instantiates `J = Jacobian C`, `φ = ofCurve P`,
  `W = Cⁿ`, `cᵢ =` projections, and supplies the one remaining input — `IsDominant
  (∏ᵢ projᵢ ≫ ofCurve P)` from Tower B (Jacobi inversion / Riemann–Roch: the curve generates
  `Pic⁰`) — plus `hφ = comp_ofCurve` (hole 8).  Everything else is discharged here.

## Obstruction (stated at maximum resolution, NOT ground through)

### Hole 4's **dimension half** — `relative dimension = genus` — is a multi-day mathlib wall
Hole 4 is the single instance `SmoothOfRelativeDimension (genus C) (Jacobian C).hom`.
Smoothness is delivered; the remaining content is **relative dimension `= genus`**.  This is
blocked **twice over**:

1. **Tower-B / cohomology block**: over `k̄`, `rel.dim (Jacobian) = dim T_e(Pic⁰) = dim_k
   H¹(C, 𝒪_C) = g`.  The identification `T_e Pic⁰ ≅ H¹(C,𝒪)` is deformation theory of the
   Picard functor — Tower B's construction, not available against an abstract interface.

2. **A genuine mathlib-infrastructure wall on the descent itself.**  The natural Tower-C
   contribution mirrors round 1: *faithfully-flat descent of `SmoothOfRelativeDimension n`*
   (base-change `g` over `k̄` down to `k`).  At the pin this is **not** a one-session brick:
   - `SmoothOfRelativeDimension n` has `HasRingHomProperty (Locally (IsStandardSmoothOf
     RelativeDimension n))`.  Round 1's descent of plain `Smooth` used the clean module
     property `RingHom.Smooth`; here the ring-hom property is wrapped in **`Locally`**, and
     **mathlib has no `Locally`-codescent lemma** (`CodescendsAlong (Locally P) Q` from
     `CodescendsAlong P Q`).  Building it is a substantial PR (it interacts localization
     covers with the base change).
   - The reduction `IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = n`
     (`iff_of_isStandardSmooth`) needs a **global** `IsStandardSmooth R S`, but smoothness
     gives only *locally* standard smooth ⟹ `Ω[S⁄R]` is only **locally free**.  So
     relative dimension is a **locally-constant** invariant (`rankAtStalk`), and the
     cardinal `Module.rank_baseChange` (which needs `Module.Free`) does **not** apply.
   - The `rankAtStalk` route would sidestep freeness (`rankAtStalk_baseChange` exists), but
     there is **no scheme-level sheaf of differentials `Ω_{X/Y}` at the pin** and **no
     cotangent-`rankAtStalk` characterization of `SmoothOfRelativeDimension n`** — that
     whole layer would have to be built first.

   **Precise missing lemma (the leap):** *`SmoothOfRelativeDimension n` codescends along a
   faithfully-flat base change* — equivalently, `CodescendsAlong (Locally
   (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat`.  Entry points:
   `RingHom.Smooth.codescendsAlong_faithfullyFlat` (round 1, the `n`-free analogue),
   `IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`,
   `KaehlerDifferential.tensorKaehlerEquiv` (Ω base change), `Module.rank_baseChange` /
   `rankAtStalk_baseChange` (rank preservation), `Mathlib/RingTheory/RingHom/Locally.lean`
   (the `Locally` API, which needs a codescent companion).

### Hole 9's **existence half** — the factorization — remains theorem-of-the-cube-grade
Building `g : Jacobian C ⟶ A` from a pointed `f : C ⟶ A` (Milne JV §6) needs: the
rational map `Pic⁰ ⤏ A` from the symmetric-power/divisor description, its extension to a
morphism (Weil's extension theorem: a rational map from a smooth variety to an abelian
variety is everywhere defined — theorem-of-the-cube lineage), and `Cᵍ ⤏ Pic⁰` birational
(Riemann–Roch).  All of this is Tower-B/FGA-grade with zero mathlib foundation; the
uniqueness brick above is the reachable Tower-C half.

## Status of the brief's three next bricks
| Brief brick | This round |
|---|---|
| 1. hole 9 — `exists_unique_ofCurve_comp` | **Full uniqueness side DELIVERED** (`AlbaneseUniqueness.lean`, `albanese_uniqueness_of_pointed_factorization` — handles *bare* morphisms via rigidity); existence half = theorem-of-the-cube wall (stated). |
| 2. hole 4 — `smoothOfRelativeDimension_genus` | **Smoothness half DELIVERED** (`SmoothGroupScheme.lean`); dimension half = `Locally`-codescent + Tower-B wall (stated above). |
| 3. hole 3's hom structure | Round-1 rigidity/hom corollaries already cover it; the `GrpObj (Jacobian C)` *construction* is Tower B's. |
