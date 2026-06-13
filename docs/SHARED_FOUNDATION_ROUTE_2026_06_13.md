# Shared-foundation route — what BOTH Jacobian routes need (2026-06-13)

**Decision context.** The A-vs-B route leap (Weil/`Sym^d` vs FGA/`Pic⁰`,
`noethersolve/docs/LEAP_QUEUE.md §4`) was **deferred**: build the foundation BOTH
routes share first, then revisit A-vs-B once it exists and the trade-off is concrete.
This doc is the dependency map of that shared foundation, with the compile-verified
present/absent inventory at the pin `5450b53e5ddc` (warm cache, 2026-06-13) and the
ordered brick sequence. It is the architecture for "build the shared foundation first".

## Why these are *shared* (route-independent)

- **Line bundles / Picard.** Route B literally *represents* `Pic⁰ C` (the Jacobian IS
  `Pic⁰`). Route A needs invertible sheaves for **ample/very-ample ⇒ projective**
  (P5: `Sym^d C` projective) and for the embedding behind P3.
- **Coherent cohomology finiteness (Serre) + Riemann–Roch.** Route A needs curve RR
  for the birational group law and `genus = h¹`. Route B needs
  cohomology-and-base-change (Mumford AV §5). Both run through the SAME cohomology stack
  Tower A built Segments 1–2 of.
- **Projective morphisms / ample.** Route A directly (P5). Route B uses projectivity of
  Quot/Hilbert pieces.

So the shared foundation is two parallel stacks — **(I) the module/line-bundle/ample
stack** and **(II) the cohomology→Serre→RR stack** — meeting at "ample + cohomology ⇒
projective + RR".

## Present / absent inventory (compile-verified at pin, warm cache)

### Stack I — sheaves of modules → line bundles → ample → projective
| Layer | Statement | At pin | Note |
|---|---|---|---|
| I.0 | `PresheafOfModules R` monoidal (tensor) | **✓** | `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` |
| I.0 | `PresheafOfModules.sheafification` + adjunction; `SheafOfModules` abelian, colimits, quasicoherent | **✓** | `…/Sheaf/{Sheafification,Abelian,Colimits,Quasicoherent}.lean` |
| I.0 | `CategoryTheory.Localization.Monoidal.*` (transport monoidal thru a localization) | **✓** | `CategoryTheory/Localization/Monoidal/{Basic,Functor,Braided}.lean` |
| **I.1** | **`MonoidalCategory (SheafOfModules R)`** (sheafify the presheaf tensor) | **✗** | `Sheaf/` has NO `Monoidal.lean`. **= bottom brick** (transport I.0 monoidal thru the sheafification localization). |
| I.2 | **Invertible sheaf** = ⊗-invertible object of `SheafOfModules`; `Pic X` = its iso-class group | **✗** | no `LocallyFree`/invertible-object/`Picard` for schemes (only Weierstrass-specific); needs I.1 + categorical "invertible objects of a monoidal cat" (also absent — only `Grp_`/invertible-*morphisms*). |
| I.3 | `Proj ℬ` Serre twisting sheaf `𝒪(n)`; `𝒪(1)` ample | **✗** | `Proj ℬ` exists (`ProjectiveSpectrum/`) but NO twisting sheaf / `𝒪(n)`. |
| I.4 | **ample / very-ample invertible sheaf**; closed immersion into `ℙⁿ_S` | **✗** | only `AmpleSet` (convex-geometry h-principle, unrelated). |
| I.5 | **projective / quasi-projective morphism** of schemes | **✗** | none. (P5 not even *statable* until here — Tower-B leaf-obstruction.) |

### Stack II — coherent cohomology → Serre finiteness → Riemann–Roch
| Layer | Statement | At pin | Note |
|---|---|---|---|
| II.0 | `Hⁿ`/`H¹(C,𝒪_C)` valued in `ModuleCat k` (Segments 1–2) | **✓ (built)** | `Submission/{SheafCohomologyModuleCat,StructureSheafCohomology}.lean`; `ModuleCat.finite_ext` (Ext of f.g. modules is f.g.) present. |
| **II.1** | **Serre finiteness** `FiniteDimensional k (H¹ C)` = sheaf-`Ext`↔module-`Ext` bridge (derived↔Čech / proper-pushforward) | **✗** | no comparison/Leray/acyclic-cover; the 2-affine-cover Čech route (M1b) also needs "curve − point is affine" (Serre's criterion, absent). The deep wall (Wall 1). |
| II.2 | curve **Riemann–Roch**; `genus = h¹(𝒪)` | **✗** | needs II.1 + divisors. |

### Stack III — regular-local / smooth (Tower-A Wall 2; NOT shared-critical, but built)
- `regular local ⇒ domain` (any dim, Stacks 00NP) + cotangent/embedding-dim drop — **✓ built**
  (`Submission/Cohomology/RegularLocalDomainGeneral.lean`, `main` @ `5d3a8ed`).
- `smooth ⇒ regular local` — **✗**, bottoms out in the finite-type-over-field dimension
  formula (`dim=trdeg`, absent) + the residue-field cotangent sequence
  `finrank_κ(𝔪/𝔪²)=rel dim` (`StandardSmoothCotangent` gives `rank_S Ω`, a different
  cotangent). Not on any hole's critical path (genus `def` has no required equation).

## Ordered brick sequence (build the shared foundation)

**Bottom brick I.1 `MonoidalCategory (SheafOfModules R)` — SCAFFOLD DONE + REDUCED**
(`Submission/Cohomology/SheafOfModulesMonoidal.lean`, `main` @ `fa4f350`, green/axiom-clean/
vacuity-0). Transported `PresheafOfModules` monoidal (I.0) through the sheafification
localization (`CategoryTheory.Localization.Monoidal`, defeq type-synonym transport). The
predicted risk landed exactly: the instance is **conditional on `[W.IsMonoidal]`** (mathlib's
`MorphismProperty.IsMonoidal`, mirroring mathlib's own `Sheaf.monoidalCategory`). So I.1 is now
*reduced to one classical theorem*:

> **I.1a (the genuine remaining content, = next concrete brick):** `(sheafificationW J R₀).IsMonoidal`
> = **"sheafification of presheaves of modules commutes with the tensor product"** (Stacks 17.16 /
> EGA 0_I.4.1) = its two whiskering fields (`tensorLeft X ⋙ sheafification` and `tensorRight Y ⋙
> sheafification` invert `W`). Absent at pin (no `MonoidalClosed (PresheafOfModules)`,
> no sheafification-preserves-tensor; `IsLeftAdjoint` insufficient). Multi-hundred-LOC sub-arc:
> **build `MonoidalClosed (PresheafOfModules (R₀ ⋙ forget₂ …))`** (then the internal-hom proof
> that gives `J.W.whiskerLeft` in `Sites/Monoidal.lean` ports), **or** develop the sheaf tensor
> directly and identify it with the localized tensor. Discharging I.1a makes I.1 unconditional and
> unblocks I.2.

Once I.1a lands, in dependency order: I.2 invertible sheaves + `Pic X` → (fork point: A-vs-B can be
revisited here, since `Pic` now exists) → I.3 Proj `𝒪(n)` / II.1 Serre finiteness (parallel)
→ I.4 ample / II.2 RR → I.5 projective morphisms. Stack II (Serre finiteness) is the harder
of the two and gates RR + cohomology-and-base-change for both routes.

## Honest scope

This is a multi-month EGA-III/IV + FGA build; the pin has almost none of the AG
superstructure. No single brick closes a hole. The value of this doc: it turns the
"multi-month foundation" into an ordered sequence of individually-buildable bricks, and
identifies the bottom one (I.1) as the concrete next target. The A-vs-B leap is best
revisited at the I.2 fork (once `Pic X` exists). Sources: this session's compile-probes;
`OPEN.md`, `PARALLEL_PLAN.md`, `LEAP_QUEUE.md §4–5`.
