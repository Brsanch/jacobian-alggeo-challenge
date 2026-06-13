import Mathlib

/-!
# M1b-1 — the `R`-algebras → `R`-modules forgetful functor

The genus DONE WHEN needs the structure sheaf of the curve `C` (a scheme over
`Spec k`) as a presheaf valued in `ModuleCat k`, so that the Čech complex of
`Submission/CechModuleCat.lean` (`cechComplexMod`, generic in the preadditive
target) computes `H¹(C, 𝒪_C)` as a `k`-module.

Mathlib at this pin (`5450b53e5ddc`) has **no** off-the-shelf bridge for this:
there is no `forget₂ CommRingCat (ModuleCat k)` (the `k`-module structure on a
ring needs an `Algebra k`/ring map `k → R`, which is data, not a forgetful
functor), no `AlgebraCat` at this pin, and no `Under R ⥤ ModuleCat R` functor.
`AlgebraicGeometry.structurePresheafInModuleCat` exists only for the *affine*
`Spec R` with modules over `R` itself, not over a base field.

This module supplies the missing algebra-side primitive: the forgetful functor
from `R`-algebras (objects of `Under R`, i.e. ring maps `R ⟶ A`) to `R`-modules.
An object `A : Under R` is a ring map `A.hom : R ⟶ A.right`, which equips
`A.right` with the `R`-module structure `r • x = A.hom r * x`
(`RingHom.toModule`); a morphism `f` over `R` is `R`-linear because it commutes
with the structure maps (`Under.w`). This is mathlib-PR-shaped infrastructure
(its own M1b milestone, per the mathlib-first gate).

The geometric step M1b-2 (the structure sheaf of `C` as a presheaf valued in
`Under (CommRingCat.of k)`, via the structure morphism `C.hom`) then composes
with this functor to land in `ModuleCat k`; M1b-3 specializes `cechH`.

No `sorry`, no `axiom`, no `ω` binders (Lean 4.30 reserves `ω`).
-/

open CategoryTheory

namespace JacobianAlggeo

universe u

/-- The forgetful functor from `R`-algebras to `R`-modules.

An object of `Under R` is a ring map `A.hom : R ⟶ A.right`; this functor sends it
to the underlying `R`-module of `A.right`, where the `R`-action is `r • x =
A.hom r * x` (`RingHom.toModule A.hom.hom`). A morphism `f : A ⟶ B` in `Under R`
is a ring map `f.right` over `R`; it is `R`-linear because `Under.w f` says it
commutes with the two structure maps, so `f.right (r • x) = f.right (A.hom r * x)
= B.hom r * f.right x = r • f.right x`.

This is the `R`-algebras → `R`-modules forgetful functor absent from mathlib at
the pin (no `forget₂ CommRingCat (ModuleCat R)`, no `AlgebraCat`). It is the
bridge that turns the (`CommRingCat`-valued) structure sheaf of a `k`-scheme,
re-expressed over the base via the structure morphism, into the `ModuleCat k`-
valued presheaf the Čech complex `cechComplexMod` consumes. -/
noncomputable def underToModuleCat (R : CommRingCat.{u}) : Under R ⥤ ModuleCat.{u} R where
  obj A :=
    letI := A.hom.hom.toModule
    ModuleCat.of R A.right
  map {A B} f :=
    letI := A.hom.hom.toModule
    letI := B.hom.hom.toModule
    ModuleCat.ofHom
      { toFun := f.right.hom
        map_add' := map_add f.right.hom
        map_smul' := fun r x => by
          have h : f.right.hom (A.hom.hom r) = B.hom.hom r := by
            have hw := Under.w f
            rw [← hw]; rfl
          show f.right.hom (A.hom.hom r * x) = B.hom.hom r * f.right.hom x
          rw [map_mul, h] }
  map_id A := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

end JacobianAlggeo
