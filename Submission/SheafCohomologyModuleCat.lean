import Mathlib

/-!
# Segment 1 — sheaf cohomology valued in `ModuleCat k` (derived-functor route)

This is build-target step 1 of the coherent-cohomology stack (`NEXT_SESSION.md`):
degree-`n` sheaf cohomology `H J k n F` of a `ModuleCat k`-valued sheaf `F` on a
site `(C, J)`, defined as the `Ext`-groups from the constant sheaf with value `k`,
**taken in the category `Sheaf J (ModuleCat k)`**. The point of landing in
`ModuleCat k` rather than `AddCommGrpCat` (mathlib's `Sheaf.H`) is that the
cohomology then carries a `k`-module structure, so `FiniteDimensional k (H J k 1 F)`
is type-correct — the property the genus (`Challenge.lean` hole 1) ultimately needs.

## What is already in mathlib at the pin (Gate-6 survey, 2026-06-13)

The earlier route notes feared the "first real content" was building
*Grothendieck-abelian-of-sheaves ⇒ `HasExt`* from scratch. The warm-cache survey
found that is **already in mathlib** (`5450b53e5ddc`); the present file only
assembles it:

* `CategoryTheory.Sheaf` (in `Abelian/GrothendieckAxioms/Sheaf.lean`):
  `Sheaf J A` is `IsGrothendieckAbelian` when `A` is, given `[HasSheafify J A]`
  and a small site.
* `IsGrothendieckAbelian.hasExt` (in `Abelian/GrothendieckCategory/HasExt.lean`):
  a Grothendieck-abelian category `HasExt`. ⇒ `HasExt (Sheaf J (ModuleCat k))`
  is automatic.
* `Abelian.Ext.instModule` (in `DerivedCategory/Ext/Linear.lean`): in a
  `k`-linear abelian category, `Ext X Y n` is a `k`-module. And
  `Sheaf J (ModuleCat k)` *is* `k`-linear (the instance resolves), so
  `H J k n F` is a `k`-module with no extra work.
* `Sheaf.Γ` / `constantSheafΓAdj` (in `Sites/GlobalSections.lean`): the global
  sections functor and its adjunction with the constant sheaf functor — the
  ingredients for `H⁰ ≅ Γ`.

## The genuinely new content here

`Sheaf.H` (mathlib) lists `H⁰ ≅ Γ` as a TODO and does not prove it. We prove the
`ModuleCat k`-valued analogue, `HZeroAddEquivΓ : H J k 0 F ≃+ (Sheaf.Γ J _).obj F`
(degree-`0` sheaf cohomology is the global sections, as abelian groups). The
single missing mathlib lemma it needs — additivity of the constant-presheaf
functor `Functor.const Cᵒᵖ` — is supplied here (`Functor.const_additive`); the
rest is `Adjunction.homAddEquiv` + `Adjunction.right_adjoint_additive` +
`Ext.linearEquiv₀` + the `ModuleCat`-hom-from-`k` identification.

No `sorry`, no `axiom`, no `ω` binders (Lean 4.30 reserves `ω`).

## Hypotheses (mathlib idiom, not a named sorry)

`[HasSheafify J (ModuleCat k)]` is carried as an instance hypothesis exactly as
mathlib's own `Sheaf.H` carries `[HasSheafify J AddCommGrpCat]`: it is the genuine
typeclass under which sheaf cohomology is defined, discharged at instantiation
time (for the curve's actual site), not deferred content.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace JacobianAlggeo

universe w v u

/-- Additivity of the constant-presheaf functor `Functor.const Cᵒᵖ : A ⥤ (Cᵒᵖ ⥤ A)`
for a preadditive target `A`. (Missing from mathlib at the pin; needed so that the
constant *sheaf* functor — `Functor.const Cᵒᵖ ⋙ presheafToSheaf` — is additive, hence
that the constant-sheaf/global-sections adjunction has an additive hom-equivalence.) -/
instance Functor.const_additive {C : Type v} [Category.{v} C]
    {A : Type u} [Category.{w} A] [Preadditive A] :
    (Functor.const Cᵒᵖ : A ⥤ (Cᵒᵖ ⥤ A)).Additive where
  map_add := by intro X Y f g; ext j; rfl

section

variable {C : Type v} [SmallCategory.{v} C] (J : GrothendieckTopology C)
variable (k : Type v) [Field k] [HasSheafify J (ModuleCat.{v} k)]

/-- The coefficient sheaf for `k`-valued cohomology: the constant sheaf with value
`k`, viewed as the rank-one free `k`-module `ModuleCat.of k k`. Sheaf cohomology with
`k`-coefficients is `Ext` out of this object (mirroring `Sheaf.H`, where the
coefficient object is the constant sheaf `ℤ`). -/
noncomputable def coeffSheaf : Sheaf J (ModuleCat.{v} k) :=
  (constantSheaf J (ModuleCat.{v} k)).obj (ModuleCat.of k k)

/-- The constant sheaf functor into `ModuleCat k`-sheaves is additive: it is
`Functor.const Cᵒᵖ ⋙ presheafToSheaf`, both factors additive. -/
instance : (constantSheaf J (ModuleCat.{v} k)).Additive := by
  unfold constantSheaf; infer_instance

/-- **Degree-`n` sheaf cohomology valued in `ModuleCat k`.** For a `ModuleCat k`-valued
sheaf `F` on the site `(C, J)`, this is `Ext^n` from the constant sheaf `k` to `F`,
computed in the Grothendieck-abelian, `k`-linear category `Sheaf J (ModuleCat k)`.

It is a bare type carrying the `k`-module structure that `Ext` has in any `k`-linear
abelian category (`Abelian.Ext.instModule`), so `Module k (H J k n F)` and
`FiniteDimensional k (H J k n F)` are type-correct — `H J k 1 F` is the object whose
`k`-dimension the genus is built from. `HasExt (Sheaf J (ModuleCat k))` resolves
automatically (Grothendieck abelian). -/
noncomputable abbrev H (n : ℕ) (F : Sheaf J (ModuleCat.{v} k)) : Type v :=
  Ext (coeffSheaf J k) F n

noncomputable example (n : ℕ) (F : Sheaf J (ModuleCat.{v} k)) :
    Module k (H J k n F) := inferInstance

/-- **Degree-`0` sheaf cohomology is the global sections** (as abelian groups):
`H J k 0 F ≃+ Γ(F)`. This is the `ModuleCat k`-valued analogue of the `H⁰ ≅ Γ`
isomorphism that mathlib's `Sheaf.H` only lists as a TODO.

Construction: `Ext^0 ≃ Hom` (`Ext.linearEquiv₀`), then the constant-sheaf/global-
sections adjunction `Adjunction.homAddEquiv` (additive because the constant sheaf
functor is — see the instance above), then `Hom_{ModuleCat k}(k, M) ≅ M`
(`ModuleCat.homLinearEquiv` ▸ `LinearMap.ringLmapEquivSelf`). -/
noncomputable def HZeroAddEquivΓ (F : Sheaf J (ModuleCat.{v} k)) :
    H J k 0 F ≃+ (Sheaf.Γ J (ModuleCat.{v} k)).obj F :=
  (Abelian.Ext.linearEquiv₀ (R := k)).toAddEquiv.trans <|
    ((constantSheafΓAdj J (ModuleCat.{v} k)).homAddEquiv (ModuleCat.of k k) F).trans <|
      (ModuleCat.homLinearEquiv.trans
        (LinearMap.ringLmapEquivSelf k k ((Sheaf.Γ J (ModuleCat.{v} k)).obj F))).toAddEquiv

end

end JacobianAlggeo
