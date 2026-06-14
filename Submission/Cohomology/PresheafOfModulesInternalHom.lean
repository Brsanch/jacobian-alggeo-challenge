import Mathlib
import Submission.Cohomology.SheafOfModulesMonoidal

/-!
# Internal hom of presheaves of modules, and the sheafification localizer as a Bousfield class

This file builds towards discharging the one undischarged hypothesis of
`SheafOfModules.monoidalCategory` (`Submission/Cohomology/SheafOfModulesMonoidal.lean`),
namely `(sheafificationW J R₀).IsMonoidal` — the classical theorem "sheafification of
presheaves of modules commutes with the tensor product" (Stacks 17.16 / EGA 0_I.4.1).

The proof mirrors mathlib's own `CategoryTheory.GrothendieckTopology.W.monoidal`
(`Mathlib/CategoryTheory/Sites/Monoidal.lean`) for presheaves valued in a braided closed
category, which proves `whiskerLeft` (`W g ⟹ W (F ◁ g)`) using:
1. the characterization of `W` as orthogonality to the *local objects* (sheaves), and
2. the closed structure: `Hom(F ⊗ G, H) ≅ Hom(G, [F,H])` with `[F,H]` a sheaf when `H` is.

For presheaves of *modules* over a *varying* commutative ring presheaf this needs the
internal hom of presheaves of modules, which mathlib does not have (it only has the
fixed-ring `ModuleCat/Monoidal/Closed.lean`, and the `Enriched.FunctorCategory` machinery
behind `Sites/Monoidal.lean` is for constant-enrichment plain functor categories). We build
it here.

## Piece (I): `sheafificationW` is a Bousfield local class

`sheafificationW J R₀` is, by definition, `J.W.inverseImage (toPresheaf …)`. Mathlib shows
(`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`) that this equals
the class of morphisms inverted by the sheafification functor
`L := PresheafOfModules.sheafification α : PresheafOfModules R₀' ⥤ SheafOfModules R`. Since
`L` is a *reflective* localization — its right adjoint
`F := SheafOfModules.forget R ⋙ restrictScalars α` is fully faithful
(`PresheafOfModules.sheafificationAdjunction`, with `IsIso counit`) — the left Bousfield
machinery (`ObjectProperty.isLocal_eq_inverseImage_isomorphisms`) identifies this class with
`ObjectProperty.isLocal (· ∈ Set.range F.obj)`: the morphisms `g` such that precomposition
with `g` is a bijection into every object that is (the restriction of) a sheaf of modules.

This is the form used in the `whiskerLeft` argument: to show `W (F ◁ g)` we will check
orthogonality against the local objects, which are exactly the (restrictions of) sheaves of
modules, against which the internal hom `[F, -]` lands (its sheaf-preservation, piece III).

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory Opposite

namespace JacobianAlggeo

universe u v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The fully-faithful right adjoint of the sheafification of presheaves of modules:
`SheafOfModules.forget R ⋙ restrictScalars α : SheafOfModules R ⥤ PresheafOfModules R₀'`.
Its essential image is the class of *local objects* (restrictions of sheaves of modules);
`sheafificationW` is orthogonality to it (`sheafificationW_eq_isLocal`). -/
noncomputable abbrev localInclusion :
    SheafOfModules.{u} R ⥤ PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat) :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

/-- **Piece (I).** `sheafificationW J R₀` is the left Bousfield local class of the local
objects `· ∈ Set.range (localInclusion α).obj` — i.e. `W g` iff precomposition with `g`
is a bijection into every (restriction of a) sheaf of modules.

Proof: mathlib identifies `sheafificationW` with the class inverted by
`PresheafOfModules.sheafification α`
(`inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`), and the left Bousfield lemma
`ObjectProperty.isLocal_eq_inverseImage_isomorphisms` identifies *that* with the local class,
using the fully-faithful right adjoint of `sheafificationAdjunction α`. -/
theorem sheafificationW_eq_isLocal :
    sheafificationW J R₀ =
      ObjectProperty.isLocal (· ∈ Set.range (localInclusion α).obj) := by
  rw [sheafificationW,
    PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α,
    ← ObjectProperty.isLocal_eq_inverseImage_isomorphisms
      (PresheafOfModules.sheafificationAdjunction α)]

/-- **Piece (I), consumable form.** If `sheafificationW J R₀ g`, then for every sheaf of
modules `H`, precomposition with `g` is a bijection
`(Y ⟶ (localInclusion α).obj H) → (X ⟶ (localInclusion α).obj H)`.

This is the exact statement consumed by the `whiskerLeft` argument: there `H` will be the
internal hom `[F, -]` applied to a sheaf (piece III shows it lands in the local objects, i.e.
is of the form `(localInclusion α).obj _`). -/
theorem sheafificationW.bijective_precomp {X Y : PresheafOfModules.{u} (R₀ ⋙ forget₂ _ _)}
    {g : X ⟶ Y} (hg : sheafificationW J R₀ g) (H : SheafOfModules.{u} R) :
    Function.Bijective
      (fun (φ : Y ⟶ (localInclusion α).obj H) => g ≫ φ) := by
  rw [sheafificationW_eq_isLocal α] at hg
  exact hg _ ⟨H, rfl⟩

end JacobianAlggeo
