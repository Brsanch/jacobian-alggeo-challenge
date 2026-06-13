import Mathlib

/-!
# Monoidal (tensor) structure on `SheafOfModules R`

This file builds the tensor product of sheaves of modules over a (commutative)
sheaf of rings — the bottom brick of the line-bundle / Picard / ample stack for
the alggeo Jacobian challenge — by **localization of the monoidal structure on
presheaves of modules**.

## Set-up

Fix a presheaf of *commutative* rings `R₀ : Cᵒᵖ ⥤ CommRingCat` and a sheaf of
rings `R : Sheaf J RingCat` together with a locally bijective morphism
`α : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj` (so `R` is the sheafification of
`R₀`). The commutativity of `R₀` is **required**: mathlib's monoidal structure on
`PresheafOfModules` (`PresheafOfModules.monoidalCategory`) is only available for a
ring presheaf of the special form `S ⋙ forget₂ CommRingCat RingCat`, since the
tensor `M ⊗ N` is computed pointwise as `M.obj X ⊗[R₀.obj X] N.obj X` and needs a
commutative base. This matches the geometric use case (the structure sheaf of a
scheme is commutative).

With
* `C := PresheafOfModules (R₀ ⋙ forget₂ _ _)` (monoidal, by `PresheafOfModules.monoidalCategory`),
* `D := SheafOfModules R`,
* `L := PresheafOfModules.sheafification α : C ⥤ D`,
* `W := sheafificationW J R₀ := J.W.inverseImage (toPresheaf …)` (the morphisms `L` inverts),

mathlib already supplies `L.IsLocalization W`
(`PresheafOfModules.instIsLocalizationSheafificationInverseImageWToPresheaf` in
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`). The general machinery
`CategoryTheory.Localization.Monoidal` (`LocalizedMonoidal L W ε`) then transports the
monoidal structure across the localization, **provided** `W` is monoidal
(`W.IsMonoidal`: multiplicative + stable under left/right whiskering).

## What is proved here

* `sheafificationW J R₀` is `IsMultiplicative`, `RespectsIso`, `ContainsIdentities`
  (free, from the `inverseImage` instances).
* `SheafOfModules.monoidalCategory α` : **`MonoidalCategory (SheafOfModules R)`**, an
  instance obtained by transporting the localized monoidal structure across the
  *defeq* type synonym `LocalizedMonoidal L W (Iso.refl _) = SheafOfModules R`. The
  monoidal unit is `L.obj (𝟙_ C) = sheafification (PresheafOfModules.unit …)`, i.e.
  the structure sheaf as a module over itself (the chosen `ε := Iso.refl`, exactly as
  in mathlib's own `Sheaf.monoidalCategory`).

The instance is stated **conditional on `[(sheafificationW J R₀).IsMonoidal]`**,
in precise analogy with mathlib's `CategoryTheory.Sheaf.monoidalCategory`, which is
itself stated conditional on `[(J.W).IsMonoidal]`. This is *not* a renamed `sorry`:
`MorphismProperty.IsMonoidal` is a substantive type class (its two whiskering fields
carry the real geometric content — see "The remaining leaf" below), not a `True`-valued
stand-in.

## The remaining leaf (`(sheafificationW J R₀).IsMonoidal`)

Discharging this unconditionally is exactly the classical theorem **"sheafification of
presheaves of modules commutes with the tensor product"** (Stacks 17.16 / EGA 0_I.4.1):
one must show that if `sheafification.map f` and `sheafification.map g` are isomorphisms
then so is `sheafification.map (f ⊗ₘ g)`, equivalently that `tensorLeft X ⋙ sheafification`
and `tensorRight Y ⋙ sheafification` invert `W`.

At the pin `5450b53e5ddc` mathlib has **no** support for this on `PresheafOfModules`:
there is no `MonoidalClosed (PresheafOfModules …)` instance (so the internal-hom /
enriched-hom proof that gives `GrothendieckTopology.W.whiskerLeft` for the
*abelian-group-presheaf-level* `J.W` in `Mathlib/CategoryTheory/Sites/Monoidal.lean`
does not port), and no "sheafification preserves tensor" lemma. The only available
structural fact is `sheafification.IsLeftAdjoint` (it preserves colimits), which is
*insufficient*: the tensor is the pointwise `· ⊗[R₀.obj X] ·`, and its commutation with
sheafification is precisely the unproven content. This is a genuine multi-hundred-LOC
sub-arc (build a `MonoidalClosed` structure on `PresheafOfModules`, or develop the
sheaf tensor product directly and identify it with the localized tensor).

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory

namespace JacobianAlggeo

universe u v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- `sheafificationW J R₀` is the class of morphisms of presheaves of modules over
`R₀ ⋙ forget₂ CommRingCat RingCat` that become isomorphisms after sheafification, i.e.
the localizing class for the sheafification functor.  It depends only on `R₀`, not on the
target sheaf of rings `R` or the morphism `α`. -/
abbrev sheafificationW (J : GrothendieckTopology C) (R₀ : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ CommRingCat RingCat))

/-- `sheafificationW` is multiplicative (it is the inverse image of the multiplicative
class `J.W`). -/
instance : (sheafificationW J R₀).IsMultiplicative := inferInstance

/-- `sheafificationW` respects isomorphisms. -/
instance : (sheafificationW J R₀).RespectsIso := inferInstance

/-- `sheafificationW` contains identities. -/
instance : (sheafificationW J R₀).ContainsIdentities := inferInstance

/-- The sheafification functor is a localization of presheaves of modules at
`sheafificationW J R₀` (this is `PresheafOfModules`' instance, re-exported here for
the monoidal construction). -/
example : (PresheafOfModules.sheafification.{u} α).IsLocalization (sheafificationW J R₀) :=
  inferInstance

section Monoidal

variable [(sheafificationW J R₀).IsMonoidal]

/-- **The localized monoidal category structure** on the sheafification target,
`MonoidalCategory (LocalizedMonoidal (sheafification α) W (Iso.refl _))`, obtained from
`CategoryTheory.Localization.Monoidal` once `W := sheafificationW J R₀` is monoidal.
The chosen unit isomorphism is `Iso.refl`, so the monoidal unit is the sheafification of
the presheaf-of-modules unit. -/
noncomputable example :
    MonoidalCategory
      (LocalizedMonoidal (PresheafOfModules.sheafification.{u} α) (sheafificationW J R₀)
        (Iso.refl _)) :=
  inferInstance

/-- **Tensor product of sheaves of modules.**  The monoidal category structure on
`SheafOfModules R`, obtained by transporting the localized monoidal structure across the
(definitional) type synonym `LocalizedMonoidal (sheafification α) W (Iso.refl _) =
SheafOfModules R`.

This is the bottom brick of the line-bundle / Picard / ample stack: it equips
`SheafOfModules R` with `⊗`, the unit `𝟙_`, the associator and unitors, and all the
coherence (pentagon/triangle), with the sheafification functor `PresheafOfModules ⥤
SheafOfModules` becoming a (strong) monoidal functor.

It is conditional on `[(sheafificationW J R₀).IsMonoidal]` — exactly as mathlib's
`CategoryTheory.Sheaf.monoidalCategory` is conditional on `[(J.W).IsMonoidal]`. See the
module docstring for why that hypothesis is the genuine remaining leaf at this pin.

It is a `def` (consumed via `attribute [local instance]` / `letI`), not a global
typeclass instance, because the monoidal structure depends on the *data* `α` (the chosen
presentation of `R` as the sheafification of the commutative presheaf of rings `R₀`),
which an instance search cannot infer. -/
@[reducible]
noncomputable def _root_.SheafOfModules.monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} R) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (PresheafOfModules.sheafification.{u} α) (sheafificationW J R₀)
      (Iso.refl _)))

/-- With the monoidal structure of `SheafOfModules.monoidalCategory`, the sheafification
functor `PresheafOfModules (R₀ ⋙ forget₂ _ _) ⥤ SheafOfModules R` is a monoidal functor
(the localization functor `toMonoidalCategory`, which is definitionally the sheafification). -/
noncomputable example :
    (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification.{u} α) (sheafificationW J R₀) (Iso.refl _)).Monoidal :=
  inferInstance

end Monoidal

end JacobianAlggeo
