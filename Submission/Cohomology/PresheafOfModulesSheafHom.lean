import Mathlib
import Submission.Cohomology.PresheafOfModulesInternalHom

/-!
# I.1a piece (III): the internal hom of a sheaf of modules is a sheaf

This file builds piece (III) of `I.1a` — sheaf-preservation of the internal hom of presheaves of
modules — via the **sub-sheaf-through-separatedness** strategy
(`docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md`, Route A):

`(internalHom F H).presheaf` (the R₀-linear PMod-morphisms over slices) embeds as a **mono** into
the type-valued sheaf `presheafHom F.presheaf H.presheaf` (all natural transformations of the
underlying abelian-group presheaves). mathlib already proves the latter is a sheaf
(`Presheaf.IsSheaf.hom`, the heavy amalgamation). We then show the amalgamation of a family of
linear morphisms is again linear — using only that `H` is **separated** — so it lands back in the
sub-object, making `(internalHom F H).presheaf` a sheaf.

The forgetful embedding `u` is `toPresheaf` applied to slice-morphisms: by the `rfl` alignment
`((restrict X).obj F).presheaf = (Over.forget X.unop).op ⋙ F.presheaf`
(`pushforward₀CompToPresheaf = Iso.refl`), the underlying presheaf of a slice-morphism is exactly a
section of `presheafHom`, and `toPresheaf` faithful makes `u` a pointwise injection.

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory Opposite Limits

namespace JacobianAlggeo

universe u v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace InternalHomSheaf

variable (F H : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))

/-- **Brick (1): the ambient sheaf.** When the underlying presheaf of `H` is a sheaf, the
type-valued presheaf `presheafHom F.presheaf H.presheaf` of natural transformations between the
underlying abelian-group presheaves (over each slice) is a sheaf — this is mathlib's
`Presheaf.IsSheaf.hom`, the heavy amalgamation argument, reused as a black box. -/
theorem ambient_isSheaf (hH : Presheaf.IsSheaf J H.presheaf) :
    Presheaf.IsSheaf J (presheafHom F.presheaf H.presheaf) :=
  Presheaf.IsSheaf.hom F.presheaf H.presheaf hH

/-- **Brick (2): the forgetful embedding `toAmbient`.** The natural transformation
`(internalHom F H).presheaf ⋙ forget AddCommGrpCat ⟶ presheafHom F.presheaf H.presheaf`
that sends a slice-morphism `φ : (restrict X).obj F ⟶ (restrict X).obj H` (an element of
`(internalHom F H).presheaf.obj X`, after `forget`) to its underlying natural transformation of
abelian-group presheaves `(toPresheaf _).map φ` (an element of `(presheafHom F.presheaf
H.presheaf).obj X`, by the `rfl` alignment `((restrict X).obj F).presheaf = (Over.forget X.unop).op ⋙
F.presheaf`). The `app` lands in the `TypeCat`-style hom of `Cᵒᵖ ⥤ Type _` via `TypeCat.ofHom`, and
naturality is `rfl` (both sides reindex along `Over.map f.unop`). -/
noncomputable def toAmbient :
    (internalHom F H).presheaf ⋙ forget AddCommGrpCat ⟶ presheafHom F.presheaf H.presheaf where
  app X := TypeCat.ofHom
    (fun (φ : (restrict X).obj F ⟶ (restrict X).obj H) => (PresheafOfModules.toPresheaf _).map φ)
  naturality := by intro X Y f; rfl

@[simp] lemma toAmbient_app_apply (X : Cᵒᵖ) (φ : (restrict X).obj F ⟶ (restrict X).obj H) :
    (toAmbient F H).app X φ = (PresheafOfModules.toPresheaf _).map φ := rfl

/-- The embedding `toAmbient` is pointwise injective: `toPresheaf` is faithful, so distinct
slice-morphisms have distinct underlying natural transformations. This makes
`(internalHom F H).presheaf` a sub-object of the ambient sheaf `presheafHom F.presheaf H.presheaf`. -/
lemma toAmbient_app_injective (X : Cᵒᵖ) : Function.Injective ((toAmbient F H).app X) :=
  fun _ _ h => (PresheafOfModules.toPresheaf _).map_injective h

/-! ### Bricks (3)–(5): build state (2026-06-14)

Bricks (1) `ambient_isSheaf` and (2) `toAmbient`/`toAmbient_app_injective` above are COMPLETE: the
linear hom embeds as a pointwise-injective sub-object of mathlib's `presheafHom` sheaf.

**Brick (3) — `internalHom_isSheaf` (the bulk, the separatedness argument)**, **(4)** local-object
packaging, **(5)** the whiskerLeft/Right/IsMonoidal port: see
`docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md` (Route A "sub-sheaf via separatedness").
The amalgamation of a linear family, taken in the ambient sheaf, is linear because each linearity
equation `y.app W (r • m) = r • y.app W m` holds in `H(W.left)` after restriction to the cover
(where `y` is the linear family member) — and `H` is separated. -/

end InternalHomSheaf

end JacobianAlggeo
