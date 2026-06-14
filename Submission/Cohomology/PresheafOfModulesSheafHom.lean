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

/-! ### Bricks (2)–(5): build state (2026-06-14)

Brick (1) `ambient_isSheaf` above is COMPLETE — it reuses mathlib's heavy `presheafHom`
amalgamation (`Presheaf.IsSheaf.hom`) to establish the ambient sheaf into which the linear hom
embeds.

**Brick (2) — the forgetful embedding `u : (internalHom F H).presheaf ⋙ forget ⟶ presheafHom
F.presheaf H.presheaf`** (pointwise `φ ↦ (toPresheaf _).map φ`, injective by `toPresheaf` faithful)
is mathematically immediate via the `rfl` alignment `((restrict X).obj F).presheaf =
(Over.forget X.unop).op ⋙ F.presheaf`, but the **Lean obstruction is concrete-category coercion**:
the source `(internalHom F H).presheaf ⋙ forget AddCommGrpCat` and target `presheafHom …` must land
in the *same* hom-category (a `TypeCat`/`ConcreteCategory` `⟶`, not a bare function), so the `app`
field needs the `TypeCat.ofHom` wrapper and the `forget AddCommGrpCat` target-category must be
aligned with `presheafHom`'s `Cᵒᵖ ⥤ Type _`. Resolve the `Type` vs `TypeCat` target before the `app`
typechecks; then `naturality` is `rfl` (both sides reindex along `(Over.map f.unop)`), and
injectivity is `(toPresheaf _).map_injective`.

**Brick (3) — `internalHom_isSheaf` (the bulk, the separatedness argument)**, **(4)** local-object
packaging, **(5)** the whiskerLeft/Right/IsMonoidal port: see
`docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md` (Route A "sub-sheaf via separatedness").
The amalgamation of a linear family, taken in the ambient sheaf, is linear because each linearity
equation `y.app W (r • m) = r • y.app W m` holds in `H(W.left)` after restriction to the cover
(where `y` is the linear family member) — and `H` is separated. -/

end InternalHomSheaf

end JacobianAlggeo
