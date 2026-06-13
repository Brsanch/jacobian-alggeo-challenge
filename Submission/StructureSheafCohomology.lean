import Mathlib
import Submission.StructureSheafModule
import Submission.SheafCohomologyModuleCat

/-!
# Segment 2 — `H¹(C, 𝒪_C)` as a `k`-module, and the genus

Build-target step 2 (`NEXT_SESSION.md`): present the structure sheaf `𝒪_C` of the
curve `C : Over (Spec k)` as a sheaf valued in `ModuleCat k`, and feed it to the
derived-functor cohomology `H` of Segment 1 to obtain `H¹(C, 𝒪_C)` as a `k`-module.
This is the fork-B path — it uses the *opens site* of `C.left` and its derived
cohomology, so it never needs the explicit finite affine cover that blocked the
Čech route (the M1b mathlib gap).

## The chain

* `kStruct C : (const k) ⟶ 𝒪_C` — the `k`-algebra structure on the structure
  sheaf, induced by the structure morphism `C.hom : C.left ⟶ Spec k`
  (`k ≅ Γ(Spec k) →⟮appTop⟯ Γ(C.left, ⊤) →⟮restrict⟯ 𝒪_C(U)`).
* `structurePresheafUnder C` — `𝒪_C` lifted to a presheaf of `k`-algebras
  (`(Opens C.left)ᵒᵖ ⥤ Under (CommRingCat.of k)`), via `Under.mk (kStruct.app U)`.
* `structurePresheafModule C` — postcompose with `underToModuleCat` (Segment 1b's
  `Under R ⥤ ModuleCat R`) to land in `ModuleCat k`.
* `structureSheafModule C : Sheaf (Opens.grothendieckTopology C.left) (ModuleCat k)`
  — the sheaf condition transports from `C.left`'s own sheaf condition: the
  underlying `Type`-presheaf of the `ModuleCat k` version is *defeq* to that of the
  `CommRingCat` structure sheaf, and `forget (ModuleCat k)` reflects limits
  (`isSheaf_of_isSheaf_comp`).
* `H1 C := H _ k 1 (structureSheafModule C)` — `H¹(C, 𝒪_C)`, a `k`-module (via
  Segment 1), so `FiniteDimensional k (H1 C)` and `Module.finrank k (H1 C)` are
  type-correct.
* `genus C := Module.finrank k (H1 C)` — the genus, i.e. `dim_k H¹(C, 𝒪_C)`. This
  is the intended content of `Challenge.lean`'s hole 1; the actual hole is filled in
  `Submission.lean` (`Submission.genus`) with the same definition.

## Gate-6 note

`HasSheafify (Opens.grothendieckTopology C.left) (ModuleCat k)` resolves
*automatically* at the pin (the general `HasSheafify` instance for a target whose
`forget` preserves limits, with small covers) — so the Segment-1 `H` applies to the
curve's opens site with no hypothesis to discharge. Likewise
`HasExt`/`Linear k`/`Module k (Ext …)` are all automatic (Segment 1).

No `sorry`, no `axiom`, no `ω` binders (Lean 4.30 reserves `ω`).
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace JacobianAlggeo

universe u

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-- The ring map `k → Γ(C.left, ⊤)` induced by the structure morphism
`C.hom : C.left ⟶ Spec k`: invert `Γ(Spec k, ⊤) ≅ k` and apply `C.hom` on global
sections. -/
noncomputable def toΓtop : CommRingCat.of k ⟶ C.left.presheaf.obj (op ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop

/-- The `k`-algebra structure on the structure sheaf, as a natural transformation
`const k ⟶ 𝒪_C`: on an open `U`, `k → Γ(C.left, ⊤) → 𝒪_C(U)` (global structure map
followed by restriction). Naturality is restriction-compatibility of `𝒪_C`. -/
noncomputable def kStruct :
    (Functor.const (Opens C.left)ᵒᵖ).obj (CommRingCat.of k) ⟶ C.left.presheaf where
  app U := toΓtop C ≫ C.left.presheaf.map (homOfLE le_top).op
  naturality U V f := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    congr 1

/-- The structure sheaf lifted to a presheaf of `k`-algebras,
`(Opens C.left)ᵒᵖ ⥤ Under (CommRingCat.of k)`: each section ring carries the
`k`-algebra structure `kStruct.app U`, and restriction maps are `k`-algebra maps
(naturality of `kStruct`). -/
noncomputable def structurePresheafUnder :
    (Opens C.left)ᵒᵖ ⥤ Under (CommRingCat.of k) where
  obj U := Under.mk ((kStruct C).app U)
  map {U V} f := Under.homMk (C.left.presheaf.map f) (by
    have := (kStruct C).naturality f
    dsimp at this ⊢
    rw [Category.id_comp] at this
    exact this.symm)

/-- The structure sheaf as a presheaf valued in `ModuleCat k`:
`structurePresheafUnder` postcomposed with the `Under R ⥤ ModuleCat R` forgetful
functor (`underToModuleCat`, Segment 1b). -/
noncomputable def structurePresheafModule : (Opens C.left)ᵒᵖ ⥤ ModuleCat.{u} k :=
  structurePresheafUnder C ⋙ underToModuleCat (CommRingCat.of k)

/-- **`𝒪_C` as a sheaf valued in `ModuleCat k`.** The sheaf condition transports from
`C.left`'s own sheaf condition: `structurePresheafModule C ⋙ forget (ModuleCat k)` is
defeq to `C.left.presheaf ⋙ forget CommRingCat` (the `ModuleCat k` and `CommRingCat`
versions have the same underlying `Type`-presheaf), and `forget (ModuleCat k)`
reflects limits. -/
noncomputable def structureSheafModule :
    Sheaf (Opens.grothendieckTopology C.left) (ModuleCat.{u} k) :=
  ⟨structurePresheafModule C, by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{u} k))
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ (forget CommRingCat.{u}) C.left.IsSheaf⟩

/-- **`H¹(C, 𝒪_C)` as a `k`-module.** Degree-1 derived sheaf cohomology (Segment 1's
`H`) of the structure sheaf on the opens site of `C.left`. It is a `k`-module, so
`FiniteDimensional k (H1 C)` (Serre finiteness, the Segment-3 target) and
`Module.finrank k (H1 C)` are type-correct. -/
noncomputable abbrev H1 : Type u :=
  H (Opens.grothendieckTopology C.left) k 1 (structureSheafModule C)

/-- **The genus** `g = dim_k H¹(C, 𝒪_C)` — the intended content of `Challenge.lean`'s
hole 1 (`genus`). `Module.finrank` is total (junk value `0` if `H¹` is not
finite-dimensional); the value is the honest genus once Serre finiteness (Segment 3)
is established. The actual hole is filled in `Submission.lean` (`Submission.genus`). -/
noncomputable def genusH1 : ℕ := Module.finrank k (H1 C)

end JacobianAlggeo
