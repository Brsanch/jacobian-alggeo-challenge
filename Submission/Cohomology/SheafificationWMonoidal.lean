import Mathlib
import Submission.Cohomology.PresheafOfModulesClosed
import Submission.Cohomology.PresheafOfModulesSheafHom

/-!
# I.1a bricks (4)–(5): `(sheafificationW J R₀).IsMonoidal`

This file discharges the one undischarged hypothesis of `SheafOfModules.monoidalCategory`
(`Submission/Cohomology/SheafOfModulesMonoidal.lean`): the **left Bousfield class
`sheafificationW J R₀` is monoidal**, i.e. it is stable under left/right whiskering. This is the
classical theorem *"sheafification of presheaves of modules commutes with the tensor product"*
(Stacks 17.16 / EGA 0_I.4.1), here delivered by mirroring mathlib's
`CategoryTheory.GrothendieckTopology.W.monoidal` with the **internal hom of presheaves of modules**
(built in pieces I–III) in place of the missing `MonoidalClosed (PresheafOfModules …)`.

## Bricks

* **(4) `mem_isoClosure_of_isSheaf`** — a presheaf of modules whose underlying presheaf is a sheaf is
  (up to isomorphism) a *local object* of `sheafificationW`, i.e. the restriction of a sheaf of
  modules. Proof: its sheafification unit is an isomorphism, since `toPresheaf` reflects isomorphisms
  and `toPresheaf` of the unit is the abelian-group sheafification unit `toSheafify`, which is an
  isomorphism on a sheaf. This is the local-object packaging that piece (III)
  (`internalHom_isSheaf`) feeds.
* **(5a) `sheafificationW_whiskerLeft`** — `sheafificationW g ⟹ sheafificationW (F ◁ g)`. Reduce to
  orthogonality against the local objects (`sheafificationW_eq_isLocal`); the internal hom `[F, Z]`
  into a local object `Z` is itself local (brick 4 + piece III), and the tensor–hom adjunction
  `tensorLeft F ⊣ [F,-]` (piece II) conjugates precomposition by `F ◁ g` into precomposition by `g`.
* **(5b) `sheafificationW_whiskerRight`** — from `whiskerLeft` via the symmetric braiding on
  presheaves of modules (`MorphismProperty.arrow_mk_iso_iff` + `β_`).
* **(5) `sheafificationW_isMonoidal`** — `(sheafificationW J R₀).IsMonoidal`, assembling (5a) + (5b).

This makes `SheafOfModules.monoidalCategory` unconditional (the `[(sheafificationW J R₀).IsMonoidal]`
hypothesis is now derivable from the sheafification data `α`): at any concrete instantiation a user
writes `haveI := sheafificationW_isMonoidal α` (the data `α` being already in scope, as it is in the
geometric use case for the curve's structure sheaf).

Single-universe (`C : Type u`, `Category.{u} C`, modules `.{u}`), matching pieces II and III.

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory Opposite Limits Presieve

namespace JacobianAlggeo

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **Brick (4).** A presheaf of modules `M` whose underlying presheaf is a sheaf is, up to
isomorphism, the restriction of a sheaf of modules (a *local object* of `sheafificationW`).

The sheafification unit `M ⟶ (localInclusion α).obj (sheafification α |>.obj M)` is an isomorphism:
its image under `toPresheaf` is the abelian-group sheafification unit `toSheafify J M.presheaf`
(`toPresheaf_map_sheafificationAdjunction_unit_app`), which is an isomorphism because `M.presheaf` is
a sheaf (`isIso_toSheafify`); and `toPresheaf` reflects isomorphisms. Hence `M` is isomorphic to a
genuine restriction `(localInclusion α).obj _`. -/
lemma mem_isoClosure_of_isSheaf (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))
    (hM : Presheaf.IsSheaf J M.presheaf) :
    ObjectProperty.isoClosure (fun N => N ∈ Set.range (localInclusion α).obj) M := by
  have hunit : IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app M) := by
    have h2 : IsIso ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app M)) := by
      rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact CategoryTheory.isIso_toSheafify J hM
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact ⟨_, ⟨(PresheafOfModules.sheafification α).obj M, rfl⟩, ⟨@asIso _ _ _ _ _ hunit⟩⟩

include α in
/-- **Brick (5a): left whiskering.** `sheafificationW J R₀ g ⟹ sheafificationW J R₀ (F ◁ g)`.

Working with the local-object characterization (`sheafificationW_eq_isLocal`): to show
precomposition with `F ◁ g` is bijective into every local object `Z = (localInclusion α).obj H`,
conjugate by the tensor–hom adjunction `tensorLeft F ⊣ [F,-]` (piece II) — this turns it into
precomposition with `g` into `[F, Z]`, which is local by brick 4 + piece III
(`internalHom_isSheaf`), so bijective by hypothesis `hg`. -/
lemma sheafificationW_whiskerLeft
    (F : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))
    {Y₁ Y₂ : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} {g : Y₁ ⟶ Y₂}
    (hg : sheafificationW J R₀ g) :
    sheafificationW J R₀ (F ◁ g) := by
  rw [sheafificationW_eq_isLocal α]
  rintro Z ⟨H, rfl⟩
  have hloc : ObjectProperty.isoClosure (fun N => N ∈ Set.range (localInclusion α).obj)
      ((internalHomFunctor F).obj ((localInclusion α).obj H)) :=
    mem_isoClosure_of_isSheaf α _
      (InternalHomSheaf.internalHom_isSheaf F ((localInclusion α).obj H) H.isSheaf)
  have hg' : (ObjectProperty.isoClosure
      (fun N => N ∈ Set.range (localInclusion α).obj)).isLocal g := by
    rw [ObjectProperty.isoClosure_isLocal, ← sheafificationW_eq_isLocal α]; exact hg
  have hbij := hg' _ hloc
  have hcomp : (fun (h : F ⊗ Y₂ ⟶ (localInclusion α).obj H) => (F ◁ g) ≫ h)
      = ⇑((InternalHomClosed.internalHomAdjunction F).homEquiv Y₁ ((localInclusion α).obj H)).symm ∘
          ((fun ψ => g ≫ ψ) ∘
            ⇑((InternalHomClosed.internalHomAdjunction F).homEquiv Y₂
              ((localInclusion α).obj H))) := by
    funext h
    show (tensorLeft F).map g ≫ h
        = ((InternalHomClosed.internalHomAdjunction F).homEquiv Y₁ _).symm
            (g ≫ (InternalHomClosed.internalHomAdjunction F).homEquiv Y₂ _ h)
    rw [← (InternalHomClosed.internalHomAdjunction F).homEquiv_naturality_left,
        Equiv.symm_apply_apply]
  rw [hcomp]
  exact (((InternalHomClosed.internalHomAdjunction F).homEquiv Y₁ _).symm.bijective).comp
    (hbij.comp ((InternalHomClosed.internalHomAdjunction F).homEquiv Y₂ _).bijective)

include α in
/-- **Brick (5b): right whiskering**, from left whiskering via the symmetric braiding on presheaves
of modules. -/
lemma sheafificationW_whiskerRight
    {F₁ F₂ : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} {f : F₁ ⟶ F₂}
    (hf : sheafificationW J R₀ f)
    (G : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    sheafificationW J R₀ (f ▷ G) :=
  ((sheafificationW J R₀).arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2
    (sheafificationW_whiskerLeft α G hf)

include α in
/-- **Brick (5): `(sheafificationW J R₀).IsMonoidal`** — the left Bousfield localizing class of the
sheafification of presheaves of modules is monoidal. This discharges the hypothesis of
`SheafOfModules.monoidalCategory`, making the tensor product of sheaves of modules unconditional
(given the sheafification data `α`). -/
theorem sheafificationW_isMonoidal : (sheafificationW J R₀).IsMonoidal where
  whiskerLeft F _ _ _ hg := sheafificationW_whiskerLeft α F hg
  whiskerRight _ hf G := sheafificationW_whiskerRight α hf G

end JacobianAlggeo
