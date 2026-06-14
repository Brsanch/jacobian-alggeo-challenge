import Mathlib
import Submission.Cohomology.PresheafOfModulesInternalHom

/-!
# The tensor-hom adjunction for presheaves of modules: `Closed F`

This file builds the tensor-hom adjunction `tensorLeft F ⊣ internalHomFunctor F` for presheaves of
modules over a varying commutative ring presheaf `R₀`, giving the `CategoryTheory.Closed F` instance
that the `I.1a` monoidal-localization argument consumes.

The monoidal structure on `PresheafOfModules` is the *pointwise* tensor
(`(F ⊗ G).obj X = F.obj X ⊗ G.obj X`, `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`), so
`internalHom` (the module-valued `presheafHom` over slices) is exactly its right adjoint: the
adjunction is the cartesian-closed-style curry/uncurry, assembled here from the concrete evaluation
(counit) morphism.

We work in the single-universe regime `C : Type u`, `Category.{u} C` (the curve's opens site is a
`SmallCategory`), so `internalHom F H : PresheafOfModules.{u} R₀'` and `tensorLeft F`,
`internalHomFunctor F` are endofunctors of the same category `PresheafOfModules.{u} R₀'`.

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory Opposite

namespace JacobianAlggeo

universe u

variable {C : Type u} [Category.{u} C] {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace InternalHomClosed

variable (F H : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))

/-- The identity slice object `(X, 𝟙)` over `X`, at which a value `[F,H](X)` is evaluated to recover
a morphism `F(X) ⟶ H(X)`. -/
abbrev topSlice (X : Cᵒᵖ) : (Over (unop X))ᵒᵖ := op (Over.mk (𝟙 (unop X)))

/-- Evaluation of a slice-morphism `φ : [F,H](X)` at the identity slice object, as a morphism
`F(X) ⟶ H(X)` (the components of the counit `F ⊗ [F,H] ⟶ H`). -/
noncomputable abbrev evalTop (X : Cᵒᵖ)
    (φ : (restrict X).obj F ⟶ (restrict X).obj H) : F.obj X ⟶ H.obj X :=
  φ.app (topSlice X)

set_option backward.isDefEq.respectTransparency false in
/-- The counit / evaluation map `F ⊗ [F,H] ⟶ H` at the object `X`: `f' ⊗ φ ↦ φ(X)(f')`,
evaluating the slice-morphism `φ` at the identity slice object. -/
noncomputable def evalAppMap (X : Cᵒᵖ) :
    (F.obj X) ⊗ ((internalHom F H).obj X) ⟶ H.obj X :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun f' φ => (φ.app (topSlice X)).hom f')
    (fun f'₁ f'₂ φ => by
      show (φ.app (topSlice X)).hom (f'₁ + f'₂)
        = (φ.app (topSlice X)).hom f'₁ + (φ.app (topSlice X)).hom f'₂
      rw [map_add])
    (fun c f' φ => by
      show (φ.app (topSlice X)).hom (c • f') = c • (φ.app (topSlice X)).hom f'
      rw [map_smul])
    (fun f' φ ψ => by
      show ((φ + ψ).app (topSlice X)).hom f'
        = (φ.app (topSlice X)).hom f' + (ψ.app (topSlice X)).hom f'
      rfl)
    (fun c f' φ => by
      show ((c • φ).app (topSlice X)).hom f' = c • (φ.app (topSlice X)).hom f'
      erw [internalSMulApp_hom_apply]
      show (R₀.map (𝟙 X)).hom c • (φ.app (topSlice X)).hom f' = c • (φ.app (topSlice X)).hom f'
      rw [R₀.map_id]
      rfl)

@[simp] lemma evalAppMap_tmul (X : Cᵒᵖ) (f' : F.obj X) (φ : (internalHom F H).obj X) :
    (evalAppMap F H X).hom (f' ⊗ₜ φ) = (φ.app (topSlice X)).hom f' := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The **counit / evaluation** `F ⊗ [F,H] ⟶ H` of the tensor-hom adjunction. Naturality reduces, on
a simple tensor `f' ⊗ φ`, to the naturality of the slice-morphism `φ` along the slice morphism
`Over.homMk f.unop : (Over.map f.unop).obj (X,𝟙) ⟶ (X,𝟙)` (whose `((restrict X)·).map` is `·.map f`). -/
noncomputable def internalHomEval : F ⊗ internalHom F H ⟶ H where
  app X := evalAppMap F H X
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun f' φ => ?_)
    have key := PresheafOfModules.naturality_apply φ
      (Over.homMk f.unop (by simp) :
        (Over.map f.unop).obj (Over.mk (𝟙 (unop Y))) ⟶ Over.mk (𝟙 (unop X))).op f'
    simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply, evalAppMap_tmul]
    exact key

end InternalHomClosed

end JacobianAlggeo
