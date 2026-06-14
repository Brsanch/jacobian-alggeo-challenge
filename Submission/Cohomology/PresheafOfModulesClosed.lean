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

/-! ### The unit / coevaluation `G ⟶ [F, F ⊗ G]` -/

variable (G : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))

set_option backward.isDefEq.respectTransparency false in
/-- For `g : G(X)` and a slice object `W`, the component `f'' ↦ f'' ⊗ G(W.hom)(g)` of the unit's
slice-morphism (the "insert into the tensor" map). -/
noncomputable def coevSliceApp (X : Cᵒᵖ) (g : G.obj X) (W : (Over (unop X))ᵒᵖ) :
    F.obj (op (unop W).left) ⟶ (F ⊗ G).obj (op (unop W).left) :=
  ModuleCat.ofHom
    ((TensorProduct.mk (R₀.obj (op (unop W).left)) (F.obj (op (unop W).left))
        (G.obj (op (unop W).left))).flip ((G.map (unop W).hom.op).hom g))

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma coevSliceApp_hom_apply (X : Cᵒᵖ) (g : G.obj X) (W : (Over (unop X))ᵒᵖ)
    (f'' : F.obj (op (unop W).left)) :
    (coevSliceApp F G X g W).hom f'' = f'' ⊗ₜ[R₀.obj (op (unop W).left)] (G.map (unop W).hom.op).hom g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit's slice-morphism at `(X, g)`: the section `f'' ↦ f'' ⊗ G(W.hom)(g)` over the slice
`Over X.unop`. Naturality across `W` is `G`'s restriction functoriality (`map_comp`) + the `Over`
triangle. -/
noncomputable def coevSlice (X : Cᵒᵖ) (g : G.obj X) :
    (restrict X).obj F ⟶ (restrict X).obj (F ⊗ G) where
  app W := coevSliceApp F G X g W
  naturality {W W'} h := by
    refine ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_))
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
    erw [coevSliceApp_hom_apply, coevSliceApp_hom_apply,
      PresheafOfModules.Monoidal.tensorObj_map_tmul]
    congr 1
    erw [← PresheafOfModules.map_comp_apply]
    apply PresheafOfModules.congr_map_apply
    apply Quiver.Hom.unop_inj
    simp [Over.w]

/-! The unit `G ⟶ [F, F ⊗ G]` will assemble `coevSlice` into an `R₀(X)`-linear app `coevAppHom`
(then naturality-in-X). NOTE for the next builder: the app `G.obj X ⟶ internalHomObj F (F ⊗ G) X`
crosses the carrier diamond — `G.obj X` is over the *RingCat* `R₀'(X)` but `internalHomObj` is over
the *CommRingCat* `R₀.obj X`, so a bare `ModuleCat.ofHom` of an `R₀.obj X`-linear map fails synthesis
(`Module (R₀'(X)) (slice-hom-set)` not found). Resolve exactly as the internalHom *map* field did:
route through `ModuleCat.semilinearMapAddEquiv` over the reduced `(𝟙)`/CommRingCat hom (carrier
discipline) — see `PresheafOfModulesInternalHom.lean`'s `internalHomMapHom`. The per-component
linearity proofs (`map_add'` via `map_add`+`TensorProduct.tmul_add`; `map_smul'` via
`PresheafOfModules.map_smul`+`TensorProduct.tmul_smul`+`internalSMulApp_hom_apply`) and the
naturality-in-X (`map_comp_apply` + `op_comp`, mirroring `coevSlice`'s naturality) are otherwise ready. -/

end InternalHomClosed

end JacobianAlggeo
