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

set_option backward.isDefEq.respectTransparency false in
/-- The unit's **app at `X`**: the `R₀(X)`-linear map `g ↦ coevSlice g`, into `[F, F ⊗ G](X)`.
This crosses the carrier diamond — `G.obj X` is over the *RingCat* `R₀'(X)` but `internalHomObj` is
over the *CommRingCat* `R₀.obj X` — by routing through `ModuleCat.semilinearMapAddEquiv` over the
identity ring hom (carrier discipline), exactly as `internalHomMapHom` did. Additivity in `g` is
`TensorProduct.tmul_add`; `R₀(X)`-linearity is `PresheafOfModules.map_smul` (semilinearity of `G`'s
restriction) followed by `TensorProduct.tmul_smul`, matching the `internalSMulApp` scaling. -/
noncomputable def coevAppHom (X : Cᵒᵖ) :
    G.obj X ⟶ (internalHom F (F ⊗ G)).obj X :=
  ModuleCat.semilinearMapAddEquiv (RingHom.id (R₀.obj X)) (G.obj X) (internalHomObj F (F ⊗ G) X)
    ({ toFun := fun g => coevSlice F G X g
       map_add' := by
         intro g g'
         refine PresheafOfModules.hom_ext
           (fun W => ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_)))
         show (coevSliceApp F G X (g + g') W).hom f''
           = (coevSliceApp F G X g W).hom f'' + (coevSliceApp F G X g' W).hom f''
         rw [coevSliceApp_hom_apply, coevSliceApp_hom_apply, coevSliceApp_hom_apply, map_add,
           TensorProduct.tmul_add]
       map_smul' := by
         intro r g
         refine PresheafOfModules.hom_ext
           (fun W => ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_)))
         show (coevSliceApp F G X (r • g) W).hom f''
           = (R₀.map (unop W).hom.op).hom r • (coevSliceApp F G X g W).hom f''
         rw [coevSliceApp_hom_apply, coevSliceApp_hom_apply, ← TensorProduct.tmul_smul]
         congr 1
         erw [PresheafOfModules.map_smul]
         rfl } :
      G.obj X →ₛₗ[RingHom.id (R₀.obj X)] internalHomObj F (F ⊗ G) X)

@[simp] lemma coevAppHom_hom_apply (X : Cᵒᵖ) (g : G.obj X) :
    (coevAppHom F G X).hom g = coevSlice F G X g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The **unit / coevaluation** `G ⟶ [F, F ⊗ G]` of the tensor-hom adjunction (per `G`). Naturality
in `X` mirrors `coevSlice`'s naturality: both sides reduce, on `g` and a slice object `V`, to
`G`'s restriction functoriality (`map_comp_apply`) along the `Over.map f.unop`-reindexed slice. -/
noncomputable def internalHomCoev : G ⟶ internalHom F (F ⊗ G) where
  app X := coevAppHom F G X
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext (fun g => ?_))
    show coevSlice F G Y ((G.map f).hom g) = internalHomMap F (F ⊗ G) f (coevSlice F G X g)
    refine PresheafOfModules.hom_ext (fun V => ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_)))
    rw [internalHomMap_app]
    show (coevSliceApp F G Y ((G.map f).hom g) V).hom f''
      = (coevSliceApp F G X g (op ((Over.map f.unop).obj V.unop))).hom f''
    rw [coevSliceApp_hom_apply, coevSliceApp_hom_apply, ← PresheafOfModules.map_comp_apply]
    congr 1

/-! ### The counit and unit as natural transformations in the module variable -/

set_option backward.isDefEq.respectTransparency false in
/-- The **counit** `[F,-] ⋙ (F ⊗ -) ⟶ 𝟭` as a natural transformation in the module variable, with
components `internalHomEval F H`. Naturality in `H` reduces, on `f' ⊗ φ`, to evaluating the
slice-morphism `φ ≫ (restrict X).map θ` at the identity slice — definitionally `θ.app X` applied to
the evaluation of `φ`. -/
noncomputable def internalHomEvalNat :
    internalHomFunctor F ⋙ tensorLeft F ⟶
      𝟭 (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) where
  app H := internalHomEval F H
  naturality {H₁ H₂} θ := by
    refine PresheafOfModules.hom_ext (fun X => ?_)
    refine ModuleCat.MonoidalCategory.tensor_ext (fun f' φ => ?_)
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The **unit** `𝟭 ⟶ (F ⊗ -) ⋙ [F,-]` as a natural transformation in the module variable, with
components `internalHomCoev F G`. Naturality in `G` reduces, on `g` and a slice object `W`, to the
naturality of `γ` (`PresheafOfModules.naturality_apply`) under the `whiskerLeft`/`coevSlice`
combinatorics. -/
noncomputable def internalHomCoevNat :
    𝟭 (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) ⟶
      tensorLeft F ⋙ internalHomFunctor F where
  app G := internalHomCoev F G
  naturality {G₁ G₂} γ := by
    refine PresheafOfModules.hom_ext (fun X => ModuleCat.hom_ext (LinearMap.ext (fun g => ?_)))
    show coevSlice F G₂ X ((γ.app X).hom g) = coevSlice F G₁ X g ≫ (restrict X).map (F ◁ γ)
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_)))
    show (coevSliceApp F G₂ X ((γ.app X).hom g) W).hom f''
      = (((restrict X).map (F ◁ γ)).app W).hom ((coevSliceApp F G₁ X g W).hom f'')
    rw [coevSliceApp_hom_apply, coevSliceApp_hom_apply]
    erw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
    congr 1
    exact (PresheafOfModules.naturality_apply γ (unop W).hom.op g).symm

/-! ### The tensor-hom adjunction `tensorLeft F ⊣ internalHomFunctor F` and `Closed F` -/

set_option backward.isDefEq.respectTransparency false in
/-- The **tensor-hom adjunction** `tensorLeft F ⊣ [F,-]` for presheaves of modules over a varying
commutative-ring presheaf. Unit/counit are `internalHomCoevNat`/`internalHomEvalNat`. The two triangle
identities reduce, on a simple tensor `f' ⊗ g` (resp. a slice-morphism `φ`), to `G.map (𝟙 X) = 𝟙`
(left) and the `Over.map`/`topSlice` reindexing collapse (right, definitional). -/
noncomputable def internalHomAdjunction : tensorLeft F ⊣ internalHomFunctor F where
  unit := internalHomCoevNat F
  counit := internalHomEvalNat F
  left_triangle_components G := by
    refine PresheafOfModules.hom_ext (fun X => ?_)
    refine ModuleCat.MonoidalCategory.tensor_ext (fun f' g => ?_)
    show (coevSliceApp F G X g (topSlice X)).hom f' = f' ⊗ₜ[R₀.obj X] g
    rw [coevSliceApp_hom_apply]
    congr 1
    show (G.map (𝟙 X)).hom g = g
    rw [PresheafOfModules.map_id]
    rfl
  right_triangle_components H := by
    refine PresheafOfModules.hom_ext (fun X => ModuleCat.hom_ext (LinearMap.ext (fun φ => ?_)))
    show coevSlice F (internalHom F H) X φ ≫ (restrict X).map (internalHomEval F H) = φ
    refine PresheafOfModules.hom_ext (fun V => ModuleCat.hom_ext (LinearMap.ext (fun f'' => ?_)))
    rw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [coevSliceApp_hom_apply, evalAppMap_tmul, internalHomMapHom_hom_apply, internalHomMap_app]
    have hobj : (op ((Over.map (unop V).hom.op.unop).obj
        (unop (topSlice ((Over.forget (unop X)).op.obj V)))) : (Over (unop X))ᵒᵖ) = V := by
      refine congrArg op ?_
      show Over.mk (𝟙 (unop V).left ≫ (unop V).hom) = Over.mk (unop V).hom
      rw [Category.id_comp]
    have key : φ.app (op ((Over.map (unop V).hom.op.unop).obj
        (unop (topSlice ((Over.forget (unop X)).op.obj V))))) = φ.app V :=
      eq_of_heq (congr_arg_heq φ.app hobj)
    rw [key]
    rfl

/-- **`F` is a closed object of `PresheafOfModules R₀'`**: `tensorLeft F` has the right adjoint
`[F,-] = internalHomFunctor F`. This is the tensor-hom adjunction that the `I.1a`
monoidal-localization argument (`(sheafificationW J R₀).IsMonoidal`) consumes. -/
noncomputable instance closedObj : Closed F where
  rightAdj := internalHomFunctor F
  adj := internalHomAdjunction F

end InternalHomClosed

end JacobianAlggeo
