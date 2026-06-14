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

/-! ## Piece (II): the internal-hom object `[F,H]` valued in `R₀(X)`-modules

For presheaves of modules `F H` over a presheaf of *commutative* rings `R₀`, the value of the
internal hom at `X : Cᵒᵖ` is the module of morphisms between the restrictions of `F` and `H` to the
slice `Over X.unop` (the module-theoretic lift of `CategoryTheory.presheafHom`). Concretely we take
the `Hom`-set `(restrict X).obj F ⟶ (restrict X).obj H` in `PresheafOfModules` over the restricted
ring presheaf and equip it with the `R₀(X)`-module structure obtained by *restriction of scalars*
along the slice: `r : R₀(X)` acts on a slice-morphism `φ` by scaling `φ` at each slice object `W`
by the restriction `R₀(W.hom)(r)` of `r`.

The one non-trivial wall here is an instance diamond: scaling a `ModuleCat (R₀'.obj _)` morphism (or
its underlying `LinearMap`) by a ring element fails synthesis, because morphism-scaling needs
`SMulCommClass`/`Linear` over the RingCat carrier, which is not found, whereas *element*-scaling
`Module (R₀.obj X) (M.obj X)` IS mathlib-provided. We resolve it by **carrier discipline**: the
scaled morphism `internalSMulApp` is built *element-wise* as a `LinearMap` typed over the
`CommRingCat` carrier `R₀.obj (op W.left)`, where all the scalings land on mathlib's provided
element-module instance. The naturality of the action (`internalHomSMul`) reduces, via the
restriction-compatibility of the scalar (`R₀(W'.hom)(r) = (S.map g)(R₀(W.hom)(r))`, from the `Over`
triangle), to `φ.naturality` together with the semilinearity of `H`'s restriction maps.

This builds `internalHomObj F H X : ModuleCat (R₀.obj X)`, the value `[F,H](X)`. The remaining pieces
of I.1a are: the restriction maps assembling these values into a `PresheafOfModules R₀` (piece II,
presheaf laws), the tensor-hom adjunction `Hom(F ⊗ G, H) ≅ Hom(G, [F,H])` (`Closed F`), the
sheaf-preservation `IsSheaf H ⟹ IsSheaf [F,H]` (piece III), and the port to
`(sheafificationW J R₀).IsMonoidal`.

No `sorry`, no `axiom`, no `ω` binders. -/

section InternalHomObject

variable (F H : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))

/-- The restriction of presheaves of modules over `R₀` to the slice `Over X.unop`, as the
pushforward along the forgetful functor `Over X.unop ⥤ C`. The value `[F,H](X)` is built from the
`Hom`-set between the restrictions of `F` and `H`. -/
noncomputable abbrev restrict (X : Cᵒᵖ) :
    PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} ((Over.forget X.unop).op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.pushforward₀ (Over.forget X.unop) (R₀ ⋙ forget₂ CommRingCat RingCat)

/-- A slice-morphism `φ`, read off at the slice object `W` as a morphism `F(W.left) ⟶ H(W.left)`
in the *reduced* `ModuleCat (R₀'(W.left))` form (defeq to `φ.app W`). Using this reduced form is
what makes the `R₀`-scaling below land on mathlib's element-module instance. -/
noncomputable abbrev appAt (X : Cᵒᵖ)
    (φ : (restrict X).obj F ⟶ (restrict X).obj H) (W : (Over X.unop)ᵒᵖ) :
    F.obj (op W.unop.left) ⟶ H.obj (op W.unop.left) := φ.app W

/-- The action of `r : R₀(X)` on a slice-morphism `φ`, at the slice object `W`: scale `φ.app W` by
the restriction `R₀(W.hom)(r)` of `r`. Built element-wise as a `LinearMap` over the `CommRingCat`
carrier `R₀.obj (op W.left)` — the carrier discipline that sidesteps the morphism-scaling diamond. -/
noncomputable def internalSMulApp (X : Cᵒᵖ) (r : R₀.obj X)
    (φ : (restrict X).obj F ⟶ (restrict X).obj H) (W : (Over X.unop)ᵒᵖ) :
    F.obj (op W.unop.left) ⟶ H.obj (op W.unop.left) :=
  ModuleCat.ofHom
    (({ toFun := fun x => (R₀.map W.unop.hom.op).hom r • (appAt F H X φ W).hom x
        map_add' := by intro x y; rw [map_add, smul_add]
        map_smul' := by
          intro a x
          simp only [map_smul, RingHom.id_apply]
          exact smul_comm _ _ _ } :
      F.obj (op W.unop.left) →ₗ[R₀.obj (op W.unop.left)] H.obj (op W.unop.left)))

@[simp] lemma internalSMulApp_hom_apply (X : Cᵒᵖ) (r : R₀.obj X)
    (φ : (restrict X).obj F ⟶ (restrict X).obj H) (W : (Over X.unop)ᵒᵖ)
    (z : F.obj (op W.unop.left)) :
    (internalSMulApp F H X r φ W).hom z
      = (R₀.map W.unop.hom.op).hom r • (appAt F H X φ W).hom z := rfl

/-- The action of `r : R₀(X)` on a slice-morphism `φ`, as a morphism of presheaves of modules.
Its naturality is the restriction-compatibility of the scalar combined with `φ.naturality` and the
semilinearity of the restriction maps of `H`. -/
noncomputable def internalHomSMul (X : Cᵒᵖ) (r : R₀.obj X)
    (φ : (restrict X).obj F ⟶ (restrict X).obj H) :
    (restrict X).obj F ⟶ (restrict X).obj H where
  app W := internalSMulApp F H X r φ W
  naturality {W W'} g := by
    have hcomp : (unop W).hom.op ≫ ((Over.forget (unop X)).map g.unop).op = (unop W').hom.op := by
      apply Quiver.Hom.unop_inj; simp [Over.w]
    have hmeq : R₀.map (unop W).hom.op ≫ R₀.map ((Over.forget (unop X)).map g.unop).op
        = R₀.map (unop W').hom.op := (R₀.map_comp _ _).symm.trans (congrArg R₀.map hcomp)
    have hcompat : ((((Over.forget X.unop).op ⋙ R₀ ⋙ forget₂ CommRingCat RingCat)).map g).hom
        ((R₀.map W.unop.hom.op).hom r) = (R₀.map W'.unop.hom.op).hom r := by
      show (R₀.map ((Over.forget (unop X)).map g.unop).op).hom
          ((R₀.map (unop W).hom.op).hom r) = (R₀.map (unop W').hom.op).hom r
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmeq) r
    ext y
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
    erw [internalSMulApp_hom_apply, internalSMulApp_hom_apply]
    simp only [appAt]
    erw [PresheafOfModules.naturality_apply, PresheafOfModules.map_smul]
    rw [hcompat]
    rfl

/-- The internal-hom value `[F,H](X)` carries an `R₀(X)`-module structure, with `r` acting by the
slice-scaling `internalHomSMul`. The module axioms reduce (via the element-wise apply lemma) to the
ring-hom properties of `R₀.map` and the module axioms over each slice object. -/
noncomputable instance internalHomModule (X : Cᵒᵖ) :
    Module (R₀.obj X) ((restrict X).obj F ⟶ (restrict X).obj H) where
  smul r φ := internalHomSMul F H X r φ
  one_smul φ := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom 1 • (appAt F H X φ W).hom z = (appAt F H X φ W).hom z
    rw [map_one, one_smul]
  mul_smul a b φ := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom (a * b) • (appAt F H X φ W).hom z
      = (R₀.map W.unop.hom.op).hom a • (R₀.map W.unop.hom.op).hom b • (appAt F H X φ W).hom z
    rw [map_mul, mul_smul]
  smul_zero r := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom r • (appAt F H X (0 : _ ⟶ _) W).hom z = 0
    rw [show (appAt F H X (0 : _ ⟶ _) W).hom z = 0 from rfl, smul_zero]
  zero_smul φ := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom 0 • (appAt F H X φ W).hom z = 0
    rw [map_zero, zero_smul]
  smul_add r φ ψ := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom r • (appAt F H X (φ + ψ) W).hom z
      = (R₀.map W.unop.hom.op).hom r • (appAt F H X φ W).hom z
        + (R₀.map W.unop.hom.op).hom r • (appAt F H X ψ W).hom z
    rw [show (appAt F H X (φ + ψ) W).hom z
      = (appAt F H X φ W).hom z + (appAt F H X ψ W).hom z from rfl, smul_add]
  add_smul a b φ := by
    refine PresheafOfModules.hom_ext (fun W => ModuleCat.hom_ext (LinearMap.ext (fun z => ?_)))
    show (R₀.map W.unop.hom.op).hom (a + b) • (appAt F H X φ W).hom z
      = (R₀.map W.unop.hom.op).hom a • (appAt F H X φ W).hom z
        + (R₀.map W.unop.hom.op).hom b • (appAt F H X φ W).hom z
    rw [map_add, add_smul]

/-- **The internal-hom object `[F,H](X)`**, as an `R₀(X)`-module: the module of morphisms between the
slice-restrictions of `F` and `H`. This is the value, at `X`, of the internal hom of presheaves of
modules being built towards `(sheafificationW J R₀).IsMonoidal`. -/
noncomputable def internalHomObj (X : Cᵒᵖ) : ModuleCat (R₀.obj X) :=
  ModuleCat.of (R₀.obj X) ((restrict X).obj F ⟶ (restrict X).obj H)

end InternalHomObject

end JacobianAlggeo
