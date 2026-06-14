import Mathlib
import Submission.Cohomology.PresheafOfModulesInternalHom

/-!
# I.1a piece (III): the internal hom of a sheaf of modules is a sheaf

This file builds piece (III) of `I.1a` — sheaf-preservation of the internal hom of presheaves of
modules — via the **sub-sheaf-through-separatedness** strategy
(`docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md`, Route A):

`(internalHom F H).presheaf` (the `R₀`-linear `PresheafOfModules`-morphisms over slices) embeds as a
**mono** into the type-valued sheaf `presheafHom F.presheaf H.presheaf` (all natural transformations
of the underlying abelian-group presheaves). mathlib already proves the latter is a sheaf
(`Presheaf.IsSheaf.hom`, the heavy amalgamation). We then show the amalgamation of a family of
linear morphisms is again linear — using only that `H` is **separated** — so it lands back in the
sub-object, making `(internalHom F H).presheaf` a sheaf.

The forgetful embedding `toAmbient` is `toPresheaf` applied to slice-morphisms: by the `rfl`
alignment `((restrict X).obj F).presheaf = (Over.forget X.unop).op ⋙ F.presheaf`
(`pushforward₀CompToPresheaf = Iso.refl`), the underlying presheaf of a slice-morphism is exactly a
section of `presheafHom`, and `toPresheaf` faithful makes `toAmbient` a pointwise injection.

This file is stated in the **single-universe** setting (`C : Type u`, `Category.{u} C`, modules in
universe `u`) to match piece (II) (`PresheafOfModulesClosed.lean`) and to keep the value categories
of the forgetful sheaf comparisons in the universe `mathlib`'s `Presheaf.isSheaf_iff_isSheaf_forget`
demands (which fixes the abelian-group value category to `AddCommGrpCat.{max v u}`, here `= u`).

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory Opposite Limits Presieve

namespace JacobianAlggeo

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
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

set_option backward.isDefEq.respectTransparency false in
/-- **Brick (3): the internal hom of a sheaf of modules is a sheaf** (Stacks 17.16 / the linear
refinement of `Presheaf.IsSheaf.hom`).

If the underlying presheaf of `H` is a sheaf, then so is the underlying presheaf of the internal hom
`[F, H] = internalHom F H`. This is the load-bearing content of `I.1a`: it is what makes
`internalHom F (localInclusion α).obj H` land back in the (restrictions of) sheaves of modules, hence
what feeds the `whiskerLeft` step of `(sheafificationW J R₀).IsMonoidal`.

**Proof (sub-sheaf via separatedness).** Reduce to the type-level sheaf condition via
`isSheaf_iff_isSheaf_forget` + `isSheaf_iff_isSheaf_of_type`. A compatible family `x` of
slice-morphisms over a covering sieve `S` of `X` forgets (along `toAmbient`) to a compatible family
in the ambient sheaf `presheafHom F.presheaf H.presheaf` (brick 1), which therefore amalgamates to a
unique natural transformation `y`. The only thing to check is that `y` is `R₀`-linear at each slice
`W` (so that it is the underlying transformation of a genuine slice-morphism `φ = homMk y _`): for
`r` a scalar and `m` a section, the two sections `y.app W (r • m)` and `r • y.app W m` of `H` over
`W.left` agree after restriction along every arrow `h` of the pulled-back covering sieve
`S.pullback W.unop.hom` — there `y` agrees (by `PresheafHom.isAmalgamation_iff`) with the *linear*
family member `x (h ≫ W.unop.hom)`, and the scalar passes through by `PresheafOfModules.map_smul`
together with that member's `R₀`-linearity. Since `H` is separated, the two sections are equal. The
amalgamation `φ`, its amalgamation property, and uniqueness then transport across the faithful,
injective `toAmbient`. -/
theorem internalHom_isSheaf (hH : Presheaf.IsSheaf J H.presheaf) :
    Presheaf.IsSheaf J (internalHom F H).presheaf := by
  -- the ambient `presheafHom` sheaf, and `H` itself, as type-level sheaves
  have hQ : Presieve.IsSheaf J (presheafHom F.presheaf H.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (ambient_isSheaf F H hH)
  have hHsheaf : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget J H.presheaf (forget AddCommGrpCat)).1 hH)
  rw [Presheaf.isSheaf_iff_isSheaf_forget J (internalHom F H).presheaf (forget AddCommGrpCat),
      isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  -- amalgamate the forgotten family in the ambient sheaf
  obtain ⟨y, hy, yuniq⟩ := hQ S hS (x.map (toAmbient F H)) (hx.map (toAmbient F H))
  have hyamalg := (PresheafHom.isAmalgamation_iff S _ (hx.map (toAmbient F H)) y).1 hy
  -- the glued slice-morphism: `y` upgraded to an `R₀`-linear morphism (linearity via separatedness)
  set φ : (restrict (op X)).obj F ⟶ (restrict (op X)).obj H :=
    PresheafOfModules.homMk y (by
      intro W r m
      refine (hHsheaf (S.pullback W.unop.hom)
        (J.pullback_stable W.unop.hom hS)).isSeparatedFor.ext (fun T' h hh => ?_)
      have hg : S.arrows (h ≫ W.unop.hom) := hh
      -- naturality of the amalgamation `y` along the slice reindexing by `h`
      have key : ∀ (z : F.presheaf.obj (op W.unop.left)),
          y.app (op (Over.mk (h ≫ W.unop.hom))) (F.presheaf.map h.op z)
            = H.presheaf.map h.op (y.app W z) := by
        intro z
        simpa using NatTrans.naturality_apply (F := (Over.forget X).op ⋙ F.presheaf)
          (G := (Over.forget X).op ⋙ H.presheaf) y
          ((Over.homMk h : Over.mk (h ≫ W.unop.hom) ⟶ W.unop).op) z
      -- at an arrow of the cover, `y` agrees with the *linear* family member (native module form)
      have hyΦ : ∀ (z : F.obj (op T')),
          y.app (op (Over.mk (h ≫ W.unop.hom))) z
            = (appAt F H (op T') (x (h ≫ W.unop.hom) hg) (op (Over.mk (𝟙 T')))).hom z := by
        intro z
        rw [hyamalg T' (h ≫ W.unop.hom) hg]
        simp only [FamilyOfElements.map_apply, toAmbient_app_apply]
        rfl
      have connect : (appAt F H (op T') (x (h ≫ W.unop.hom) hg) (op (Over.mk (𝟙 T')))).hom
          (F.map h.op m) = H.map h.op (y.app W m) := by
        rw [← hyΦ]; exact key m
      -- the scalar passes through, using `H`'s separatedness over the pulled-back sieve
      erw [PresheafOfModules.map_smul H h.op r (y.app W m), ← key (r • m),
          PresheafOfModules.map_smul F h.op r m]
      rw [hyΦ, map_smul, connect]) with hφ_def
  -- `φ` forgets back to `y`
  have htpφ : (PresheafOfModules.toPresheaf _).map φ = y := by
    rw [hφ_def]
    ext W z
    erw [PresheafOfModules.toPresheaf_map_app_apply]
  -- `φ` amalgamates `x`, uniquely (transport across the faithful, injective `toAmbient`)
  refine ⟨φ, fun Y f hf => ?_, fun t ht => ?_⟩
  · apply (PresheafOfModules.toPresheaf _).map_injective
    have e := NatTrans.naturality_apply (toAmbient F H) f.op φ
    simp only [toAmbient_app_apply] at e
    rw [htpφ] at e
    rw [e]
    exact hy f hf
  · apply (PresheafOfModules.toPresheaf _).map_injective
    rw [htpφ]
    exact yuniq _ (ht.map (toAmbient F H))

/-! ### Bricks (4)–(5): remaining I.1a content

Bricks (1)–(3) above are COMPLETE: `internalHom_isSheaf` is the classical sheaf-preservation theorem
(Stacks 17.16) for the internal hom of presheaves of modules, sorry/axiom-free.

**Remaining:** (4) repackage `internalHom F ((localInclusion α).obj H)` as `(localInclusion α).obj _`
(bookkeeping via `SheafOfModules.fullyFaithfulForget`), and (5) the short
`whiskerLeft`/`whiskerRight`/`IsMonoidal` port (≈40–60 LOC, using only the already-built `closedObj`
adjunction + piece I + this `internalHom_isSheaf`). See
`docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md` ("short remainder" §). -/

end InternalHomSheaf

end JacobianAlggeo
