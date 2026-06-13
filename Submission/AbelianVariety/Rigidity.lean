import Submission.AbelianVariety.PointedDiff

/-!
# Rigidity: a pointed morphism of abelian varieties is a homomorphism

Tower C, layer 2.  This supplies the geometric input that
`Submission/AbelianVariety/PointedDiff.lean` reduces hole 9 to: the
pointed-difference map `pointedDiff h : A ⊗ A ⟶ B` of a pointed morphism
`h : A ⟶ B` between abelian varieties is the **constant** unit map, hence (by
`isMonHom_iff_pointedDiff_eq`) `h` is a group-object homomorphism.

The proof is the rigidity lemma (Mumford, *Abelian Varieties* §4).  We follow
mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
(the commutativity-of-proper-group-schemes argument, `Group/Abelian.lean`) almost
verbatim: that proof shows the *commutator* `G ⊗ G ⟶ G` is constant; we run the
same Zariski's-Main-Theorem + completeness argument on the endomorphism-like map
`gam = lift (fst A A) (pointedDiff h) : A ⊗ A ⟶ A ⊗ B`, whose constancy on the
axis `{e} × A` (proved formally in layer 1, `lift_one_id_pointedDiff`) propagates
to constancy everywhere because `A` is complete (proper) and `A ⊗ A` is integral.

The alg-closed case is then descended to a general base field exactly as
`isCommMonObj_of_isProper_of_geometricallyIntegral` descends commutativity.

No `sorry`, no `axiom`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AbelianVariety

universe u

open AlgebraicGeometry

variable {K : Type u} [Field K]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity, algebraically closed case.**  For abelian varieties `A`, `B` over
an algebraically closed field `K` (with `A ⊗ A` integral), a pointed morphism
`h : A ⟶ B` (i.e. `η[A] ≫ h = η[B]`) has constant pointed-difference map. -/
theorem pointedDiff_eq_toUnit_η_of_isAlgClosed [IsAlgClosed K]
    (A B : Over (Spec (.of K))) [IsProper A.hom] [GrpObj A] [IsIntegral (A ⊗ A).left]
    [IsProper B.hom] [GrpObj B] (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    pointedDiff h = toUnit _ ≫ η := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty A.left := ⟨η[A].left point⟩
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : JacobsonSpace (A ⊗ A).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (A ⊗ A).hom
  have : Surjective A.hom := ⟨Function.surjective_to_subsingleton (α := A.left) (β := Spec _) _⟩
  have : IsProper (fst A A).left := by dsimp; infer_instance
  have : Surjective (fst A A).left := by dsimp; infer_instance
  have hsepB : IsSeparated (fst A B).left := by dsimp; infer_instance
  have hlftB : LocallyOfFiniteType (fst A B).left := by dsimp; infer_instance
  have : IsProper ((pointedDiff h).left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift η[A] η[B]).left ≫ (fst A B).left) := by
    simpa using inferInstanceAs (IsClosedImmersion η[A].left)
  have : IsClosedImmersion (lift η[A] η[B]).left := .of_comp _ (g := (fst A B).left)
  let gam : A ⊗ A ⟶ A ⊗ B := lift (fst _ _) (pointedDiff h)
  have hgamfst : gam ≫ fst A B = fst A A := by simp [gam]
  have : IsProper (gam.left ≫ (fst A B).left) := by
    rw [← Over.comp_left, hgamfst]; infer_instance
  have : IsProper gam.left := .of_comp _ (fst A B).left
  -- It suffices to check that `pointedDiff h` is constantly `1`.
  refine Over.OverMorphism.ext ?_
  have H : gam.left '' ((fst A A).left ⁻¹' {η[A].left point}) ⊆ {(lift η[A] η[B]).left point} := by
    rw [Set.image_subset_iff, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.diff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[A] η[B]).left.isClosedMap _ hpoint).preimage gam.left.continuous).isOpen_compl
      · exact (η[A].left.isClosedMap _ hpoint).preimage (fst A A).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (A ⊗ A).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ A := lift (𝟙 _) (Over.homMk c hc ≫ snd A A)
    have hcfst : c ≫ pullback.fst A.hom A.hom = η[A].left :=
      ext_of_apply_closedPoint_eq A.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (η[A] ▷ A).left := by dsimp; ext <;> simp [fc, S, hcfst]
    have H₂ : fc ≫ η[A] ▷ A ≫ gam = lift η[A] η[B] := by
      ext1
      · simp [fc, gam, S]
      · simpa [fc, gam, S] using lift_unit_pointedDiff h hone (Over.homMk c hc ≫ snd A A)
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gam.left (fst A B).left (η[A].left point) (by
      have hcomp : gam.left ≫ (fst A B).left = (fst A A).left := by rw [← Over.comp_left, hgamfst]
      rw [show ((gam.left ≫ (fst A B).left) ⁻¹' {η[A].left point})
          = ((fst A A).left ⁻¹' {η[A].left point}) by rw [hcomp]]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((fst A B).left ⁻¹' {x.1} ∩ Set.range ⇑gam.left).Finite := by
    refine ((((gam.left.imageι ≫ (fst A B).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gam.left.imageι)).subset ?_
    have hUx : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← hUx, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst A B).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gam.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq B.hom _
    ((fst A A).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst A A).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst A A).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst A A).left y} := by simpa using (fst A A).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ A := Over.homMk (pointOfClosedPoint A.hom _ hx) (by simp)
    -- the source closed point `(x, e)` on the `A × {e}` axis through `y`'s fibre
    let xs : (A ⊗ A).left := (fst A A ≫ (ρ_ _).inv ≫ A ◁ η[A]).left y
    -- `gam` is constant on the fibre `{x} × A`, so `gam y = gam (x, e)`
    have hval : gam.left y = gam.left xs := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst A A).left.continuous).isLocallyClosed ?_ gam.left.continuous
        gam.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gam])) ?_ ?_
      · let α : A ⊗ A ⟶ A ⊗ A := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert ((IrreducibleSpace.isIrreducible_univ _).image α.left
          α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · exact ⟨xs, subset_closure (by
          simp [xs, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]), rfl⟩
    -- and on the axis `gam (x, e)`'s `B`-component is `e` (`pointedDiff` vanishes there)
    have key : gam ≫ snd A B = pointedDiff h := lift_snd _ _
    have hσ : (fst A A ≫ (ρ_ A).inv ≫ A ◁ η[A]) ≫ pointedDiff h = toUnit _ ≫ η := by
      simp only [Category.assoc]
      rw [whiskerLeft_η_pointedDiff h hone]
      simp
    have step1 : (pointedDiff h).left y = (snd A B).left (gam.left y) := by
      rw [← key, Over.comp_left, Scheme.Hom.comp_apply]
    have step2 : (pointedDiff h).left xs = (snd A B).left (gam.left xs) := by
      rw [← key, Over.comp_left, Scheme.Hom.comp_apply]
    have step3 : (pointedDiff h).left xs
        = (toUnit (A ⊗ A) ≫ η[B] : (A ⊗ A) ⟶ B).left y := by
      show (pointedDiff h).left ((fst A A ≫ (ρ_ A).inv ≫ A ◁ η[A]).left y) = _
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hσ]
    rw [step1, hval, ← step2, step3]
  · simp

/-- **Rigidity corollary, algebraically closed case** (Mumford, *Abelian Varieties* §4):
a pointed morphism of abelian varieties over an algebraically closed field — a
morphism `h : A ⟶ B` sending the identity to the identity (`η[A] ≫ h = η[B]`) — is a
group-object homomorphism. -/
theorem isMonHom_of_pointed_of_isAlgClosed [IsAlgClosed K]
    (A B : Over (Spec (.of K))) [IsProper A.hom] [GrpObj A] [IsIntegral (A ⊗ A).left]
    [IsProper B.hom] [GrpObj B] (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    IsMonHom h :=
  (isMonHom_iff_pointedDiff_eq h hone).mpr
    (pointedDiff_eq_toUnit_η_of_isAlgClosed A B h hone)

open scoped Obj in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity, general base field** (descent of `pointedDiff_eq_toUnit_η_of_isAlgClosed`
along `Spec k̄ → Spec k`): for abelian varieties `A`, `B` over an arbitrary field `k`
with `A` geometrically integral, a pointed morphism `h : A ⟶ B` has constant
pointed-difference map.  The descent mirrors
`isCommMonObj_of_isProper_of_geometricallyIntegral`. -/
theorem pointedDiff_eq_toUnit_η_of_geometricallyIntegral
    (A B : Over (Spec (.of K))) [IsProper A.hom] [GrpObj A] [GeometricallyIntegral A.hom]
    [IsProper B.hom] [GrpObj B] (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    pointedDiff h = toUnit _ ≫ η := by
  let fK := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback fK
  let A' := F.obj A
  let B' := F.obj B
  have : IsProper A'.hom := by dsimp [A', F]; infer_instance
  have : IsProper B'.hom := by dsimp [B', F]; infer_instance
  have : IsIntegral (A' ⊗ A').left := by dsimp [A', F]; infer_instance
  let : GrpObj A' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have hone' : η[A'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Category.assoc, ← Functor.map_comp, hone, ← Functor.obj.η_def]
  have key := pointedDiff_eq_toUnit_η_of_isAlgClosed A' B' (F.map h) hone'
  apply F.map_injective
  rw [← cancel_epi (Functor.Monoidal.μIso F A A).hom]
  dsimp only [pointedDiff] at key ⊢
  simpa only [Functor.Monoidal.μIso_hom, Functor.map_mul, Functor.map_inv', Functor.map_comp,
    comp_mul, GrpObj.comp_inv, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd,
    Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd_assoc, Functor.obj.μ_def, one_eq_one,
    comp_one, Functor.map_one, Category.assoc] using key

/-- **Pointed morphisms of abelian varieties are homomorphisms**, over an arbitrary
field `k` (Mumford, *Abelian Varieties* §4).  This is the rigidity input hole 9's
uniqueness consumes. -/
theorem isMonHom_of_pointed_of_geometricallyIntegral
    (A B : Over (Spec (.of K))) [IsProper A.hom] [GrpObj A] [GeometricallyIntegral A.hom]
    [IsProper B.hom] [GrpObj B] (h : A ⟶ B) (hone : η[A] ≫ h = η[B]) :
    IsMonHom h :=
  (isMonHom_iff_pointedDiff_eq h hone).mpr
    (pointedDiff_eq_toUnit_η_of_geometricallyIntegral A B h hone)

end AbelianVariety
