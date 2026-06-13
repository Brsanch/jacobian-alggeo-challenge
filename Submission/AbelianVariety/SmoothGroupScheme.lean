import Submission.AbelianVariety.SmoothFaithfullyFlatDescent

/-!
# Smoothness of group schemes over an arbitrary field

Tower C — this **closes hole 4's smoothness half** as a usable theorem.

mathlib's `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` proves that a reduced,
locally-of-finite-presentation group scheme over an *algebraically closed* field is
smooth.  Round 1 (`SmoothFaithfullyFlatDescent.lean`) supplied the missing
descent direction — smoothness satisfies fpqc descent along a faithfully-flat base
change.  This file combines the two into the general-field statement

* `AlgebraicGeometry.smooth_of_grpObj` — **a geometrically reduced, locally-of-finite-
  presentation group scheme over *any* field `k` is smooth.**

The proof base-changes to `k̄ = AlgebraicClosure k`: there the group scheme is reduced
(geometric reducedness) and locally of finite presentation, hence smooth by the
algebraically-closed result; smoothness then descends along the faithfully-flat
`Spec k̄ → Spec k` (`= Surjective ⊓ Flat ⊓ QuasiCompact`, the descent class of round 1).

This is the smoothness input the abelian-variety hypotheses of holes 4, 5, 6 need:
the Jacobian (a geometrically integral — hence geometrically reduced — proper group
scheme) is smooth over the (not necessarily closed) base field `k`.

No `sorry`, no `axiom`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MorphismProperty

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}} (f : G ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] [GrpObj (Over.mk f)]

open scoped Obj in
set_option backward.isDefEq.respectTransparency false in
/-- **A geometrically reduced, locally-of-finite-presentation group scheme over an
arbitrary field `k` is smooth.**  Combines `smooth_of_grpObj_of_isAlgClosed`
(over `k̄`) with the faithfully-flat descent of smoothness (round 1). -/
theorem smooth_of_grpObj : Smooth f := by
  -- Base change to the algebraic closure `k̄`.
  let K' := AlgebraicClosure K
  let s : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  -- Over `k̄`, `G ×_k k̄ = pullback f s` is reduced (geometric reducedness), lfp, and a
  -- group scheme (the cartesian pullback functor preserves group objects), hence smooth.
  haveI hred : IsReduced (Limits.pullback f s) :=
    pullback_of_geometrically (‹GeometricallyReduced f›.geometrically_isReduced) K' s
  haveI hgrp : GrpObj (Over.mk (Limits.pullback.snd f s)) :=
    Functor.grpObjObj (F := Over.pullback s) (G := Over.mk f)
  have hsm : Smooth (Limits.pullback.snd f s) :=
    smooth_of_grpObj_of_isAlgClosed (Limits.pullback.snd f s)
  -- `s = Spec k̄ → Spec k` is faithfully flat, i.e. `Surjective ⊓ Flat ⊓ QuasiCompact`.
  have hfs := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K K'))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hqc : QuasiCompact s := inferInstance
  -- Smoothness descends along the faithfully-flat base change.
  exact of_pullback_snd_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hfs.2, hfs.1⟩, hqc⟩ hsm

end AlgebraicGeometry
