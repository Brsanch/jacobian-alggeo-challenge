import Mathlib

/-!
# Faithfully-flat descent of smoothness

Tower C — the ring-theoretic input to hole 4's smoothness half.  mathlib has
`smooth_of_grpObj_of_isAlgClosed` (a reduced, locally-of-finite-presentation group
scheme over an algebraically closed field is smooth); upgrading it to a general
base field `k` funnels — for every route — through **faithfully-flat descent of
smoothness** (`Spec k̄ → Spec k` is faithfully flat).  mathlib has smoothness
*stable under base change* but not the descent direction; `Descent.lean`'s own TODO
notes even affine-morphism faithfully-flat descent is unbuilt.

This file supplies it.  `Algebra.FormallySmooth R S` is, at the pin, defined by two
module-level conditions — `Module.Projective S Ω[S⁄R]` and
`Subsingleton (Algebra.H1Cotangent R S)` — and **both descend along a faithfully-flat
base change** `R → T`:

* the projective half via the Kähler base-change `tensorKaehlerEquiv`, projectivity
  ⇒ flatness, faithfully-flat descent of flatness (`Module.Flat.of_flat_tensorProduct`),
  and `Module.projective_of_finitePresentation` (using that `Ω[S⁄R]` is finitely
  presented when `S` is a finitely-presented `R`-algebra);
* the subsingleton half via the cotangent base-change `tensorH1CotangentOfFlat` and
  `Module.subsingleton_tensorProduct_iff_right` (a faithfully-flat module reflects
  triviality of a tensor factor).

Hence `Algebra.Smooth` (= `FormallySmooth ∧ FinitePresentation`) codescends along
faithfully-flat ring maps — `RingHom.Smooth.codescendsAlong_faithfullyFlat`.

No `sorry`, no `axiom`.  Upstreamable to mathlib as-is.
-/

open TensorProduct

namespace Algebra

universe u

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

/-- **Faithfully-flat descent of formal smoothness** (given finite presentation, so
that projectivity of `Ω` can be recovered from flatness).  If `R → T` is faithfully
flat, `S` is a finitely-presented `R`-algebra, and `T ⊗[R] S` is formally smooth over
`T`, then `S` is formally smooth over `R`. -/
theorem FormallySmooth.of_faithfullyFlat_tensorProduct (T : Type u) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.FinitePresentation R S]
    [Algebra.FormallySmooth T (T ⊗[R] S)] : Algebra.FormallySmooth R S := by
  letI : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.FaithfullyFlat S (T ⊗[R] S) :=
    .of_linearEquiv S (S ⊗[R] T) (Algebra.TensorProduct.commRight R S T).symm.toLinearEquiv
  haveI : Algebra.IsPushout R T S (T ⊗[R] S) := TensorProduct.isPushout
  refine ⟨?_, ?_⟩
  · -- `Module.Projective S Ω[S⁄R]`
    let e := KaehlerDifferential.tensorKaehlerEquiv R T S (T ⊗[R] S)
    haveI : Module.Projective (T ⊗[R] S) ((T ⊗[R] S) ⊗[S] Ω[S⁄R]) :=
      Module.Projective.of_equiv e.symm
    haveI : Module.Flat S Ω[S⁄R] :=
      Module.Flat.of_flat_tensorProduct (R := S) (M := Ω[S⁄R]) (T ⊗[R] S)
    exact Module.Flat.projective_of_finitePresentation
  · -- `Subsingleton (Algebra.H1Cotangent R S)`
    have e := Algebra.tensorH1CotangentOfFlat (R := R) (S := S) T
    haveI : Subsingleton (T ⊗[R] Algebra.H1Cotangent R S) :=
      (Equiv.subsingleton_congr e.toEquiv).mpr inferInstance
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R T).mp inferInstance

/-- **Faithfully-flat descent of smoothness.**  If `R → T` is faithfully flat and
`T ⊗[R] S` is smooth over `T`, then `S` is smooth over `R`. -/
theorem Smooth.of_faithfullyFlat_tensorProduct (T : Type u) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.Smooth T (T ⊗[R] S)] : Algebra.Smooth R S := by
  haveI : Algebra.FinitePresentation R S :=
    .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  exact ⟨FormallySmooth.of_faithfullyFlat_tensorProduct T, inferInstance⟩

end Algebra

namespace RingHom

/-- **Smoothness codescends along faithfully-flat ring maps** (smoothness is fppf-local
on the base).  This is the ring-theoretic input that upgrades
`smooth_of_grpObj_of_isAlgClosed` to a general base field, via base change to `k̄`. -/
theorem Smooth.codescendsAlong_faithfullyFlat :
    CodescendsAlong Smooth FaithfullyFlat := by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact Algebra.Smooth.of_faithfullyFlat_tensorProduct S

end RingHom

namespace AlgebraicGeometry

open CategoryTheory MorphismProperty

/-- **Smoothness satisfies fpqc descent** — the scheme-level lift of
`RingHom.Smooth.codescendsAlong_faithfullyFlat` through
`HasRingHomProperty.descendsAlong`.  Smoothness of a morphism descends along a
surjective flat quasi-compact (i.e. faithfully-flat) base change.  Applied to
`Spec k̄ → Spec k`, this upgrades `smooth_of_grpObj_of_isAlgClosed` to a general
base field. -/
instance Smooth.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply HasRingHomProperty.descendsAlong (P := @Smooth) (P' := @Surjective ⊓ @Flat)
    (Q := RingHom.Smooth) (hQQ' := RingHom.Smooth.codescendsAlong_faithfullyFlat)
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · exact fun {_ _ f} h ↦ (flat_and_surjective_SpecMap_iff f).mp ⟨h.2, h.1⟩

end AlgebraicGeometry
