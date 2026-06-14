import Mathlib
import Submission.Cohomology.IntegralKrullDim

/-!
# The dimension formula for finite-type domains over a field: `dim = trdeg`

For a finitely generated **domain** `A` over a field `k`, the Krull dimension equals the
transcendence degree of `A` over `k`:
`ringKrullDim A = trdeg k A`.

This upgrades `Submission.IntegralKrullDim.exists_ringKrullDim_eq_of_finiteType`
(`dim A = s`, with `s` the *non-canonical* rank of a Noether normalization
`k[X₁,…,X_s] ↪ A`) to the canonical birational invariant `trdeg k A`. It is the classical
dimension theorem (Atiyah–Macdonald ch. 11, Eisenbud Thm A, Stacks `00OW` + `030H`): the
dimension of an affine variety is the transcendence degree of its function field — i.e. the
**relative dimension** of the structure morphism. It is the keystone of the dimension half of
the `smooth ⇒ regular local` chain (Wall 2 of the genus / coherent-cohomology arc): for a
smooth curve `trdeg = 1 = rel dim`, pinning `dim A = 1`.

Proof. Noether normalization (`exists_integral_inj_algHom_of_fg`) gives an injective integral
`k[Fin s] ↪ A`. Krull-dimension invariance under injective integral extensions
(`Submission.IntegralKrullDim.ringKrullDim_eq_of_isIntegral_of_injective`) plus
`MvPolynomial.ringKrullDim_of_isNoetherianRing` gives `dim A = dim k[Fin s] = s`. Transcendence
degree is additive in the tower `k → k[Fin s] → A` (`trdeg_add_eq`, Stacks `030H`) with
`trdeg_{k[Fin s]} A = 0` (integral ⇒ algebraic, `trdeg_eq_zero`) and `trdeg_k k[Fin s] = s`
(`MvPolynomial.trdeg_of_isDomain`), so `trdeg k A = s` as well.

Route-independent, upstreamable mathlib content; certifies no challenge hole (foundation).
-/

open Cardinal

namespace Submission.DimensionFormula

open Submission.IntegralKrullDim

universe u

/-- **The dimension formula** for a finite-type domain over a field: there is a natural number
`s` that is simultaneously the Krull dimension and the transcendence degree. Stated in this
existence form to keep both invariants in their native types (`WithBot ℕ∞` and `Cardinal`)
while exhibiting their common natural-number value. -/
theorem exists_ringKrullDim_eq_trdeg (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ s : ℕ, ringKrullDim A = (s : WithBot ℕ∞) ∧ Algebra.trdeg k A = (s : Cardinal) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.isIntegral_def.mpr hint
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : FaithfulSMul k (MvPolynomial (Fin s) k) :=
    (faithfulSMul_iff_algebraMap_injective k (MvPolynomial (Fin s) k)).mpr <| by
      rw [MvPolynomial.algebraMap_eq]; exact MvPolynomial.C_injective (Fin s) k
  refine ⟨s, ?_, ?_⟩
  · rw [← ringKrullDim_eq_of_isIntegral_of_injective hinj,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  · have h1 : Algebra.trdeg k (MvPolynomial (Fin s) k) = (s : Cardinal) := by
      rw [MvPolynomial.trdeg_of_isDomain]; simp
    have h2 : Algebra.trdeg (MvPolynomial (Fin s) k) A = 0 := trdeg_eq_zero
    have h3 := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := A)
    rw [h1, h2, add_zero] at h3
    exact h3.symm

/-- The dimension formula as a direct equality. The transcendence degree of a finite-type
domain over a field is finite, so its `Cardinal.toNat` recovers the Krull dimension. -/
theorem ringKrullDim_eq_trdeg_toNat (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  obtain ⟨s, hdim, htr⟩ := exists_ringKrullDim_eq_trdeg k A
  rw [hdim, htr, Cardinal.toNat_natCast]

end Submission.DimensionFormula
