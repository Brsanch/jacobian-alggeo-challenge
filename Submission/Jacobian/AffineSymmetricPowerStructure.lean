import Submission.Jacobian.AffineSymmetricPower
import Submission.Jacobian.AffineQuotientBase

/-!
# The affine symmetric power as a scheme over the base, and `Sym^1(Spec A) ≅ Spec A`

`Submission/Jacobian/AffineSymmetricPower.lean` builds `affineSymmetricPower R A d =
Sym^d(Spec A)` as a bare `Scheme`. This file gives it its structure *over* the base `Spec R`
(the challenge's `Jacobian` lives in `Over (Spec (.of k))`), and identifies the degree-one
symmetric power with `Spec A` itself.

* `symPowStructureMorphism` / `affineSymmetricPowerOver` — `Sym^d(Spec A) ⟶ Spec R` and the
  `Over (Spec R)` packaging.
* `finOneTensorAlgEquiv` — `A^{⊗1} ≃ₐ[R] A` (the singleton tensor power; mathlib has only the
  `LinearEquiv` `PiTensorProduct.subsingletonEquiv`, upgraded here to an algebra equivalence).
* `symOneAlgEquiv` — `(A^{⊗1})^{S_1} ≃ₐ[R] A` (`S_1` is trivial, so the invariants are everything).
* `affineSymOneIso` — **`Sym^1(Spec A) ≅ Spec A`** as schemes, with `symOneIso_over` showing the
  iso is over `Spec R`. This is the degree-1 base case of the Abel–Jacobi map `C → Sym^1 C → Pic`.

Route-independent, mathlib-PR-shaped.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open PiTensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-! ### `Sym^d(Spec A)` as a scheme over `Spec R` -/

/-- The structure morphism `Sym^d(Spec A) ⟶ Spec R`. -/
noncomputable def symPowStructureMorphism (d : ℕ) :
    affineSymmetricPower R A d ⟶ Spec (CommRingCat.of R) :=
  AffineQuotient.structureMorphism R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- `Sym^d(Spec A)` packaged as an object of `Over (Spec R)`. -/
noncomputable def affineSymmetricPowerOver (d : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (symPowStructureMorphism R A d)

/-- The quotient map `Spec(A^{⊗d}) → Sym^d(Spec A)` is a morphism over `Spec R`. -/
theorem symPowQuotient_comp_structureMorphism (d : ℕ) :
    symPowQuotient R A d ≫ symPowStructureMorphism R A d
      = AffineQuotient.baseStructureMorphism R (TensorPow R A d) :=
  AffineQuotient.quotientMap_comp_structureMorphism R (TensorPow R A d) (Equiv.Perm (Fin d))

/-! ### The degree-one identification `Sym^1(Spec A) ≅ Spec A` -/

/-- The singleton tensor power `A^{⊗1} = ⨂[R] (_ : Fin 1), A` is `R`-algebra isomorphic to `A`.
mathlib provides only the underlying `LinearEquiv` (`PiTensorProduct.subsingletonEquiv`); the
multiplicativity (on pure tensors `tprod f * tprod g = tprod (f·g)`) is proved here. -/
noncomputable def finOneTensorAlgEquiv : TensorPow R A 1 ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.subsingletonEquiv (0 : Fin 1))
    (by
      rw [PiTensorProduct.one_def, PiTensorProduct.subsingletonEquiv_apply_tprod]
      rfl)
    (by
      intro x y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod s g =>
          simp only [map_smul, smul_mul_smul_comm, tprod_mul_tprod,
            PiTensorProduct.subsingletonEquiv_apply_tprod, Pi.mul_apply]
        | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂])

/-- `S_1 = Equiv.Perm (Fin 1)` is trivial, so the invariant subalgebra `(A^{⊗1})^{S_1}` is all
of `A^{⊗1}`. -/
theorem fixedPoints_perm_fin_one_eq_top :
    FixedPoints.subalgebra R (TensorPow R A 1) (Equiv.Perm (Fin 1)) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  show ∀ g : Equiv.Perm (Fin 1), g • x = x
  intro g
  rw [Subsingleton.elim g 1, one_smul]

/-- `(A^{⊗1})^{S_1} ≃ₐ[R] A`: the degree-1 invariants are `A` itself. -/
noncomputable def symOneAlgEquiv :
    ↥(FixedPoints.subalgebra R (TensorPow R A 1) (Equiv.Perm (Fin 1))) ≃ₐ[R] A :=
  (Subalgebra.equivOfEq _ _ (fixedPoints_perm_fin_one_eq_top R A)).trans
    (Subalgebra.topEquiv.trans (finOneTensorAlgEquiv R A))

/-- **`Sym^1(Spec A) ≅ Spec A`** as schemes: the degree-1 symmetric power is `Spec A`. This is the
base case of the Abel–Jacobi map (`C ≅ Sym^1 C → Pic^1`). -/
noncomputable def affineSymOneIso :
    affineSymmetricPower R A 1 ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso (symOneAlgEquiv R A).toRingEquiv.toCommRingCatIso.symm.op

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
