import Mathlib

/-!
# The symmetric-group action on a tensor power of a commutative algebra

For a commutative `R`-algebra `A`, the `d`-fold tensor power `A^{⊗d} = ⨂[R] (_ : Fin d), A` is
a commutative `R`-algebra (`PiTensorProduct.instCommRing`). The symmetric group
`Equiv.Perm (Fin d)` permutes the tensor factors; this file upgrades the linear
reindexing equivalence `PiTensorProduct.reindex` to a **`MulSemiringAction`** of
`Equiv.Perm (Fin d)` on `A^{⊗d}` by `R`-algebra automorphisms (with `SMulCommClass`), so that
the invariant subalgebra `(A^{⊗d})^{S_d}` and hence the affine symmetric power
`Sym^d(Spec A) = Spec((A^{⊗d})^{S_d})` can be formed via `InvariantFiniteness`.

mathlib has `reindex` only as a `LinearEquiv` (the ring/permutation action is a stated TODO
in `LinearAlgebra/TensorPower/Symmetric.lean`); the multiplicativity is proved here by
induction on pure tensors. Route-independent, mathlib-PR-shaped.
-/

open scoped TensorProduct
open PiTensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (d : ℕ)

/-- The `d`-fold tensor power `A^{⊗d}`, a commutative `R`-algebra. -/
abbrev TensorPow : Type u := ⨂[R] (_ : Fin d), A

/-- The `R`-linear automorphism of `A^{⊗d}` permuting the tensor factors by `σ`. -/
noncomputable def permEquiv (σ : Equiv.Perm (Fin d)) :
    TensorPow R A d ≃ₗ[R] TensorPow R A d :=
  PiTensorProduct.reindex R (fun _ => A) σ

@[simp] theorem permEquiv_tprod (σ : Equiv.Perm (Fin d)) (f : Fin d → A) :
    permEquiv R A d σ (tprod R f) = tprod R (fun i => f (σ.symm i)) :=
  PiTensorProduct.reindex_tprod σ f

/-- The permutation map preserves multiplication (proved by induction on pure tensors). -/
theorem permEquiv_mul (σ : Equiv.Perm (Fin d)) (x y : TensorPow R A d) :
    permEquiv R A d σ (x * y) = permEquiv R A d σ x * permEquiv R A d σ y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      have hfun : (fun i => (a * b) (σ.symm i))
          = (fun i => a (σ.symm i)) * (fun i => b (σ.symm i)) := by
        funext i; simp [Pi.mul_apply]
      simp only [smul_tprod_mul_smul_tprod, map_smul, permEquiv_tprod, hfun]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]

/-- The permutation map preserves the unit. -/
@[simp] theorem permEquiv_one (σ : Equiv.Perm (Fin d)) :
    permEquiv R A d σ (1 : TensorPow R A d) = 1 := by
  rw [PiTensorProduct.one_def, permEquiv_tprod]
  rw [show (fun i => (1 : Fin d → A) (σ.symm i)) = (1 : Fin d → A) from rfl, ← PiTensorProduct.one_def]

/-- **The symmetric-group action on `A^{⊗d}` by `R`-algebra automorphisms.** -/
noncomputable instance permAction : MulSemiringAction (Equiv.Perm (Fin d)) (TensorPow R A d) where
  smul σ x := permEquiv R A d σ x
  one_smul x := by
    show permEquiv R A d 1 x = x
    rw [permEquiv, show (1 : Equiv.Perm (Fin d)) = Equiv.refl (Fin d) from rfl,
      PiTensorProduct.reindex_refl]
    rfl
  mul_smul σ τ x := by
    show permEquiv R A d (σ * τ) x = permEquiv R A d σ (permEquiv R A d τ x)
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      have hfun : (fun i => f ((σ * τ).symm i)) = (fun i => f (τ.symm (σ.symm i))) := rfl
      simp only [map_smul, permEquiv_tprod, hfun]
    | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  smul_zero σ := map_zero (permEquiv R A d σ)
  smul_add σ x y := map_add (permEquiv R A d σ) x y
  smul_one σ := permEquiv_one R A d σ
  smul_mul σ x y := permEquiv_mul R A d σ x y

/-- The symmetric-group action commutes with the `R`-scalar action (`permEquiv` is `R`-linear),
so the invariant subalgebra `(A^{⊗d})^{S_d}` is a well-defined `R`-subalgebra. -/
instance : SMulCommClass (Equiv.Perm (Fin d)) R (TensorPow R A d) where
  smul_comm σ r x := map_smul (permEquiv R A d σ) r x

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
