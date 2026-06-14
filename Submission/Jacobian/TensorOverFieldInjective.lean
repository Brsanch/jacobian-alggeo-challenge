import Submission.Jacobian.TensorPowerAddEquivariant

/-!
# Tensor of injective maps over a field is injective

Over a field `k`, every `k`-module is free, hence flat, so `TensorProduct.map f g` of two injective
`k`-linear maps is injective (`mathlib`'s `TensorProduct.map_injective_of_flat_flat`). The
specialization to subalgebra inclusions, `B ⊗_k C ↪ M ⊗_k N`, is the **corestriction
well-definedness** ingredient of the affine addition map
`(A^{⊗(d+e)})^{S_{d+e}} → (A^{⊗d})^{S_d} ⊗_k (A^{⊗e})^{S_e}` (`Sym^d × Sym^e → Sym^{d+e}`): the
equivariant image (brick (b)) lands in the `(S_d×S_e)`-invariants, and over a field that subspace IS
`(A^{⊗d})^{S_d} ⊗ (A^{⊗e})^{S_e}` (the invariants-commute-with-`⊗` step), into which the
corestriction is well-defined precisely because this inclusion is injective.

Route-independent, mathlib-PR-shaped.
-/

open scoped TensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

/-- Over a field, the tensor product of two injective `k`-linear maps is injective (both factors
are flat). -/
theorem tensorMap_injective_of_field {k : Type u} [Field k]
    {M N P Q : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (f : P →ₗ[k] M) (g : Q →ₗ[k] N) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  haveI : Module.Free k M := Module.Free.of_divisionRing k M
  haveI : Module.Flat k M := Module.Flat.of_free
  haveI : Module.Free k Q := Module.Free.of_divisionRing k Q
  haveI : Module.Flat k Q := Module.Flat.of_free
  exact TensorProduct.map_injective_of_flat_flat f g hf hg

/-- The inclusion `B ⊗_k C ↪ M ⊗_k N` of a tensor of subalgebras is injective over a field — the
corestriction-well-definedness ingredient of the affine addition map. -/
theorem subalgebra_tensorMap_val_injective {k : Type u} [Field k]
    {M N : Type u} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
    (B : Subalgebra k M) (C : Subalgebra k N) :
    Function.Injective (Algebra.TensorProduct.map B.val C.val) :=
  tensorMap_injective_of_field (k := k) B.val.toLinearMap C.val.toLinearMap
    Subtype.val_injective Subtype.val_injective

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
