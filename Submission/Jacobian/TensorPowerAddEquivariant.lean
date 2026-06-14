import Submission.Jacobian.TensorPowerAdd

/-!
# `S_d × S_e ↪ S_{d+e}` equivariance of the merge isomorphism

The merge iso `tensorPowMulEquiv : A^{⊗d} ⊗ A^{⊗e} ≃ₐ A^{⊗(d+e)}` (brick (a)) intertwines the
factor-wise symmetric-group action `(σ, τ)` on `A^{⊗d} ⊗ A^{⊗e}` (`σ` permuting the first `d`
factors, `τ` the last `e`) with the **block permutation** `blockPerm σ τ ∈ S_{d+e}` (the image of
`(σ, τ)` under the subgroup embedding `S_d × S_e ↪ S_{d+e}`). This is brick (b) of the affine
addition map `Sym^d × Sym^e → Sym^{d+e}`: it is exactly what makes the merge iso carry the symmetric
tensors `(A^{⊗(d+e)})^{S_{d+e}}` into the `(S_d × S_e)`-invariants, the first step of dualizing the
divisor-concatenation map. Route-independent, mathlib-PR-shaped.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open scoped TensorProduct
open PiTensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The block embedding `S_d × S_e ↪ S_{d+e}`: `(σ, τ)` acts as `σ` on the first `d` indices and
`τ` on the last `e`, transported along `Fin d ⊕ Fin e ≃ Fin (d+e)`. -/
def blockPerm {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e)) :
    Equiv.Perm (Fin (d + e)) :=
  finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ τ)

theorem blockPerm_symm_castAdd {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e))
    (j : Fin d) : (blockPerm σ τ).symm (Fin.castAdd e j) = Fin.castAdd e (σ.symm j) := by
  rw [Equiv.symm_apply_eq, blockPerm, Equiv.permCongr_apply]
  simp

theorem blockPerm_symm_natAdd {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e))
    (j : Fin e) : (blockPerm σ τ).symm (Fin.natAdd d j) = Fin.natAdd d (τ.symm j) := by
  rw [Equiv.symm_apply_eq, blockPerm, Equiv.permCongr_apply]
  simp

/-- The combinatorial heart of the equivariance: precomposing `Fin.append a b` with the inverse
block permutation permutes the two blocks separately. -/
theorem append_comp_blockPerm_symm {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e))
    (a : Fin d → A) (b : Fin e → A) :
    (fun i => Fin.append a b ((blockPerm σ τ).symm i))
      = Fin.append (fun i => a (σ.symm i)) (fun i => b (τ.symm i)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [blockPerm_symm_castAdd, Fin.append_left, Fin.append_left]
  · rw [blockPerm_symm_natAdd, Fin.append_right, Fin.append_right]

/-- **Equivariance of the merge map.** The merge iso intertwines the factor-wise `(σ, τ)`-action on
`A^{⊗d} ⊗ A^{⊗e}` with the block permutation `blockPerm σ τ` on `A^{⊗(d+e)}`. -/
theorem mergeLinearEquiv_permEquiv {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e))
    (x : TensorPow R A d) (y : TensorPow R A e) :
    mergeLinearEquiv R A d e (permEquiv R A d σ x ⊗ₜ[R] permEquiv R A e τ y)
      = permEquiv R A (d + e) (blockPerm σ τ) (mergeLinearEquiv R A d e (x ⊗ₜ[R] y)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      rw [map_smul, map_smul, permEquiv_tprod, permEquiv_tprod,
        TensorProduct.smul_tmul_smul, map_smul, mergeLinearEquiv_tprod,
        TensorProduct.smul_tmul_smul, map_smul, mergeLinearEquiv_tprod, map_smul, permEquiv_tprod,
        append_comp_blockPerm_symm]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, TensorProduct.add_tmul, h₁, h₂]

/-- **Equivariance on the algebra iso.** The same statement phrased through `tensorPowMulEquiv`. -/
theorem tensorPowMulEquiv_permEquiv {d e : ℕ} (σ : Equiv.Perm (Fin d)) (τ : Equiv.Perm (Fin e))
    (x : TensorPow R A d) (y : TensorPow R A e) :
    tensorPowMulEquiv R A d e (permEquiv R A d σ x ⊗ₜ[R] permEquiv R A e τ y)
      = permEquiv R A (d + e) (blockPerm σ τ) (tensorPowMulEquiv R A d e (x ⊗ₜ[R] y)) :=
  mergeLinearEquiv_permEquiv R A σ τ x y

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
