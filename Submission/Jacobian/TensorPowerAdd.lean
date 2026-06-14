import Submission.Jacobian.TensorPowerPermAction

/-!
# The merge algebra isomorphism `A^{⊗d} ⊗ A^{⊗e} ≃ₐ A^{⊗(d+e)}`

For a commutative `R`-algebra `A`, the tensor powers `A^{⊗d}`, `A^{⊗e}`, `A^{⊗(d+e)}` are
commutative `R`-algebras (`PiTensorProduct.instCommRing`). This file builds the **algebra
isomorphism**
`tensorPowMulEquiv : A^{⊗d} ⊗[R] A^{⊗e} ≃ₐ[R] A^{⊗(d+e)}`
which concatenates tensor factors (`tprod a ⊗ₜ tprod b ↦ tprod (Fin.append a b)`).

The underlying `LinearEquiv` `mergeLinearEquiv` is `tmulEquiv ≫ reindex finSumFinEquiv` (the same
composite mathlib bundles as `TensorPower.mulEquiv`, but re-built here at the `TensorPow` types so
instances are pinned). Its multiplicativity for the *diagonal* `CommRing` structure (mathlib only
relates the composite to the *graded* product `ₜ*`) is proved here by reduction to pure tensors,
upgrading the `LinearEquiv` to an `AlgEquiv` via `AlgEquiv.ofLinearEquiv`.

This is brick (a) of the affine **addition / monoid map** `Sym^d × Sym^e → Sym^{d+e}` (the
algebraic heart of the group law, hole 3): on coordinate rings the addition map dualizes to
`(A^{⊗(d+e)})^{S_{d+e}} → (A^{⊗d})^{S_d} ⊗ (A^{⊗e})^{S_e}`, the restriction of this merge iso to
symmetric tensors. The `S_d × S_e ↪ S_{d+e}` equivariance and the over-a-field
invariants-commute-with-`⊗` step are the follow-up bricks. Route-independent, mathlib-PR-shaped.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open scoped TensorProduct
open PiTensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The merge `LinearEquiv` `A^{⊗d} ⊗ A^{⊗e} ≃ₗ A^{⊗(d+e)}`: `tmulEquiv` followed by reindexing
along `Fin d ⊕ Fin e ≃ Fin (d+e)`. (Same composite as `TensorPower.mulEquiv`, re-typed at
`TensorPow`.) -/
noncomputable def mergeLinearEquiv (d e : ℕ) :
    TensorPow R A d ⊗[R] TensorPow R A e ≃ₗ[R] TensorPow R A (d + e) :=
  (tmulEquiv R A).trans (reindex R (fun _ => A) finSumFinEquiv)

/-- `mergeLinearEquiv` on a pair of pure tensors concatenates the index functions. -/
theorem mergeLinearEquiv_tprod (d e : ℕ) (a : Fin d → A) (b : Fin e → A) :
    mergeLinearEquiv R A d e (tprod R a ⊗ₜ[R] tprod R b) = tprod R (Fin.append a b) := by
  simp only [mergeLinearEquiv, LinearEquiv.trans_apply, tmulEquiv_apply, reindex_tprod]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [finSumFinEquiv_symm_apply_castAdd, Fin.append_left, Sum.elim_inl]
  · rw [finSumFinEquiv_symm_apply_natAdd, Fin.append_right, Sum.elim_inr]

/-- `Fin.append` distributes over the pointwise product of index functions. -/
theorem append_mul {d e : ℕ} (a a' : Fin d → A) (b b' : Fin e → A) :
    Fin.append (a * a') (b * b') = (Fin.append a b) * (Fin.append a' b') := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left, Pi.mul_apply]
  · simp [Fin.append_right, Pi.mul_apply]

/-- `Fin.append` of the constant-one functions is the constant-one function. -/
theorem append_one {d e : ℕ} : Fin.append (1 : Fin d → A) (1 : Fin e → A) = 1 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

/-- The bilinear core of multiplicativity: `mergeLinearEquiv` carries the product of two pure-tmul
elements to the product of their images. Proved by reduction to pure tensors. -/
theorem mergeLinearEquiv_tmul_mul (d e : ℕ) (xd yd : TensorPow R A d) (xe ye : TensorPow R A e) :
    mergeLinearEquiv R A d e ((xd * yd) ⊗ₜ[R] (xe * ye))
      = mergeLinearEquiv R A d e (xd ⊗ₜ[R] xe) * mergeLinearEquiv R A d e (yd ⊗ₜ[R] ye) := by
  induction xd using PiTensorProduct.induction_on with
  | smul_tprod rd ad =>
    induction xe using PiTensorProduct.induction_on with
    | smul_tprod re ae =>
      induction yd using PiTensorProduct.induction_on with
      | smul_tprod sd bd =>
        induction ye using PiTensorProduct.induction_on with
        | smul_tprod se be =>
          rw [smul_tprod_mul_smul_tprod, smul_tprod_mul_smul_tprod,
            TensorProduct.smul_tmul_smul, map_smul, mergeLinearEquiv_tprod,
            TensorProduct.smul_tmul_smul, map_smul, mergeLinearEquiv_tprod,
            TensorProduct.smul_tmul_smul, map_smul, mergeLinearEquiv_tprod,
            smul_mul_smul_comm, tprod_mul_tprod, ← append_mul]
          congr 1
          ring
        | add ye₁ ye₂ h₁ h₂ =>
          simp only [mul_add, TensorProduct.tmul_add, map_add, h₁, h₂]
      | add yd₁ yd₂ h₁ h₂ =>
        simp only [mul_add, TensorProduct.add_tmul, map_add, h₁, h₂]
    | add xe₁ xe₂ h₁ h₂ =>
      simp only [add_mul, TensorProduct.tmul_add, map_add, h₁, h₂]
  | add xd₁ xd₂ h₁ h₂ =>
    simp only [add_mul, TensorProduct.add_tmul, map_add, h₁, h₂]

/-- Diagonal-`CommRing` multiplicativity of `mergeLinearEquiv`. -/
theorem mergeLinearEquiv_mul (d e : ℕ) (x y : TensorPow R A d ⊗[R] TensorPow R A e) :
    mergeLinearEquiv R A d e (x * y)
      = mergeLinearEquiv R A d e x * mergeLinearEquiv R A d e y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
  | tmul xd xe =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | tmul yd ye =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact mergeLinearEquiv_tmul_mul R A d e xd yd xe ye

/-- `mergeLinearEquiv` preserves the unit (for the diagonal `CommRing` structure). -/
theorem mergeLinearEquiv_one (d e : ℕ) :
    mergeLinearEquiv R A d e (1 : TensorPow R A d ⊗[R] TensorPow R A e) = 1 := by
  have h1d : (1 : TensorPow R A d) = PiTensorProduct.tprod R 1 := rfl
  have h1e : (1 : TensorPow R A e) = PiTensorProduct.tprod R 1 := rfl
  rw [Algebra.TensorProduct.one_def, h1d, h1e, mergeLinearEquiv_tprod, append_one]
  rfl

/-- **The merge algebra isomorphism** `A^{⊗d} ⊗[R] A^{⊗e} ≃ₐ[R] A^{⊗(d+e)}`: concatenation of
tensor factors, an `R`-algebra isomorphism. -/
noncomputable def tensorPowMulEquiv (d e : ℕ) :
    TensorPow R A d ⊗[R] TensorPow R A e ≃ₐ[R] TensorPow R A (d + e) :=
  AlgEquiv.ofLinearEquiv (mergeLinearEquiv R A d e)
    (mergeLinearEquiv_one R A d e) (mergeLinearEquiv_mul R A d e)

@[simp] theorem tensorPowMulEquiv_tprod (d e : ℕ) (a : Fin d → A) (b : Fin e → A) :
    tensorPowMulEquiv R A d e (tprod R a ⊗ₜ[R] tprod R b) = tprod R (Fin.append a b) :=
  mergeLinearEquiv_tprod R A d e a b

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
