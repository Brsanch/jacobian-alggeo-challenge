import Submission.Jacobian.AffineSymmetricPower

/-!
# Finite type of the tensor power

If `A` is a finite-type `R`-algebra then the `d`-fold tensor power `A^{⊗d}` is a finite-type
`R`-algebra: the slot inclusions `singleAlgHom k : A →ₐ[R] A^{⊗d}` carry a finite generating
set of `A` to a finite generating set of `A^{⊗d}`, since every pure tensor
`tprod f = ∏ k, singleAlgHom k (f k)` lies in the subalgebra they generate and pure tensors
span. This makes the affine symmetric power's finiteness/properness unconditional.
-/

open scoped TensorProduct BigOperators
open PiTensorProduct

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (d : ℕ)

/-- A pure tensor is the product of its slot-wise inclusions:
`tprod f = ∏ k, singleAlgHom k (f k)`. -/
theorem tprod_eq_prod_singleAlgHom (f : Fin d → A) :
    tprod R f
      = ∏ k : Fin d, (singleAlgHom (R := R) (A := fun _ => A) k) (f k) := by
  have hpi : (∏ k : Fin d, (MonoidHom.mulSingle (fun _ : Fin d => A) k) (f k)) = f := by
    funext j
    rw [Finset.prod_apply]
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, Finset.prod_ite_eq]
  calc tprod R f
      = tprod R (∏ k : Fin d, (MonoidHom.mulSingle (fun _ : Fin d => A) k) (f k)) := by rw [hpi]
    _ = ∏ k : Fin d, tprod R ((MonoidHom.mulSingle (fun _ : Fin d => A) k) (f k)) :=
        map_prod (tprodMonoidHom R (A := fun _ : Fin d => A)) _ Finset.univ
    _ = ∏ k : Fin d, (singleAlgHom (R := R) (A := fun _ => A) k) (f k) := rfl

/-- The slot inclusions generate `A^{⊗d}` as an `R`-algebra. -/
theorem adjoin_range_singleAlgHom_eq_top :
    Algebra.adjoin R (⋃ k : Fin d,
        Set.range ((singleAlgHom (R := R) (A := fun _ => A) k) : A → TensorPow R A d)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    exact Subalgebra.prod_mem _ fun k _ =>
      Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨k, Set.mem_range_self _⟩)
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy

/-- **`A^{⊗d}` is of finite type over `R` when `A` is.** -/
instance tensorPow_finiteType [Algebra.FiniteType R A] :
    Algebra.FiniteType R (TensorPow R A d) := by
  classical
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType R A)
  refine ⟨Finset.univ.biUnion
      fun k : Fin d => S.image (singleAlgHom (R := R) (A := fun _ => A) k), ?_⟩
  rw [eq_top_iff, ← adjoin_range_singleAlgHom_eq_top R A d]
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨k, a, rfl⟩ := hx
  have ha : a ∈ Algebra.adjoin R (S : Set A) := by rw [hS]; exact Algebra.mem_top
  have h1 : (singleAlgHom (R := R) (A := fun _ => A) k) a
      ∈ Algebra.adjoin R ((singleAlgHom (R := R) (A := fun _ => A) k) '' (S : Set A)) := by
    rw [Algebra.adjoin_image]
    exact ⟨a, ha, rfl⟩
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨b, hb, rfl⟩
  refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩)
  exact Finset.mem_image.2 ⟨b, hb, rfl⟩

/-- The symmetric-power quotient map `Spec(A^{⊗d}) → Sym^d(Spec A)` is finite whenever `A` is
of finite type over `R` (unconditional version of `symPowQuotient_finite`). -/
theorem symPowQuotient_finite_of_finiteType [Algebra.FiniteType R A] :
    IsFinite (symPowQuotient R A d) :=
  symPowQuotient_finite R A d

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
