import Submission.Jacobian.AffineQuotient
import Submission.Jacobian.TensorPowerPermAction

/-!
# The affine symmetric power `Sym^d(Spec A) = Spec((A^{⊗d})^{S_d})`

Instantiates the generic affine finite-group quotient (`AffineQuotient`) at the
commutative `R`-algebra `B = A^{⊗d}` (`TensorPowerPermAction`) and the symmetric group
`G = S_d = Equiv.Perm (Fin d)` permuting the tensor factors, to construct the **affine
symmetric power** `Sym^d(Spec A)` of an affine scheme `Spec A`, with its quotient map and the
defining properties:

* `symPowQuotient_isIntegralHom` — the map `Spec(A^{⊗d}) → Sym^d(Spec A)` is integral
  (hence universally closed);
* `symPowQuotient_finite`/`_isProper` — finite (hence proper) when `A^{⊗d}` is of finite type;
* `symPowQuotient_invariant` — `S_d`-invariance of the quotient map;
* `symPow_exists_unique` — the categorical-quotient universal property.

This is the affine model of route-doc milestone M3 (`Sym^d C = C^d/S_d` for a curve `C`); the
projective/curve case glues these affine pieces (route-doc P3–P5, the remaining walls). The
identification `Spec(A^{⊗d}) ≅ (Spec A)^d` (the `d`-fold fibre product over `Spec R`) is the
affine self-product. Route-independent, mathlib-PR-shaped.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.JacobianChallenge.SymmetricPower

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (d : ℕ)

/-- The affine symmetric power `Sym^d(Spec A) = Spec((A^{⊗d})^{S_d})`: the finite-group
quotient of the affine `d`-fold self-product `Spec(A^{⊗d})` by the symmetric group `S_d`
permuting the tensor factors. -/
noncomputable def affineSymmetricPower : Scheme.{u} :=
  AffineQuotient.affineQuotient R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The quotient morphism `Spec(A^{⊗d}) → Sym^d(Spec A)`. -/
noncomputable def symPowQuotient :
    Spec (CommRingCat.of (TensorPow R A d)) ⟶ affineSymmetricPower R A d :=
  AffineQuotient.quotientMap R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The symmetric-power quotient map is integral (`A^{⊗d}` is integral over its `S_d`-invariants
since `S_d` is finite). -/
theorem symPowQuotient_isIntegralHom : IsIntegralHom (symPowQuotient R A d) :=
  AffineQuotient.quotientMap_isIntegralHom R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The symmetric-power quotient map is universally closed. -/
instance : UniversallyClosed (symPowQuotient R A d) :=
  AffineQuotient.instUniversallyClosed R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The symmetric-power quotient map is finite when `A^{⊗d}` is of finite type over `R`. -/
theorem symPowQuotient_finite [Algebra.FiniteType R (TensorPow R A d)] :
    IsFinite (symPowQuotient R A d) :=
  AffineQuotient.quotientMap_finite R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The symmetric-power quotient map is proper when finite. -/
theorem symPowQuotient_isProper [Algebra.FiniteType R (TensorPow R A d)] :
    IsProper (symPowQuotient R A d) :=
  AffineQuotient.quotientMap_isProper R (TensorPow R A d) (Equiv.Perm (Fin d))

/-- The quotient map is invariant under the `S_d`-action permuting the tensor factors:
`σ̃ ≫ π = π` for every permutation `σ`. -/
theorem symPowQuotient_invariant (σ : Equiv.Perm (Fin d)) :
    AffineQuotient.specAction R (TensorPow R A d) (Equiv.Perm (Fin d)) σ ≫ symPowQuotient R A d
      = symPowQuotient R A d :=
  AffineQuotient.specAction_comp_quotientMap R (TensorPow R A d) (Equiv.Perm (Fin d)) σ

/-- **Universal property of `Sym^d(Spec A)`:** an `S_d`-invariant morphism `Spec(A^{⊗d}) → Spec R'`
(its dual ring map has image fixed by every permutation of the tensor factors) factors uniquely
through the symmetric-power quotient. -/
theorem symPow_exists_unique {R' : Type u} [CommRing R']
    (φ : CommRingCat.of R' ⟶ CommRingCat.of (TensorPow R A d))
    (hφ : ∀ (σ : Equiv.Perm (Fin d)) (x : R'), σ • φ.hom x = φ.hom x) :
    ∃! ψ : affineSymmetricPower R A d ⟶ Spec (CommRingCat.of R'),
      symPowQuotient R A d ≫ ψ = Spec.map φ :=
  AffineQuotient.exists_unique_lift_of_invariant R (TensorPow R A d) (Equiv.Perm (Fin d)) φ hφ

end AlgebraicGeometry.JacobianChallenge.SymmetricPower
