import Submission.Jacobian.AffineQuotient

/-!
# The affine finite-group quotient as a scheme over the base `Spec R`

`Submission/Jacobian/AffineQuotient.lean` builds the affine quotient `affineQuotient R B G =
Spec(B^G)` as a bare `Scheme`. For the Jacobian challenge every object lives over the base
field (`Over (Spec (.of k))`), so the quotient must be a scheme *over* `Spec R`. This file
adds the **structure morphism** `Spec(B^G) ⟶ Spec R` (dual to `algebraMap R (B^G)`, which
exists because `B^G` is an `R`-subalgebra of `B`) and the compatibility statement that the
quotient map `π : Spec B → Spec(B^G)` is a morphism *over* `Spec R`:

* `structureMorphism` — `Spec(B^G) ⟶ Spec R`, the affine quotient as a `Spec R`-scheme;
* `quotientMap_comp_structureMorphism` — `π ≫ (structure of B^G) = (structure of B)`, i.e. the
  quotient triangle over `Spec R` commutes. This is exactly the statement that `π` descends to a
  morphism in `Over (Spec R)`, the category the challenge's `Jacobian` lives in.

Route-independent, mathlib-PR-shaped; consumed by the symmetric-power base structure
(`Submission/Jacobian/AffineSymmetricPowerStructure.lean`).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.JacobianChallenge.AffineQuotient

universe u v

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (G : Type v) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The structure morphism `Spec(B^G) ⟶ Spec R`, dual to the `R`-algebra structure map
`R → B^G` of the invariant subalgebra. This makes the affine quotient a scheme over `Spec R`. -/
noncomputable def structureMorphism :
    affineQuotient R B G ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G)))

/-- The structure morphism of `Spec B` over `Spec R`, dual to `algebraMap R B`. -/
noncomputable def baseStructureMorphism :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

/-- **The quotient triangle over `Spec R` commutes:** `π ≫ (Spec(B^G) → Spec R) = (Spec B → Spec R)`.
Equivalently, the quotient map `π : Spec B → Spec(B^G)` is a morphism *over* `Spec R` — so it
descends to `Over (Spec R)`, where the challenge's `Jacobian` lives. Dualizes to the ring-tower
identity `(algebraMap (B^G) B) ∘ (algebraMap R (B^G)) = algebraMap R B`. -/
theorem quotientMap_comp_structureMorphism :
    quotientMap R B G ≫ structureMorphism R B G = baseStructureMorphism R B := by
  have hring : CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G)) ≫ inclHom R B G
      = CommRingCat.ofHom (algebraMap R B) := by
    rw [inclHom]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    -- `(algebraMap (B^G) B) (algebraMap R (B^G) x) = algebraMap R B x` by the scalar tower.
    exact (IsScalarTower.algebraMap_apply R (FixedPoints.subalgebra R B G) B x).symm
  rw [quotientMap, structureMorphism, baseStructureMorphism]
  calc Spec.map (inclHom R B G) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G)))
      = Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G)) ≫ inclHom R B G) :=
        (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by rw [hring]

end AlgebraicGeometry.JacobianChallenge.AffineQuotient
